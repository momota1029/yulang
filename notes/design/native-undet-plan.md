# Native Undet Plan

This note tracks the native backend path for nondeterministic computation.

`std::undet.once` is intentionally treated as an integration target, not the
first implementation target.  The current standard implementation combines all
of these hard cases at once:

- effect operations for `branch` and `reject`;
- multi-shot resumptions;
- saved resumption queues;
- `list<resumption>` or an equivalent opaque control queue;
- recursive handler loops;
- `opt` non-scalar return values;
- `fold` / `sub::return` machinery inside `each`;
- handler stack and guard stack snapshots;
- thunk callbacks crossing handler boundaries.

The native CPS representation backend should grow through smaller scalar
targets first.

## Phases

1. Minimal `branch` handler:
   - local `choice::branch`;
   - handler resumes with `k true`;
   - root returns a scalar.
2. DFS `once` with `reject`, no queue:
   - local `choice::branch` and `choice::reject`;
   - `k true` is tried under a nested reject handler;
   - reject resumes `k false`;
   - root returns a scalar.
3. Finite list choice without `fold` / `sub`:
   - use `std::list::uncons`;
   - branch between the head and rejection;
   - keep the root scalar.
4. Function-shaped finite `each`:
   - source-defined `each_head` / `each_list` returning `[choice] int`;
   - caller handler frames must be visible to thunks returned across a direct
     function boundary.
5. Standard `std::undet.each`:
   - reintroduce the std implementation after the finite helper works.
6. Queue-backed `once`:
   - represent `list<resumption>` with either a CPS opaque queue helper or
     lane-aware list helpers.
7. `list` / `logic` collectors:
   - delay until non-scalar CPS returns and generated executable printing are
     no longer blockers.

## Current Status

Completed:

- minimal branch handler through the Cranelift CPS repr scalar path;
- DFS `once` with `reject` and scalar root;
- finite list choice using `std::list::uncons`, without `fold` / `sub`, and
  scalar root;
- handler arm environment capture for `ResumeWithHandler`;
- handler-aware lowering for `match` in handled bodies;
- `LocalPushId -> AddId -> Thunk` execution in handled bodies;
- Phase 4 (inlinable case): a non-recursive helper such as
  `each_head(xs): [choice] int` is inlined inside the caller's handler scope,
  and the resulting thunk is forced before reaching the handler value
  continuation. CPS eval, CPS repr eval, and Cranelift JIT all agree with VM.
- Phase 4 (recursive case, Milestone 6): a recursive helper such as
  `each_list(xs): [choice] int` reaches its caller's handler frame through
  the runtime handler stack. CPS lowering emits `InstallHandler` /
  `UninstallHandler` around handler scopes; the CPS evaluators thread
  `active_handlers` through `DirectCall` / `ApplyClosure` / `ForceThunk`;
  Cranelift backs the new stmts with thread-local
  `yulang_cps_install_handler_i64` / `yulang_cps_uninstall_handler_i64`
  helpers that share the existing handler-stack runtime.
- Milestone 7: `std::undet.each` runs end-to-end with a local DFS once
  helper. CPS lowering forces the result of effectful direct-call
  statements (e.g. the `xs.fold(...)` between `sub::sub { ... }` and
  `reject()`). The CPS evaluators wrap a handler-arm body's non-local
  return as `Aborted(value)` and bubble it up through `DirectCall` /
  `ApplyClosure` / `ForceThunk` / `Resume` / `ResumeWithHandler`.
  Cranelift mirrors this with a thread-local abort slot and helpers
  (`yulang_cps_abort_i64`, `yulang_cps_abort_active_i64`,
  `yulang_cps_abort_value_i64`, `yulang_cps_clear_abort_i64`) plus a
  `return_if_abort_active` check after every internal call site, and a
  Perform terminator that wraps the handler-arm result if no nested
  abort is already active.

Open:

- `std::undet.once` still needs a real resumption queue strategy. The
  recommended next step is to widen the CPS runtime value domain so
  resumptions / closures / thunks can flow through `List` / `Tuple` /
  `Variant` / function arguments.
- generated CPS executables still do not print non-scalar Yulang values.

The next implementation step is Phase B in
`notes/todo/native-undet-write5.md`: unify the CPS evaluator and the
Cranelift backend's value domain so first-class resumptions / closures
flow through containers and pattern matches.
