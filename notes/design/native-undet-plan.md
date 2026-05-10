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

Open:

- `std::undet.each` still uses `fold` / `sub::return`; even with the
  handler-stack threading the recursive `each` body needs to coexist with
  closure callbacks that also forward dynamic context.
- `std::undet.once` still needs a real resumption queue strategy.
- generated CPS executables still do not print non-scalar Yulang values.

The next implementation step is Milestone 7: re-introduce
`std::undet::each` together with a local DFS-once helper, which exercises
`fold`, `sub::return`, and closure callbacks against the new dynamic
handler routing.
