# Native Scoped Abort Plan

This note records the next step for CPS repr Cranelift loop-control parity.

## Problem

The current JIT has a simple thread-local abort slot:

```text
Abort = Option<Value>
```

That is enough for top-level-ish `sub` / `return` escapes where the native call
stack should stop all the way back to the root or a real handler boundary.
It fixed finite-list `for` returning through an outer `sub`.

It is not enough for open-range `for` with local `last`.

```yulang
{
    for x in 0..:
        if x == 5: last
        else: ()
    5
}
```

VM result:

```text
[0] 5
```

Native CPS repr currently times out. If the same global abort is used too
aggressively, it stops the infinite fold but returns the local handler-arm
value `0`, skipping the expression after the loop.

So the missing operation is not "abort to root"; it is "abort until the
handler's dynamic fold/loop boundary, then continue as the local expression
result".

## Required Runtime Shape

Replace the scalar abort slot with a scoped abort:

```text
Abort = None
      | Global(value)
      | Scoped {
          value,
          return_frame_threshold,
          install_eval_id,
          prompt,
        }
```

`Global(value)` keeps the current behavior.

`Scoped` means:

1. While the native call stack is still inside frames created after
   `return_frame_threshold`, return `value` immediately.
2. When the boundary is reached, clear the abort and let the current call site
   observe `value` as the result of the call.
3. Normal continuation lowering then runs after that call site.

That is the distinction open-range `last` needs:

```text
fold_from recursion
  -> local last handler catches break
  -> scoped abort unwinds fold recursion
  -> last::sub boundary consumes the abort as ()
  -> caller sequence continues to 5
```

## Codegen Implication

The current helper:

```rust
return_if_abort_active(builder)
```

can only return from the current Cranelift function. It cannot say "consume the
abort here and bind this call's destination to the abort value".

The replacement should return a value:

```rust
let result = call_internal(...);
let result = abort_result_or_return(result, dest_lane);
define dest = result;
```

At statement sites that do not bind a destination, keep a return-only helper.

## Where Scoped Abort Is Created

`yulang_cps_perform_finish_escaped_i64` already sees
`NativeCpsI64SelectedHandlerMeta`.

Use:

```text
return_frame_threshold == 0
  -> Global(value)

return_frame_threshold > 0
  -> Scoped(value, return_frame_threshold, install_eval_id, prompt)
```

The threshold-zero case is the finite `for` / outer `sub` return regression
that is already fixed.

The threshold-positive case should cover open-range local loop control without
collapsing nondeterministic resumption enumeration. Nondet handlers still need
retained return-frame chains, so tests for `.list`, `.logic`, and `.once` must
remain in the verification set.

## Verification

Minimum checks:

```text
notes/bugs/native_open_range_for_last_returns_payload.yu
examples/03_for_last.yu
notes/bugs/native_for_loop_escape_keeps_running.yu
examples/04_sub_return.yu
runs_undet_list_nested_each_sum_through_cps_repr
runs_undet_logic_nested_each_sum_through_cps_repr
runs_undet_once_nested_each_sum_through_cps_repr
cargo test -q -p yulang-native
cargo test -q -p yulang-compile -- --test-threads=1
```

The important invariant is that abort is no longer a single unstructured
"stop everything" signal. It is either global, or it has a precise dynamic
return-frame boundary where normal continuation resumes.
