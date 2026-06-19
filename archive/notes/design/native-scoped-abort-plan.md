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

## 2026-05-15 Trace Note

`notes/bugs/native_open_range_for_last_returns_payload.yu` reaches the local
`last` handler. The relevant filtered trace shape is:

```text
install_handler_full: handler=7 prompt=24 install_eval=208 threshold=7 ...
perform_select: handler=7 prompt=24 install_eval=208 ... threshold=7
scope_return_set (perform_finish): prompt=24 ... value=0 current_eval=208 initial=7
route_scope_return: prompt=24 current_eval=208 initial=7 action=current_handler value=0
```

After that, execution installs the next `handler=5` / `handler=7` pair for the
next range step:

```text
install_handler_full: handler=5 prompt=26 install_eval=238 threshold=8 ...
install_handler_full: handler=7 prompt=28 install_eval=243 threshold=8 ...
...
```

So the missing piece is not handler selection. The selected handler returns the
local arm value, but no scoped short-circuit survives long enough to stop the
recursive range/fold chain and resume at the loop expression boundary.

This also shows why a plain global abort is too blunt: the value `0` is the
handler-arm result used to stop the loop body, not the enclosing block result
`5`.

The interpreter / CPS repr evaluator has one more important distinction:
`handle_scope_return_repr` does not call the matched current handler escape as
a nested Rust function and then return normally. For a real local jump it
mutates the eval loop state instead:

```text
current = target
args = [value]
continue eval loop
```

The native JIT helper currently calls the escape continuation through a raw
function pointer and returns that result to the caller. That works for several
non-local return cases, but for open-range `last` it lets the surrounding
range/fold call chain continue after the local escape value. The eventual fix
needs either a proper native analogue of the eval-loop jump, or a scoped
short-circuit that survives that helper call until the correct continuation
boundary consumes it.

An experiment widened the current-handler route to set the legacy abort slot
for any inner eval frame:

```text
if current_initial > 0 {
    Abort = value
}
```

That changed the forced CPS repr executable from timeout to:

```text
0
```

The filtered trace then showed the other half of the bug:

```text
route_scope_return: prompt=24 current_eval=208 initial=7 action=current_handler value=0
return_i64: value=0 frame_len=7 initial=7 action=noop
abort_active: value=0
```

So a plain abort slot can stop the range recursion, but it preserves the local
handler-arm value as the whole program result. The correct operation has to
consume the short-circuit at the loop/handler boundary and then run the
continuation after the loop, producing `5`.

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
