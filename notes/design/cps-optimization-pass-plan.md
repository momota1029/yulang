# CPS Optimization Pass Plan

This note turns the CPS/SSA and one-shot-continuation reading direction into
implementation checkpoints for Yulang. It intentionally records rules rather
than copied paper text.

## Safety Model

- Administrative CPS rewrites are allowed when the target continuation protocol
  is explicit in the IR and arity/lane checks still hold.
- One-shot continuations may be inlined when the use count proves a single
  local `Continue` call and the continuation is not a handler, thunk, closure,
  resumption, or function entry.
- Multi-shot continuations are not destructively moved. Any rewrite that would
  change clone/resume sharing stays disabled unless the IR carries proof that
  no clone can observe the difference.
- Handler frames, guard state, blocked thunk state, and prompt/escape metadata
  are removed only when structured effect/control evidence proves they cannot
  be observed.
- Optimizations are driven by IR shape, lanes, effect/control evidence, and use
  counts. They must not depend on std module paths or function names.

## Current Conservative Passes

- Forwarding continuation rewrite.
- Empty return-continuation fold.
- Literal bool branch fold.
- Pure `EffectfulCall` rewrite to direct call plus local continuation jump.
- Primitive wrapper reification.
- Local partial closure apply reification.
- Known closure parameter apply reification.
- Unused continuation parameter trimming.
- Unused continuation environment slot trimming.
- Structural projection fold.
- Small pure direct-call inline.
- Single-use one-shot continuation inline.
- Unreachable continuation pruning.
- Dead pure statement elimination.
- Direct-style / SSA island counting.

## Next Candidates

- Extend environment trimming to handler env payloads once handler-env target
  rebasing is explicit.
- Recognize known thunk force shapes that are local, one-shot, and not separated
  by handler/guard boundary effects.
- Split direct-style island analysis into a reusable region object for Cranelift
  lowering decisions, not only profile counting.
- Add benchmark snapshots to each pass iteration: optimized continuation count,
  statement count, runtime control counters, and generated-executable wall time.
