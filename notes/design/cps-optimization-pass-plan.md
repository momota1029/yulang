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
- Local one-shot thunk force inline when the thunk body is a pure value
  computation and no boundary/control-changing statement separates creation
  from force.
- Consecutive deep `ForceThunk` chain collapse. Since CPS `ForceThunk` already
  forces through nested thunks, `ForceThunk(ForceThunk(x))` can be represented
  as one force when the intermediate value has no other use.
- Redundant force removal for structurally known non-thunk values when all
  uses of the force result stay in the same continuation tail.
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
- Read-only algebraic-effect region analysis over local `Perform` / handler arm
  / `Resume` structure.
- Read-only dynamic effect candidate analysis that connects active handler
  installs at effectful boundaries to dynamic-handler `Perform` sites across
  direct effectful calls or unknown thunk/apply bodies, using structural effect
  matching rather than std function names.
- Read-only dynamic effect thunk specialization seeds that connect direct-call
  local thunk arguments to finite dynamic handler regions and separate finite
  resume effects from no-resume effects.
- Read-only dynamic effect thunk rewrite plans. These classify ready finite
  seeds as `DefunctionalizeFiniteHandler`, `CalleeBodyClone`, or `Blocked`, and
  record ordinary body-clone blockers such as recursive callees, post-call
  force chains, callee handlers, and effectful boundaries.

## Next Candidates

- Consume `ReadyFinite` dynamic effect thunk specialization seeds in a real
  rewrite/codegen path. Controlled inlining/contification must bring handler
  installs, forced thunk bodies, dynamic `Perform` sites, and handler arm
  resumptions into one rewriteable region before generic handler lookup can be
  removed.
- Extend environment trimming to handler env payloads once handler-env target
  rebasing is explicit.
- Extend known thunk force recognition beyond pure value bodies once the IR
  carries enough effect/control evidence to preserve nested force semantics.
- Split direct-style island analysis into a reusable region object for Cranelift
  lowering decisions, not only profile counting.
- Add benchmark snapshots to each pass iteration: optimized continuation count,
  statement count, runtime control counters, and generated-executable wall time.
