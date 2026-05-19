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
  uses of the force result stay in the same continuation tail. Primitive
  results participate only when the primitive constructs or returns a scalar /
  container value itself; element projection such as `ListIndex` is excluded
  because it may surface a stored thunk handle.
- Interprocedural direct-call force removal. A callee can be treated as a
  known non-thunk producer only when every direct return continuation returns a
  known non-thunk value. Thunk and closure entry continuations are excluded
  from this proof because they run under their own call protocol.
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
- Finite dynamic effect thunk rewrite plans now carry the concrete handler
  rewrite coordinates: callee effect boundary, handler arm entry, dynamic
  `Perform`, resume continuation, and literal resume arguments when they are
  locally materialized in the arm. This is still read-only evidence; it makes
  the next destructive pass target a specific handler schedule instead of a
  std path or operation-name special case.
- The first experimental destructive slice is deliberately narrower than the
  20x20 hot path: when a ready finite plan forces a known local thunk whose
  body has no effectful terminators, the callee and thunk region can be cloned
  into the caller and the cloned `EffectfulForce` boundary can become a direct
  continuation edge. Effectful thunk bodies are excluded because
  `EffectfulForce` contributes blocked-force / return-frame state to the
  resumption; replacing it with an ordinary direct edge or ordinary
  `EffectfulCall` leaks the handler resume argument into downstream list code.

## Next Candidates

- Consume `ReadyFinite` dynamic effect thunk specialization seeds in a real
  rewrite/codegen path. The first destructive slice should consume the
  recorded finite schedule coordinates and replace the dynamic handler lookup
  path for a finite arm with explicit control edges. Controlled
  inlining/contification still has to preserve handler installs, forced thunk
  bodies, dynamic `Perform` sites, and handler arm resumptions as one
  rewriteable region before generic handler lookup can be removed.
- Reify `EffectfulForce`'s blocked-force / return-frame contribution as
  explicit IR evidence before transforming the 20x20 effectful thunk body.
  A normal direct edge or ordinary effectful call is not enough for resumptions
  that cross the force boundary.
- The force-frame evidence must be the full force protocol, not just the
  active-blocked boundary list. A known-thunk call experiment that pushed the
  post-force frame and extended active-blocked still failed because
  `force_native_i64_thunk_step` also owns handler/guard snapshot override,
  saved return-frame restoration, eval-context restoration, nested force
  stepping, and abort/scope-return interaction. The reusable primitive should
  expose that whole protocol before handler defunctionalization consumes it.
- Extend environment trimming to handler env payloads once handler-env target
  rebasing is explicit.
- Extend known thunk force recognition beyond pure value bodies once the IR
  carries enough effect/control evidence to preserve nested force semantics.
- Split direct-style island analysis into a reusable region object for Cranelift
  lowering decisions, not only profile counting.
- Add benchmark snapshots to each pass iteration: optimized continuation count,
  statement count, runtime control counters, and generated-executable wall time.
