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
- Dynamic effect row evidence records the row visible at effectful boundaries
  without collapsing duplicate handler layers: the nearest active matching
  handler arm is the selected layer, and unmatched dynamic performs remain
  open effects. For value-level thunk arguments, a thunk-row evidence view uses
  the specialization seeds to classify callsites as closed finite,
  closed-no-resume, or blocked. On the 20x20 nondeterministic list benchmark,
  this proves the three `list(thunk)` callsites as closed finite rows with
  `branch` carrying the two-resume schedule and `reject` carrying no resume
  action.
- Effect boundary ownership evidence is now explicit in the CPS IR. An
  `EffectfulForce` boundary can carry its owner function, return-frame resume,
  forced thunk value, closed/open row status, and the concrete finite handler
  layers it owns. Direct thunk-producing callsites can carry the same ownership
  evidence even when the generic callee boundary remains open. This follows the
  Koka duplicate-effect reading: the optimizer records the selected handler
  layer and the still-open effects instead of treating an effect name as a
  globally unique capability.
- The first ownership-consuming pass creates an interprocedural owned-perform
  clone for a forced thunk's dynamic callee. On the 20x20 nondeterministic list
  case, the root thunk's two `each` calls are rewritten to a clone whose
  `branch` perform carries the `list` handler owner and arm entry explicitly.
  Cranelift lowers that owned perform through an exact owned-handler selector
  and a direct handler-candidate call, bypassing the generic candidate dispatch
  for that finite layer. This is the first destructive use of the ownership IR;
  it intentionally leaves no-resume `reject` and the generic unspecialized
  `each` body in place.
- Local finite handler-region defunctionalization now consumes same-function
  finite `Perform` / handler-arm / terminal-`Resume` shapes. When the
  resumption pointer is only used by terminal resume statements, the `Perform`
  becomes a direct `Continue` to the arm entry and each terminal `Resume`
  becomes a direct `Continue` to the original resume continuation. This pass is
  deliberately structural: it does not inspect std paths, and it removes
  uninstalled static handler arms only after the matching local performs have
  disappeared.
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
  recorded finite schedule coordinates plus the closed thunk-row evidence and
  replace the dynamic handler lookup path for a finite arm with explicit
  control edges. Controlled
  inlining/contification still has to preserve handler installs, forced thunk
  bodies, dynamic `Perform` sites, and handler arm resumptions as one
  rewriteable region before generic handler lookup can be removed.
- The 20x20 hot path is not a same-function handler region: the `Perform`
  sites live in `std::undet::undet::each__mono1`, while the finite handler
  arms and the `EffectfulForce` boundary live in `std::undet::undet::list__mono3`.
  The IR now records the handler-owner / return-frame evidence needed to talk
  about that region without std path matching, and the first narrow
  interprocedural specialization consumes it for the owned `branch` perform.
  The next destructive pass should extend that consumption to no-resume effects
  and eventually remove the runtime resumption object for finite arm schedules.
- Lower `EffectfulForce` ownership into a codegen/runtime primitive that
  preserves the full blocked-force / return-frame contribution before
  transforming the 20x20 effectful thunk body. A normal direct edge or ordinary
  effectful call is not enough for resumptions that cross the force boundary.
- The force-frame evidence must be the full force protocol, not just the
  active-blocked boundary list. A known-thunk call experiment that pushed the
  post-force frame and extended active-blocked still failed because
  `force_native_i64_thunk_step` also owns handler/guard snapshot override,
  saved return-frame restoration, eval-context restoration, nested force
  stepping, and abort/scope-return interaction. The reusable primitive should
  expose that whole protocol before handler defunctionalization consumes it.
- A follow-up known-thunk runtime primitive experiment showed one more
  constraint: using the full force-step protocol is still not enough if the
  destructive pass first clones an effectful callee that owns handler installs
  and return-frame ownership. Even when the known-thunk helper reuses
  `force_native_i64_thunk_step`, cloning that callee changes enough control
  ownership that the branch resume boolean can still reach list code. The next
  destructive pass must consume the finite schedule in place, or explicitly
  reify handler-owner / return-frame ownership in the IR, instead of treating
  `DefunctionalizeFiniteHandler` as a callee body clone with a smarter force
  terminator.
- Do not lower an interprocedural owned handler-arm clone by rewriting local
  thunk `Resume` uses directly to the callee's raw `perform_resume`
  continuation. In 20x20, those resumes cross the `list` `EffectfulForce`
  return frame; jumping only to `each__mono1`'s resume continuation bypasses
  the caller-side force continuation and scalar branch values can flow into
  list merge. A correct destructive pass needs an explicit first-order
  representation of the composed resumption: callee perform resume plus the
  owned force return frame plus the caller-side post-force context.
- The owned perform evidence now carries the finite action local thunk entries
  and the owner force return-frame resume. For 20x20, this is the structural
  version of "pass the `.list` continuation into the `return` inside `each`'s
  fold": branch resume actions originate in the list arm thunks, continue into
  `each`'s branch resume, and the fold/sub return perform is visible as the
  local non-fallback perform that must deliver its payload to the owned
  return-frame resume. The destructive rewrite still needs a new IR edge for
  that composed continuation rather than a raw jump to either side alone.
- Cranelift now has a distinct owned-resumption construction path. Owned
  performs lower through `yulang_cps_make_owned_resumption_i64_*`, which carries
  owner function, owner return-frame resume, callee perform resume, and handler
  arm id into runtime. This intentionally keeps the existing
  `NativeCpsI64Resumption` representation for correctness; the important
  boundary is that the owned composition now has a named allocation point where
  the later destructive pass can replace generic resumption materialization
  with a first-order composed continuation.
- Runtime handler selection now saves the outer handler stack as a persistent
  snapshot rather than a fresh vector. This is not the final handler
  defunctionalization, but it removes one duplicate stack copy from the perform
  protocol while preserving the same restore semantics.
- Extend environment trimming to handler env payloads once handler-env target
  rebasing is explicit.
- Extend known thunk force recognition beyond pure value bodies once the IR
  carries enough effect/control evidence to preserve nested force semantics.
- Split direct-style island analysis into a reusable region object for Cranelift
  lowering decisions, not only profile counting.
- Add benchmark snapshots to each pass iteration: optimized continuation count,
  statement count, runtime control counters, and generated-executable wall time.
