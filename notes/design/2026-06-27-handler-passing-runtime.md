# Handler-passing runtime strategy

This note records a possible next runtime architecture for Yulang.
The goal is not to make a few pure islands fast.  In Yulang, ordinary-looking
control such as `for` can carry a break/last effect, and common library features
such as ref cells and parsers are effect based.  If only syntactically pure
subexpressions are optimized, most real programs still pay the generic handler
VM tax.

The more promising direction is a Koka-like handler/evidence-passing lowering:
instead of searching the dynamic handler stack whenever an operation is emitted,
compile an effectful computation so it receives handler evidence objects, and
operation calls invoke those objects directly.

References:

- Daan Leijen, Type Directed Compilation of Row-Typed Algebraic Effects
  <https://www.microsoft.com/en-us/research/publication/type-directed-compilation-row-typed-algebraic-effects/>
- Ningning Xie and Daan Leijen, Generalized Evidence Passing for Effect Handlers
  <https://www.microsoft.com/en-us/research/publication/generalized-evidence-passing-for-effect-handlers/>
- Pro review: `notes/design/2026-06-27-handler-passing-runtime-pro-review.md`

## Decision after Pro review

Adopt the handler/evidence-passing direction as the next runtime design track,
but do not treat evidence as a plain handler pointer.

Yulang needs runtime evidence for both sides of the type-system story:

- positive evidence: which handler can receive an operation;
- negative / hygiene evidence: which callback-origin operation must remain
  invisible to an inner handler;
- private projection evidence: private tails and public tails must not become the
  same runtime object.

This means the first useful artifact is not a faster VM.  It is an explicit
evidence IR that can show which evidence slots an operation, thunk, closure, and
function adapter require.

The current control VM remains the behavior oracle and generic fallback.  Native
backend work should not try to native-code the current request / marker / resume
model before the evidence-passing model exists; doing so would freeze the wrong
cost structure.

## Core idea

Current control VM shape:

```text
effect op
  -> build Request
  -> paint Request with active marker/add-id stack
  -> search / match handler
  -> store captured continuation
  -> resume through marker scopes
```

Handler-passing shape:

```text
effectful function receives handler evidence
  -> effect op calls evidence object
  -> evidence object either handles locally
     or forwards/yields to an outer evidence object
  -> resumption is an explicit object passed to the handler
```

The handler is a continuation-like object:

```text
HandlerEvidence<op, a, r>
  operation(payload, resume) -> r
```

For ordinary handling, the operation passes a payload and a resumption to the
current evidence.  The evidence invokes the handler code.  The handler can call
`resume(value)` zero, one, or many times depending on the effect.

The direction can appear reversed compared to the current VM: instead of the
operation producing a request and waiting for a handler to catch it, the
operation calls the handler evidence directly and receives the final value.
This reversal is the useful part.  A deep search such as nondeterminism no
longer needs to repeatedly reconstruct the same handler lookup path if the
evidence object already points at the handler implementation.

## Why pure islands are not enough

For Yulang, "pure-heavy" is a misleading optimization target.

- `for` can be control-effectful because `last` / `break` is effect-like.
- `ref` and `ref.update` are intentionally effectful.
- parser combinators are effectful by design.
- nondeterminism requires multi-shot continuation behavior.
- callback hygiene means a function-looking value can carry hidden handler
  evidence constraints.

Therefore the long-term compilation strategy should optimize effect classes,
not just effect-free regions.

## Effect classes

The handler-passing strategy should not start by treating every effect the same.
Each class has a different low-level representation.

| Class | Examples | Preferred lowering |
| --- | --- | --- |
| Pure / total | literal, closed record/list construction, pure primitive | direct value code |
| Local escape | `last`, `break`, `sub::return`-like shallow escape | lightweight prompt / direct jump evidence |
| Local state | ref get/set where the cell does not escape | local cell evidence |
| Multi-shot search | nondet `each`, parser branching | resumptive handler evidence with reusable continuation |
| Host / unknown | console, file, external operation | generic request fallback |
| Boundary-sensitive callback | higher-order callback under handler | evidence wrapper with hygiene guards |

The fallback remains the current generic control VM.  The new lowering should
specialize only the classes it can explain.

## Relationship to Yulang hidden evidence

The type solver already tracks handler visibility with directed stack evidence.
Runtime handler-passing must preserve the same distinction:

- Public types hide stack evidence.
- Internal lowering may pass handler evidence objects.
- Callback-derived effects must not be captured by an unrelated inner handler.
- Explicit effect annotation acts as a local contract that permits subtraction.

In the current VM, this is represented with marker frames, add-id markers,
guard ids, and carried guards.

In a handler-passing runtime, these become evidence routing wrappers:

```text
raw handler evidence
  -> guard own path
  -> guard foreign path
  -> preserve own on resume
  -> forward/yield to outer evidence when hidden by a callback boundary
```

The important invariant is:

```text
typed hidden stack evidence
  and runtime handler evidence routing
  must encode the same handler visibility relation
```

This is not just an optimization.  If the runtime evidence captures a callback
effect that the type evidence says must remain foreign, the language becomes
unsound with respect to handler hygiene.

## Handler evidence object shape

A first sketch:

```rust
enum Evidence {
    DirectEscape(DirectEscapeEvidence),
    LocalState(LocalStateEvidence),
    Resumptive(ResumptiveEvidence),
    Forward(ForwardEvidence),
    GenericVm(GenericVmEvidence),
}

struct ResumptiveEvidence {
    handler_id: GuardId,
    family: InternedPathPrefix,
    mode: ResumptionMode,
    outer: Option<EvidenceId>,
}

enum ResumptionMode {
    OneShot,
    MultiShot,
}
```

This should not be implemented literally yet.  The important separation is:

- evidence object identity;
- operation family;
- handler body;
- outer evidence chain;
- resumption representation;
- hygiene routing policy.

The current `Request` can be seen as the fallback representation of:

```text
operation + payload + captured continuation + dynamic evidence stack
```

Handler-passing makes the evidence stack explicit earlier and avoids building a
full request when a specialized evidence object can handle the operation.

## Expected wins

The existing VM measurements show that the remaining cost is not one single
clone.  It is repeated generic machinery:

- request construction and marking;
- active add-id scans;
- marker frame push/pop;
- continuation capture/resume bookkeeping;
- repeated handler lookup and boundary reconstruction.

Handler-passing can reduce these when an operation is statically routed to a
known evidence object:

- no active add-id scan for that operation;
- no dynamic handler lookup;
- no request payload marker painting unless forwarding is needed;
- direct handler call can be inlined;
- local escape and local state can avoid multi-shot continuation machinery.

For true multi-shot effects, this still needs real continuation support.
Nondeterminism and parser branching do not become pure direct calls.  The win is
that the handler evidence can be reused and inlined around the continuation
capture/resume points instead of rediscovering the same handler stack.

## Where this fits in the pipeline

This belongs after effect inference and monomorphization, not during parsing or
generic inference.

```text
sources
  -> infer / hidden stack evidence
  -> specialize / monomorphize
  -> control lowering
  -> evidence-passing lowering
  -> generic control VM fallback
```

The first implementation can live beside `crates/control-vm` rather than
replacing it.

Candidate crate/module boundaries:

```text
crates/control-vm/src/evidence_lower.rs
crates/control-vm/src/evidence_ir.rs
crates/control-vm/src/evidence_runtime.rs
```

The generic VM remains the oracle for behavior.  Evidence-passing paths must
fall back to generic VM if the lowering cannot prove the required effect class.

## Staged plan

### Stage 0: classify only

Add metrics.  Do not change execution.

Metrics:

- number of effect operations by family;
- number of handlers by family;
- operations with statically known nearest handler;
- operations crossing callback hygiene boundary;
- local escape candidates;
- local state candidates;
- multi-shot candidates;
- generic fallback count.

This tells whether handler-passing is worth applying to current workloads.

### Stage 1: evidence IR dump

Do not change execution yet.

Add an explicit evidence-aware IR beside the existing control/runtime IR:

```text
EvidenceFunction
  value params
  evidence params
  body

EvidenceExpr
  Perform(family, op, payload, evidence_slot)
  Handle(family, body, handler_evidence, parent_evidence)
  Call(callee, arg, evidence_args)
  FallbackToVm(reason, expr)
```

Success condition:

```text
for each operation/thunk/closure/function adapter,
dump which evidence slot or adapter it would require
```

No direct execution is needed in this stage.  The important thing is to stop
recovering evidence by re-walking current `Expr::Catch` / `Expr::ForceThunk`
shapes.

### Stage 2: callback evidence adapter

Lower the current `FunctionAdapterHygiene` idea into evidence routing:

```text
FunctionAdapterEvidence
  body evidence transform
  argument evidence transform
  return evidence transform
```

This must model callback-origin effects as hidden from unrelated inner handlers.
The adapter is the runtime counterpart of protected rows such as `#id[Empty]`.

This stage is needed before direct local escape, because even local escape can be
wrong if a callback-origin `return` / `sub::return` is captured by the wrong
handler.

### Stage 3: local escape evidence

Target `last` / `break` / `sub::return`-like effects first.

Reason:

- usually shallow;
- no multi-shot resume;
- can be represented as direct jump/prompt evidence;
- gives speedup for ordinary control flow.

Constraints:

- must preserve explicit handler contracts;
- must not capture callback-origin effects unless the type evidence permits it;
- fallback to generic VM if the handler identity is not statically routed.

### Stage 4: first-order local state evidence

Target ref get/set only when the cell and handler do not escape in a way that
requires dynamic handler behavior.

Reason:

- common in loops;
- current ref workloads still pay effect request tax;
- local cell operations can be direct.

Risk:

- field-function private evidence must not leak;
- direct get/set evidence must still forward when hidden by callback boundaries.

Do not include `ref.update` in this stage.  It is not just a local-state
primitive; it combines local state, a data-position effectful function, callback
evidence routing, and private tail projection.

### Stage 5: fallback bridge

Make fallback explicit in the evidence IR.

When evidence lowering cannot explain a region, it should produce a visible
fallback node rather than hiding a branch deep inside the evidence runtime:

```text
FallbackToVm(reason, expr, evidence_to_marker_bridge)
```

This bridge has to convert current blockers / private projections into the
marker and guard representation expected by the existing VM.

### Stage 6: one-shot resumption

Introduce a resumption object for cases that can be represented without
multi-shot sharing:

```text
OneShotResumption
  moved continuation
  evidence environment at perform
```

This is the first stage that should interact with continuation representation.

### Stage 7: multi-shot evidence for nondet/parser

Target effects that genuinely resume continuation zero, one, or many times.

Reason:

- this is where Koka-style evidence passing matters most;
- deep search can reuse evidence instead of rebuilding request routing.

Risk:

- multi-shot semantics;
- continuation snapshot sharing;
- marker/hygiene boundary on resumed computation.

This stage should reuse the stored continuation snapshot/cursor work already in
the VM.

### Stage 8: `ref.update`

Only after callback evidence adapters, first-order local state, fallback
bridging, and resumption are explicit, consider direct-lowering `ref.update`.

Until then, `ref.update` remains a generic VM fallback canary.

### Stage 9: inlining and backend use

Once evidence objects are explicit, small handlers can be inlined.

This is where a future native/direct backend can benefit:

- local escape evidence becomes ordinary branch/jump;
- local state evidence becomes cell load/store;
- pure parts become direct expression code;
- resumptive evidence stays in the control runtime.

## Non-goals for the first slice

- Do not replace the generic VM.
- Do not optimize nondeterminism first.
- Do not invent a new type rule in runtime lowering.
- Do not treat all handlers as one-shot.
- Do not erase hidden stack evidence from callback boundaries.
- Do not special-case std names or paths in inference.

## Open questions

1. How should typed hidden stack evidence be serialized into the control IR so
   runtime evidence routing can consume it without re-inference?
2. Can local escape handlers be identified structurally, or do they need an
   explicit operation property in std/control metadata?
3. What is the minimal evidence object needed to express `compose` hygiene?
4. Does `ref.update` become local state evidence, or must it remain generic
   until callback evidence routing is fully explicit?
5. How much of Koka's yield bubbling corresponds to Yulang's current
   marker/request forwarding?

## Historical first concrete task

Add Stage 0 metrics to control lowering/runtime:

- count effect operation families;
- count handler/catch families;
- record whether an operation has a statically visible handler candidate;
- count fallback reasons:
  - unknown family;
  - crosses callback hygiene boundary;
  - multi-shot resume required;
  - host effect;
  - missing lowering metadata.

The result should be a numbers-only commit.  It should not change execution.

## Stage 0 coarse profile

Implemented as `crates/control-vm/src/effect_profile.rs`.

The current pass is deliberately coarse.  It scans the lowered control IR arena
and records:

- effect operations and exact operation families;
- effect operations whose exact family appears in some catch handler arm;
- marker frames and marker frame families;
- catch expressions;
- operation handler arms;
- value arms;
- continuation arms;
- function adapters;
- ref set nodes.

It does not claim that an operation has a statically nearest handler.  The
`effect_ops_with_handler_arm` counter only means that the same exact operation
path occurs somewhere in a catch arm in the same lowered program.

This is enough for the first question:

```text
Does a workload pay generic VM tax around a small number of repeated effect
families, or around many unrelated effect families?
```

If this profile is useful, the next stage can add a proper tree traversal with
a scoped handler stack and callback-boundary markers.

## Stage 0.5 scoped candidate profile

Implemented as a refinement of `crates/control-vm/src/effect_profile.rs`.

This still does not change execution.  It traverses the lowered control IR from
top-level instance entries and expression roots with a small static context:

- a stack of operation handler arms introduced by `catch`;
- a callback-boundary depth introduced by `FunctionAdapter` nodes whose hygiene
  plan contains runtime guard markers;
- a delayed-computation depth introduced by `lambda` and `make-thunk` bodies.

Traversal rule for `catch`:

- the catch body is traversed with the operation arms pushed as handler
  candidates;
- handler arm guards and bodies are traversed in the original context, not under
  the same handler.

That rule matters because the arm body is the handler implementation, not the
handled computation.  If an arm body performs another operation, it should see
outer handlers unless it contains its own nested `catch`.

For each statically visited effect operation, the profile records:

- whether an exact nearest handler candidate is visible;
- whether the candidate is direct;
- whether the candidate is blocked by a callback hygiene boundary;
- whether the candidate is blocked by a delayed computation boundary;
- whether the matching arm is resumptive.

The pass also records call/force sites:

- direct-known effect call sites, such as applying an instance whose entry is an
  `EffectOp`;
- direct-known function call sites, such as applying an instance whose entry is
  a `Lambda`;
- dynamic call sites whose callee is not statically known;
- known `make-thunk` force sites;
- dynamic force sites, including force of a parameter value like `catch action`.

The "direct handler candidate" counter is intentionally conservative.  An effect
operation under a `lambda`, `make-thunk`, or guarded function-adapter boundary is
not counted as directly lowerable to handler passing just because a lexical
`catch` appears outside it.  Turning those cases into evidence-passing code needs
typed hidden stack evidence in the IR, not only lexical shape.

Initial measurements showed that this distinction matters.  In the existing
nondet/showcase workloads, exact effect families often have matching handler arm
families, but scoped direct candidates remain zero.  The visible handler boundary
mostly surrounds a dynamic thunk force (`catch action`), not a direct-known
`EffectOp` call site.  That means the next stage cannot be a purely syntactic
rewrite of `catch { EffectOp(...) }`; it needs lowering metadata that connects
typed effect evidence to the value/thunk being forced.

## Decision: stop extending the current VM profile

Do not keep adding more profile logic to the existing control VM as the next
step.

The Stage 0 / Stage 0.5 counters are useful as a diagnosis of the current VM:

- the current VM pays repeated request/catch/marker costs;
- effect families are relatively small in number;
- common handler shapes go through dynamic thunk force rather than a direct
  lexical `EffectOp` under `catch`.

However, those counters are not a good foundation for designing the
handler-passing semantics itself.  A handler-passing runtime changes where the
handler evidence lives and how thunks/functions receive it.  Once that happens,
"dynamic force site under the current VM" is no longer the main semantic unit.

Therefore the Stage 0.5 profile is a stopping point:

- keep it as a comparison baseline for the existing VM;
- do not add typed-force profile counters inside `control-vm`;
- do not mutate the current request/catch VM gradually into handler passing;
- design the handler-passing runtime as a separate strategy first.

The current control VM remains the behavior oracle and fallback runtime.
The handler-passing path should be introduced only after its IR and evidence
semantics are explicit enough to compare against that oracle.

## Separate runtime strategy

The next work item is not another profile pass.  It is a small semantic design
for an evidence-passing runtime.

Target shape:

```text
typed mono/control value
  -> evidence-aware IR
  -> handler-passing runtime prototype
  -> generic control VM fallback for unsupported regions
```

This should be separate from the current VM in three ways.

1. Separate IR

   The new IR should make evidence parameters explicit.  It should not infer
   evidence routing by re-walking current `Expr::Catch` / `Expr::ForceThunk`
   shapes.

2. Separate execution model

   The new runtime should call handler evidence objects directly.  The current
   `Request` object is a fallback representation, not the primary operation
   representation.

3. Separate proof obligation

   Correctness should be stated as a relation to the current VM behavior:
   if evidence lowering succeeds, running the evidence runtime should produce
   the same observable result as the current control VM.

The first prototype can still live in `crates/control-vm` as modules, but it
should be architecturally separate:

```text
crates/control-vm/src/evidence_ir.rs
crates/control-vm/src/evidence_lower.rs
crates/control-vm/src/evidence_runtime.rs
```

Those modules should not depend on the current active marker stack as their
central abstraction.  They may call back into the generic VM when lowering cannot
explain an effect class.

## Evidence runtime design tasks

Before implementation, decide these in writing:

1. Evidence parameter form

   How does an effectful function or thunk say which handler evidence it needs?
   This must come from typed hidden stack evidence, not from source path names.

2. Thunk and closure representation

   A thunk that may perform `flip` / `sub` / parser effects should carry an
   evidence environment or evidence parameter list.  This is the core difference
   from the current VM, where a thunk is forced and then emits a dynamic request.

3. Handler evidence object

   Define the object that receives an operation payload and resumption.  It must
   distinguish abortive, one-shot resumptive, and multi-shot resumptive cases.

4. Forwarding/yielding

   If a handler cannot consume an operation, define how the operation is
   forwarded to outer evidence.  This is where Yulang's hidden stack evidence
   and Koka-style yield bubbling need to be matched carefully.

5. Callback hygiene

   A callback-derived effect must not be accidentally captured by a handler that
   did not receive the right evidence contract.  This should be represented as
   evidence routing, not as a late runtime marker patch.

6. Generic VM fallback

   Unsupported regions should lower to an explicit fallback node that invokes the
   current control VM.  Falling back should be a visible lowering result, not a
   hidden branch deep inside the evidence runtime.

7. Validation fixtures

   At minimum, compare against the current VM on:

   - `all_paths`;
   - `sub` callback hygiene;
   - `compose` / higher-order effect boundary;
   - `ref.update`;
   - parser/nondet branching.

## Current next task

Build the evidence IR dump from typed mono/control data.

Scope:

- define `EvidenceFunction`, `EvidenceExpr`, `EvidenceSlot`, and
  `EvidenceAdapter` as data structures only;
- lower enough metadata to print operation sites, thunk/closure evidence
  requirements, and function adapter evidence transforms;
- do not change execution;
- do not route operations directly yet;
- do not special-case std paths or function names;
- keep the current control VM as the only executor.

Success criteria:

- `compose`, `sub` callback hygiene, `all_paths`, parser choice, and
  `ref.update` can produce an evidence dump;
- the dump distinguishes positive handler evidence from blocker / private
  projection evidence;
- every unsupported region is represented as an explicit fallback reason rather
  than an implicit runtime branch.
