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
| Local state | ref get/set/update where the cell does not escape | local cell evidence |
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

### Stage 1: local escape evidence

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

### Stage 2: local state evidence

Target ref get/set/update only when the cell and handler do not escape in a way
that requires dynamic handler behavior.

Reason:

- common in loops;
- current ref workloads still pay effect request tax;
- local cell operations can be direct.

Risk:

- `ref.update` is a hygiene canary.
- field-function private evidence must not leak.
- update callback effects must remain correctly routed.

This stage needs explicit canaries from `std.control.var.ref.update`.

### Stage 3: resumptive evidence for nondet/parser

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

### Stage 4: inlining and backend use

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

## First concrete task

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
