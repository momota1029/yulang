# Evidence-passing paper notes for Yulang

This note extracts the parts of the Koka / evidence-passing literature that
matter for a future Yulang evidence VM.

It is not a general literature summary.  The goal is to keep the next runtime
implementation from accidentally rebuilding the current request / marker /
continuation VM in a different shape.

Local reading copies:

- `~/papers/yulang-runtime/generalized-evidence-passing-effect-handlers-2021.pdf`
- `~/papers/yulang-runtime/type-directed-compilation-row-typed-algebraic-effects-2017.pdf`
- `~/papers/yulang-runtime/koka-row-polymorphic-effect-types-2014.pdf`

Primary sources:

- Ningning Xie and Daan Leijen, "Generalized Evidence Passing for Effect
  Handlers: Efficient Compilation of Effect Handlers to C", ICFP 2021.
  <https://xnning.github.io/papers/multip.pdf>
- Daan Leijen, "Type Directed Compilation of Row-Typed Algebraic Effects",
  POPL 2017.
  <https://www.microsoft.com/en-us/research/wp-content/uploads/2016/12/algeff.pdf>
- Daan Leijen, "Koka: Programming with Row Polymorphic Effect Types", MSFP 2014.
  <https://arxiv.org/abs/1406.2061>

## Reading order

1. Read the ICFP 2021 evidence-passing paper first.
   This is the direct runtime source for evidence vectors, yield bubbling,
   short-cut resumptions, and monadic translation.
2. Read the POPL 2017 compilation paper second.
   This gives the earlier Koka handler semantics, tail-resumption motivation,
   and type-directed compilation framing.
3. Read the 2014 Koka row-polymorphism paper last.
   This is mainly for row type behavior, duplicated labels, principal
   inference, and effect elimination surface types.

## What transfers directly

### Evidence vectors

The 2021 paper replaces dynamic handler search with an explicit evidence vector.
An operation looks up its handler evidence locally instead of walking the
evaluation context.

For Yulang, this corresponds to replacing:

```text
operation
  -> build Request
  -> paint with active marker/add-id stack
  -> scan handler stack
```

with:

```text
operation
  -> select evidence slot for the operation family
  -> call handler evidence or forward/yield through it
```

The important transfer is not "pass a handler pointer".  The transfer is:

- operation dispatch should be local;
- handler evidence should be an explicit argument or captured value-env entry;
- the evidence object must carry enough context to model the dynamic handler
  that would have been found by the source semantics.

The paper describes two evidence vector layouts:

- insertion order, which still needs a linear lookup for the nearest handler;
- canonical order, where row typing gives a static index for an effect label.

Yulang should target the canonical-index direction where possible.  The recent
`EvidenceVmFunctionPlan` and `EvidenceVmValueEnvPlan` are already close to this:
they name the operation paths a function or value needs, so the next lowering can
assign stable evidence slots instead of doing name/path lookup at runtime.

### Evidence context in handler evidence

The 2021 paper extends handler evidence from a pair to a triple containing:

- marker / prompt id;
- handler;
- the evidence vector under which the handler was defined.

This matters because tail-resumptive handler code can run in place.  If the
handler clause itself performs effects, those effects must be resolved relative
to the handler definition context, not accidentally relative to the operation
call-site.

For Yulang, this is the same class of bug as callback-origin hygiene:

```text
handler body evidence
caller evidence
callback closure evidence
adapter evidence
```

must not collapse into one current dynamic stack.

Implication:

- Every handler evidence object needs a parent / definition evidence route.
- Every closure, thunk, and function adapter that can call effects needs an
  evidence environment.
- A future executable evidence VM should not reconstruct this by walking
  `mono::Type` or the current control stack.  It should consume explicit
  evidence env plans produced before execution.

### Tail-resumptive operations

The papers identify a common fast path:

```text
op(x) -> resume(e)
```

where the resumption is called once in tail position and is not free in `e`.
These clauses can avoid full continuation capture.  The operation clause can
evaluate `e` directly and then continue.

For Yulang:

- many state-like or reader-like handlers can eventually use this path;
- abortive handlers and nondeterminism are not the first safe target;
- parser branching and `each` may still require non-tail or multi-shot behavior.

The immediate VM target should therefore not be "support all resumptions fast".
It should first classify handler arms:

```text
Abortive
TailResumptive
OneShotYield
MultiShotYield
Fallback
```

The current `EvidenceVmHandlerArmPlan` has `resumptive`, but not this finer
classification yet.

### Under frames / blocker context

Tail-resumptive in-place execution is not just an optimization.  It needs an
`under` frame in the 2021 semantics so operations performed by the handler
clause are resolved with the correct outer evidence.

Yulang already has a corresponding concept in the type system:

- positive evidence says which handler may receive an operation;
- negative / hygiene evidence says which handler must not capture a callback
  origin;
- private tails and hidden stack evidence must remain invisible at public type
  boundaries.

In the evidence VM, `under` should not be modeled as a late marker patch.
It should become part of the evidence object shape:

```text
HandlerEvidence {
  handled_family,
  arm_table,
  definition_env,
  blocker_or_visibility_route,
}
```

This is why a plain closure conversion of handler arms is insufficient.

### Yield bubbling

The 2021 paper localizes continuation capture by changing yield into a value
that bubbles upward while accumulating the continuation piece by piece.

For Yulang, this suggests a good fallback path:

```text
Direct evidence call
  -> tail-resumptive fast path if classified
  -> yield value with continuation fragments when full capture is needed
```

That is different from the current control VM:

```text
operation request
  -> capture current frame stack immediately
  -> resume through marker scopes
```

The evidence VM should avoid building a full continuation for operations that
do not need it.  Yield bubbling is the fallback representation for operations
that do need it.

### Short-cut resumptions

The paper represents bubbled continuation composition as an explicit list or
array of continuation fragments, so resumption can start at the deepest useful
point and share prefixes.

For Yulang, this is useful later, but not the first implementation target.
It becomes relevant when supporting:

- nondeterminism;
- parser backtracking;
- multi-shot continuation reuse;
- recursive `all_paths` style workloads.

The first executable evidence VM can postpone this if it has a clean
`Yield`/`Resumption` representation that can be upgraded later.

### Monadic translation and bind inlining

The 2021 paper eventually translates effectful code into a monadic shape where:

```text
Pure value
Yield marker handler continuation
```

are explicit cases.  The key implementation warning is that naive bind
translation allocates too many closures and can destroy tail recursion.  Koka
uses bind inlining and join-point sharing so the pure fast path stays direct.

For Yulang, this means:

- Do not build an interpreter that boxes every step into a generic monad node.
- If the evidence VM uses `Pure` / `Yield`, compile block sequencing into
  join-point-like code or a register-style instruction stream.
- The first prototype can be simple, but the committed direction should leave
  room for join points and fast pure branches.

## What does not transfer directly

### Koka's public effect rows are not Yulang's hidden stack evidence

Koka uses row types to know the dynamic evidence vector shape.  Yulang has
subtyping constraints, directed stack weights, hidden evidence, and public
projection.  Therefore:

- Koka's evidence vector corresponds mostly to positive handler evidence.
- Yulang additionally needs negative / blocker evidence.
- `#id[Empty]`, private tails, and callback-origin hygiene cannot be erased
  before runtime lowering.

The evidence VM should therefore have explicit slots for both:

```text
positive handler evidence
negative / hygiene evidence
```

The current `ControlEvidenceProgram` already exposes:

- operation routes;
- direct / blocked / unhandled status;
- adapter marker evidence;
- delayed boundaries;
- fallback sites.

That is closer to the needed source of truth than `mono::Type` alone.

### Koka duplicate labels are not the same as Yulang weights

The 2014 Koka paper allows duplicate effect labels to keep row unification
principal and to type effect elimination cleanly.

Yulang's directed weights solve a related but different problem:

- Koka duplicates a label in a public row discipline.
- Yulang tracks origin, boundary crossing, subtraction visibility, and hidden
  stack evidence.

Do not explain Yulang runtime evidence as "just duplicate labels".
The better analogy is:

```text
Koka duplicate labels:
  principal row unification and elimination

Yulang directed stack evidence:
  principal-ish subtyping surface plus handler hygiene
```

### Koka canonical order assumes row shape is enough

Koka can choose a canonical evidence vector order by effect label when the row
shape is known.  Yulang can use operation family paths as a starting key, but
the same family can have different visibility routes because of directed stack
evidence.

Therefore a Yulang evidence slot key should not be only:

```text
family path
```

It likely needs at least:

```text
family path
visibility / blocker route key
projection boundary
```

This is exactly why `EvidenceVmValueEnvPlan` captures requirements by operation
path for now, but should not yet be treated as the final slot key.

## Mapping to current Yulang artifacts

### `ControlEvidenceProgram`

This is the current behavior oracle for runtime evidence.

Use it to derive:

- which operations exist;
- which handlers are lexically available;
- which operations are direct, blocked, or unhandled;
- which function adapters create hygiene boundaries;
- where delayed function/thunk boundaries exist;
- where fallback to the generic VM is required.

Do not bypass this by reading syntax names or paths directly from source text.

### `RuntimeEvidenceSurface`

This is useful for currently observed operation/handler nodes and instance body
ownership, but it is not sufficient by itself for the final evidence VM.

Reason:

- it sees runtime evidence nodes after specialization;
- it does not yet give an executable evidence object graph;
- evidence env capture for closures/thunks/adapters is a value-level concern.

### `EvidenceVmFunctionPlan`

This now approximates function-level hidden evidence parameters:

- required evidence paths;
- provided handler paths;
- known instance calls needing evidence arguments.

This is close to Koka's "function receives evidence vector" idea, but Yulang
will need richer slot keys than paths.

### `EvidenceVmValueEnvPlan`

This approximates closure/thunk/adapter evidence environments:

- lambda body effects;
- thunk body effects;
- adapter wrapped-function requirements;
- adapter marker counts and callback-boundary presence.

This is the first step toward replacing current value marker wrapping with an
explicit captured evidence env.

## Proposed next implementation sequence

### 1. Name evidence slot keys

Introduce a planning-level key distinct from display paths:

```rust
struct EvidenceSlotKey {
    family: Vec<String>,
    route: EvidenceRouteKey,
}
```

Initially, `EvidenceRouteKey` can be conservative:

```rust
enum EvidenceRouteKey {
    Positive,
    Blocked,
    UnknownFallback,
}
```

This should stay in the evidence VM planning layer, not in type inference.

Status on 2026-06-27:

- `EvidenceVmSlotKey` exists in the evidence VM planning layer.
- The first key is intentionally conservative:
  `family path + Positive | Blocked | UnknownFallback`.
- Direct operations use `Positive`, hygiene fallback uses `Blocked`, and
  unproven runtime fallback requirements use `UnknownFallback`.
- This is not yet the final slot key because Yulang still needs a richer
  visibility / projection route key.

### 2. Build evidence function signatures

Convert function/value requirements into explicit parameter lists:

```text
EvidenceFunction {
  body,
  params: [EvidenceSlotKey],
  value_env: [EvidenceSlotKey],
}
```

The output should still be a debug plan first.

Status on 2026-06-27:

- `EvidenceVmFunctionSignature` now reports evidence params, provided evidence,
  and a future value-env slot list.
- `EvidenceVmValueEnvSignature` reports captured evidence slots for closures,
  thunks, and function adapters.
- The debug plan prints these signatures; execution still uses the old runtime.

### 3. Classify handler arms

Add a structural arm classifier:

```text
Abortive
TailResumptive
MayYield
Fallback
```

This can inspect the control IR arm body, but must not depend on source names.
The first version can be conservative and classify unknown cases as `Fallback`.

Status on 2026-06-27:

- `EvidenceVmHandlerArmClass` is in the plan dump.
- Value arms, abortive operation arms, guarded fallback arms, simple structural
  tail-resume arms, and remaining resumptive arms are separated.
- Tail-resume detection uses the control IR body shape and continuation `DefId`,
  not source names.

### 4. Prototype direct evidence calls

Start with a tiny executable subset:

- direct local handler evidence;
- no dynamic call fallback;
- no multi-shot;
- no parser/nondet;
- compare output against control VM.

This subset should prove that an operation can call a handler evidence object
without constructing the current `Request`.

Status on 2026-06-27:

- The debug plan now builds a non-executable evidence object graph.
- The graph separates:
  - evidence slots;
  - function objects;
  - value objects;
  - call objects;
  - handler objects;
  - operation objects.
- Function objects resolve signature params / provides / value-env slots to
  stable slot ids.
- Value objects resolve captured evidence slots to stable slot ids.
- Call objects resolve known instance call evidence arguments to stable slot ids.
- The provider index maps each slot to same-family handler object candidates
  without changing operation lowering.
  `fallback` slots remain `needs-evidence-env`, and `blocked` slots remain
  `blocked-by-hygiene`.
- Value objects now print lexical `env_providers`.
  This is intentionally narrower than full call/action evidence passing: it
  records handler objects that are active at value creation sites, but it does
  not yet prove provider flow through function calls or action parameters.
- Operation objects carry an execution plan:
  `direct-abortive`, `direct-tail-resumptive`, `yield-fallback`,
  `blocked-fallback`, or `generic-fallback`.
- This is deliberately still a plan.  A handler object may exist even when an
  operation remains `generic-fallback`, because the current evidence route has
  not proved that the operation can safely call that handler directly.
- The next step is not to force direct calls from lexical shape alone.  The
  next step is to make function/value evidence environments precise enough
  that operation objects can receive a proven handler object.

### 5. Add yield representation

Only after direct/tail-resumptive cases are clean, add:

```text
Pure(value)
Yield(slot, payload, continuation_fragments)
```

This is where Koka's yield bubbling and short-cut resumptions become relevant.

## Canaries

Keep these cases explicit:

- simple local handler with no resume;
- tail-resumptive reader/state-like handler;
- callback under handler that must not be captured by the inner handler;
- `all_paths` / nondet multi-shot;
- parser branch/backtrack;
- `ref.update` as fallback until callback evidence env is correct;
- function adapter with body / arg / ret marker evidence.

## Current conclusion

The papers support the direction, but also show why a low-level rewrite of the
current control VM is the wrong first move.

For Yulang, evidence passing must be an elaboration from directed stack evidence
into explicit runtime evidence objects:

```text
typed directed stack evidence
  -> ControlEvidenceProgram
  -> function/value evidence env plan
  -> executable evidence object graph
  -> direct calls, tail-resumptive fast path, yield fallback
```

The hard part is not handler lookup.  The hard part is preserving Yulang's
handler hygiene while moving the current marker-stack semantics into explicit,
captured, composable evidence environments.
