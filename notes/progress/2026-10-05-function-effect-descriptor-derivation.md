# Direct source derivation attempt for Function effect descriptors

Date: 2026-10-05
Status: focused derivation attempt; no annotation semantics or implementation authority
Scope: Value-entry callback invocation and the missing interpretation of a mixed abstract/concrete effect descriptor
Branch: `research/simple-sub-intrusion`
Governing sources: [concrete compatibility](../design/2026-10-03-concrete-compatibility-boundary.md), [ordinary computation semantics](../design/2026-10-02-ordinary-computation-semantics-package.md), [typed computation core](../design/2026-10-02-typed-computation-core-elaboration.md), and [callback context delivery](../design/2026-10-03-callback-context-delivery.md)
Independent review: compiler_referee; no blocking or major findings; two scope clarifications incorporated below

## Result

The selected source rules derive the operational Value-entry invocation skeleton

```text
receipt; Force(D) >>= rebind >>= body >>= designated result consumer
```

inside the complete `J_call` relational image. This is not a replacement
definition of `J_call`: the full image also retains the actual receiver,
native return delimiters, surrounding executing view, and separately admitted
result adaptation. A support bound from the argument and body is valid only
when the body term covers its designated result consumer, or that consumer is
bounded separately. These qualifications follow typed-core §9 and
callback-context §§3–4.

At one fixed `xi = (nu,K,D)` and original scopes, this execution derivation
preserves each request's operation instance, origin, continuation, live resumed
state, and event-specific incidence. The reviewed shallow-handler rule also
preserves raw continuation requests: handling one event does not erase a later
same-family event that the continuation emits.

The derivation does **not** produce satisfaction rules for a mixed descriptor
`[alpha, tau]` at a role-derived polarized Function port. In
`concrete-compatibility-boundary.md` §§6–8, all of the following are still
conditional rather than derived:

1. mapping abstract `alpha` to a complete correlated view at its typed port;
2. mapping concrete `tau = F(args)` to an owned typed family incidence;
3. defining their component-combination rule in the same nonempty `Rel_C`
   fiber, retaining shared `K,D` and separate incidence;
4. justifying a contravariant reversal only for a concrete contribution whose
   attachment and source-supported subtraction are witnessed.

Thus existing evidence is not shown insufficient, and no new carrier follows.
The smallest missing premise is a **comparison-independent source annotation
clause for a mixed abstract/concrete descriptor at its role-derived polarized
port**, covering both components and their joint constraints/attachments.
This is a missing derivation, not yet a demonstrated semantic choice.

## Event-identity discriminator

The following schematic transition tests an unsound support-only shortcut:

```text
D = perform tick(v); perform tick(v); return v
handle the first tick and resume its raw continuation once
```

Under the selected shallow semantics, if the first event is eligible and
selected, the response permits resumption, and no outer handler consumes the
second event, the resumed raw continuation can expose a distinct second
`tick`. Family support alone cannot cancel that second event merely because
one `tick` was handled. The complete handler image and existing event/path
evidence distinguish them. This rejects global family cancellation without
complete-image absence evidence; it does not reject every attachment-aware
partial reverse step and does not define what `tau` means in an annotation.
The example is schematic; exact raw Yulang annotation syntax and wiring are
not established by this transition.

## Bounded executable characterization

[`research_mixed_effect_subtraction.py`](../../tools/research_mixed_effect_subtraction.py)
enumerates 96 fixed histories of two or three events from one source-flow
origin. It assumes the first event is eligible and selected, one response
resumes the raw suffix once, and the outer context is represented by a
terminal family filter with no additional requests, state dependence, guards,
or resumption. In this fragment, event identity is distinct from both source
origin and family. The minimized two-event same-family witness leaves the
second event in output while support-wide cancellation removes the family.

This checker verifies the stated finite transition model; most assertions are
structural consistency checks of that model, not an independent proof of the
source machine. Actual outer handler images, arbitrary continuation use, and
any annotation-to-descriptor interpretation remain outside its scope. An
independent spec audit found no defect within the bounded scope and required
these origin and outer-handler qualifications.

## Proof boundary

The derivation closes source execution composition for this bounded callback
case, not `D_actual`/`P_actual` membership, production Function descriptor
satisfaction, or callback adequacy. It also does not turn complete denotation
inclusion into a general concrete subtyping relation: the endpoint-dependent
inequality solver remains non-compositional on successful concrete checks.
The production gate remains the direct derivation of comparison-independent
descriptor membership and challenge admission, followed by the actual-to-
checked containment theorem on the same complete fiber.

No production implementation, broad tests, builds, or Oracle investigation
were performed for this focused derivation. The bounded checker above is
research-only.
