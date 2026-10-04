# Mixed effect-component membership: candidate distinction probe

Date: 2026-10-05
Status: bounded exploratory model; no selected annotation semantics or implementation authority
Scope: compare component-family coverage with an annotation-occurrence filter over complete typed observations in one fixed relation fiber
Branch: `research/simple-sub-intrusion`
Governing sources: [concrete compatibility](../design/2026-10-03-concrete-compatibility-boundary.md) §§6–9, [ordinary computation semantics](../design/2026-10-02-ordinary-computation-semantics-package.md), and the approved [mixed-row handoff](../../questions/2026-10-05-function-effect-row-denotation/receipt.md)

## Question

The approved mixed-row fragment fixes a polarity-sensitive example, while the
source-to-descriptor mapping remains open. In particular, the current source
rules do not decide whether a concrete row component covers every compatible
contribution in the component's complete typed port view, or whether it
filters that view to contributions owned by the same source occurrence as the
row item. Family support alone cannot distinguish these interpretations.

This probe makes the difference explicit while retaining one complete
observation, its source events, and one fixed `Rel_C` `(nu,K,D)` fiber. It does
not treat immediate requests as the whole port view: an event in a resumed or
latent suffix remains part of the complete observation and retains its own
identity, origin, and typed path.

## Candidate interpretations

For concrete component `write int` at port `p`, the checker compares:

1. **Port coverage:** a complete observation is covered when it contains a
   typed `write int` event whose path reaches `p`.
2. **Component-owned filter:** require the same family, type arguments, and
   port path, and additionally require the event's source occurrence to be the
   occurrence assigned to this row item.

Both preserve event identity, origin, and the shared relation fiber. Neither
is selected semantics. The second is not the user's statement that concrete
contributions can be subtraction targets; subtraction still needs its own
attachment and complete-image evidence.

## Finite result

[`research_effect_component_membership.py`](../../tools/research_effect_component_membership.py)
enumerates all 31 nonempty subsets of a five-event universe in one fixed
fiber. Controls include a wrong family, wrong family argument, and an event
without a path to the port. The model retains a same-family/same-type suffix
event with a different source occurrence. Eight of the 31 complete
observations distinguish the two candidate readings. The minimized witness
contains only that one compatible suffix event: port coverage accepts the
observation; the component-owned filter rejects it.

The run confirms that the choice affects complete-view membership, even when
both candidates preserve the full event and `K,D` identities. It does not
establish which reading follows from Yulang source semantics, or that either
candidate is adequate or principal.

## Limits and next gate

The model uses fixed event records and Boolean path attachment. It does not
derive those records from source annotations, elaborated Function ports, or
the actual `Flow`/`Observe`/occurrence machinery. It does not execute handlers,
model arbitrary continuation relations, interpret abstract row components,
or implement the single `A <: B` solver. Its 31 cases characterize the stated
finite comparison only.

The next semantic step is to derive the concrete component's membership
predicate from the source annotation and its role-indexed typed port, over the
same complete observation fiber. If source authority does not distinguish
the two candidate readings, that exact choice must be returned for user
selection. No new carrier is justified by this probe.

Verification for the initial candidate comparison: `python3
tools/research_effect_component_membership.py`, `python3 -m py_compile
tools/research_effect_component_membership.py`, and `git diff --check` passed.
No compiler tests, builds, production code, or Oracle investigation were
performed.

## Follow-up: separate membership from subtraction

The two candidate readings above do not capture the user's separate
requirement that reverse addition operate only on a concrete contribution with
known attachment. The follow-up
[support/attachment probe](2026-10-05-effect-attachment-subtraction-playground.md)
shows why component membership, per-event subtraction authority, and
complete-output support removal must be considered separately. Treat the
comparison above only as a finite illustration that an exact-owner filter is
not equivalent to family/type coverage.

## Reconciliation with the selected callback-visibility rule

The governing ordinary-computation package §7 records the user's 2026-10-02
decision: direct requests and caller-owned requests exposed by `Force` have
equal eligibility under the same concrete typed callback boundary. Its §4
defines capture through the active receiver/handler, an explicit contract
`Γ_b`, per-event `Inc_C`, typed `Flow`/`Observe`, and the receiver's receipt for
the same view. This rules out exact event-origin equality as an eligibility
condition once that contract and incidence are established. Origin remains
evidence; it does not veto a caller-owned request exposed by `Force`.

The checker at the current path now tests that selected relation over 256
combinations. Direct and caller-`Force` origins have equal eligibility when
the concrete contract, typed observation path/incidence, and active receiver
and handler agree. A family-only mutant has 60 false positives; an exact-origin
filter rejects two otherwise eligible caller-`Force` cases in this finite
matrix. The result is a consistency check, not an independent source-machine
proof.

This closes the origin-filter ambiguity for the selected callback-visibility
subcase; it does not define general row membership. The remaining source gate
is to elaborate the concrete surface component into the right `Γ_b` profile
and typed port, then compose abstract component views and attached concrete
subtraction in one complete `Rel_C` fiber. The prior user-facing binary
question that treated whole-view membership and event ownership as alternatives
is withdrawn; no new semantic decision follows from this probe.
