# Handler release crossing: source-query falsifier

Date: 2026-10-05
Status: Frozen, independently reviewed research checkpoint; conditional separation and hand-trace characterization only
Owner/method: handler_release_falsifier; adversarial source-rule substitution and minimized decorated traces
Implementation authority: none

## Objective and pinned dependencies

Test whether the existing typed-path, emission-context observation and handler
transition judgments already determine the approved outward-crossing release
and same-target-view lifetime. This lane does not reconstruct another worker's
filter checker or read unfinished producer artifacts.

Assignment baseline: `e4df3c09643babd2e3ced824bf560d8f7c61440a`.
Source reads are pinned to `659eb05646bb95f10a991bbb9cefdee55721eea1`:

| Source | Exact governing sections | Git blob |
| --- | --- | --- |
| `notes/design/2026-10-02-typed-boundary-realization-draft.md` | §2 selected typed-value transport; §4 “Typed value flow and computation observation”, “Structural observation before dispatch”; §6 “Views, signature positions and introductions”, “One relational transport operation”, “Receiving ownership and observation”, “Transport and lifetime theorem package” | `5e0499e43b3dbf04de0bcdb6c0fa5994224d8a87` |
| `notes/design/2026-10-02-ordinary-computation-semantics-package.md` | §§2–3 request bind, inert construction, entry/re-entry; §4 callback incidence; §5 shallow image and explicit deep reapplication | `640bbfa85630d1dd496a3fd1ccb757536385d720` |
| `notes/design/2026-10-03-callback-context-delivery.md` | §§1–4, especially static/dynamic identity separation and existing-Pure invocation view | `eeed5c2b5dd38404a4c774cda486864a63992fad` |
| `notes/design/2026-10-05-handler-hygiene-public-provenance-notation.md` | “Intended reading”, “Small-step / relational interpretation candidate”, “Examples”, “Open questions” | `0b249e14d1ecb3bea076549b52af121478552491` |

The constraint source is the committed approved answer at `28dddc75f`,
`questions/2026-10-05-handler-protection-release-crossing/approved-answer.md`,
blob `358438b2a6d7b61408713c5dc48bb84b307c75d7`, exact approved clauses 1–7.
It selects actual outward crossing, same-target-view transport while the
original receiver lives, fresh-view/receiver non-copying and expiry. It proves
none of the source correspondence premises below. Expected-context delivery
does not rewrite an existing Pure value's role or entry semantics.

All five committed dependency blobs equal their assignment-baseline and
observed HEAD blobs. Observed HEAD during dependency check:
`f50c8a88882a10f109a71e2842f4d1b02982de53`. Working files equal their pins
except the handler-notation draft; that replacement is intentionally excluded.
The approved answer working file equals its committed pin. Rules read:
`research-lab.md`, `design-authority.md`, `git-concurrency.md`,
`orchestration-budget.md`, and `question-board.md`.

## Claim classes and explicit premises

**Source-text fact:** §4 defines emission-context `Observe` before dispatch;
§6 defines `Protected` as the existence of live incidence, without a release
condition. This is a reading of those pinned equations, not an independent
review of their overall semantics.

**Conditional separation:** given independently valid attribution, slot
departure and same-target-view transport, those unchanged eligibility equations
cannot realize the selected release while retaining their raw incidence
witnesses. The exact missing premise is a source-derived, causally ordered
departure judgment and its lift along certified target-view transport into
later protection queries. The result does not show that full history-indexed
`Rel_C` cannot express those facts or that a new carrier is necessary.

**Bounded characterization:** the six hand cases below discriminate named
shortcuts in a decorated kernel. They are not exhaustive source-program
enumeration, executable validation, or established soundness/principality.

Shared hypotheses for the witnesses:

1. Fix one assignment `ν`, operation `E : Unit -> Unit`, well-typed Unit
   responses, one original live receiver `r`, and one marked target-view
   identity `z` with marked slot `s` for `'e?`.
2. `Attributed(q,'e)` is supplied independently. A family equality,
   `Observe`, protection witness or event label never substitutes for it.
3. Source decoration and receipt establish the stated `Path` facts; no raw
   Yulang acceptance or arbitrary-source elaboration is asserted.
4. Each eligibility discriminator has exactly one applicable protection
   witness at the queried slot, no other excluding boundary, an active
   covering handler and an accepting pattern. Its grant is false unless the
   consumption case explicitly supplies a valid grant.
5. Later same-view observations have an independent certified transport of
   the same target view and an independently `'e`-attributed later event.
   A fresh execution occurrence is distinct from a fresh target view.

## Required transition predicate, with its unproved bridge exposed

For an actual prefix `δ` ending immediately before source transition `τ`, the
needed local trigger has this shape:

```text
Trigger(δ,τ,q,r,z,s,'e) :=
  Active(r,pre(τ)) ∧ Marked(z,s,'e?) ∧ Attributedδ(q,'e)
  ∧ Departδ,τ(q,z,s)
```

`Depart` must certify that **this actual transition** propagates the identified
contribution outward through the marked slot, after preceding intervening
computation/handler processing. It cannot mean emission-context membership or
reachability through a typed-value path. It cannot be defined by recomputing
the current handler image using the very release it is meant to justify.
The notation specifies the proof obligation; the pinned sources do not supply
its complete annotation-to-slot elaboration or transition rule.

The approved lifetime then requires a history predicate with an earlier
`Trigger`, certified continuity to the queried same target view, and an
original receiver still active at the query. Keeping attribution event-specific
prevents a released `'e` slot from releasing unrelated same-family effects.
This is a metatheoretic history specification, not a proposed compiler field,
new source rule or completed construction of `Rel_C`.

The earlier outward-boundary projection in typed-boundary §4 is explicitly
superseded **as Observe**. Its distinction between an event at a child
boundary and an event surviving an intervening handler remains useful when
stating `Depart`; reinstating that old projection as the dispatch observation
would recreate the documented borrowed-owner counterexample.

## Smallest query separation after a valid crossing

Take a later fresh event `q₂`, after a valid first departure of `q₁`. Keep the
original `r` live and establish same-target-view transport to the current
observation. Let its only candidate witness be `w=(b,p)` and retain the
profile, typed receipt, event observation and symbolic predicates as required.
The pinned §6 equations reduce to:

```text
Path(q₂,owner(h),b,p) = true
Active(h) = Active(owner(h)) = Active(b.receiver) = true
Inc_C(q₂,h,b,p) = true
Protected(q₂,h,C) = true
Grant(q₂,h,C) = false
Covers(h,E) = true
Visible(q₂,h,C) = true ∧ (false ∨ false) = false
```

The approved release removes this slot's protection barrier; with the stated
single-witness/no-other-boundary premises the candidate becomes ordinarily
eligible. Thus the unchanged equations distinguish no release history at all.
This is an algebraic contradiction to using those equations **unchanged** as
the approved release-aware query, not a contradiction in the approved meaning.

In particular, define `π` as the inputs read by these equations: current
activity, current event's `Path` witnesses, profile contracts, exact operation
coverage and receiver/owner identities. Two decorated histories, one with a
prior valid same-view departure and one without it, can give the same `π` for
`q₂` but require different protection treatment. No function of `π` alone can
produce both answers. This does not claim that the histories have equal whole
configurations, event logs, evidence graphs or complete `Rel_C` fibers.

One marked slot and one live witness suffice for the query contradiction.
Two events are the minimum needed here to discriminate history transport
without using the first departure as the later event's own crossing.

## Minimized hand traces and mutants

| Case | Decorated trace / distinguishing query | Approved constraint or pinned result |
| --- | --- | --- |
| A: consumed before crossing | `View(z,s, S_h[Emit(q₁)])`; `h` has independent valid eligibility/grant and returns Unit without resuming or re-emitting | `Observe(q₁,z,s,o)` holds at emission by §4; the shallow image returns Unit, so this contribution never departs `s`. No release trigger. One event, one intervening handler, one marked view suffice. |
| B: valid departure | Start unreleased; `Emit(q₁)` propagates past interior processing and a source-certified `Depart(q₁,z,s)` occurs while `r` lives | This first departure triggers release. Release is causally after interior handling, not a mutation of the evidence used by that earlier handling. |
| C: later same-view use | Continue B by typed result/latent transport certified to preserve the same target view; execute later `q₂` under a fresh observer occurrence | No new crossing is required for this already released view. `Observe(q₂,...)` is new; the release continuity is not copied from `q₁`'s observation edge or keyed solely by its event ID. |
| D: fresh target view/receiver | After B, introduce `z′` or receiver `r′`, without same-target-view continuity; use the same underlying closure and same operation family | No automatic release copy. `z′` needs its own eligible crossing. A newly allocated packet along certified same-view transport is not this reset case. Pointer/family/lineage equality is insufficient. |
| E: original receiver expired | After B, expire `r`, then execute the retained latent value with original profile references | §6 `Inc_C` rooted at `r` becomes false. Old release supplies no authority. Ordinary later eligibility may still hold because the old protection also ended. A false release-liveness test does not mean recreating the old mask. |
| F: shallow/deep control | Resume a raw suffix from C; alternatively explicitly rewrap under a fresh deep-handler occurrence | Raw resume restores crossed views under the current context and no selected shallow handler. Same-view continuity plus live original `r` preserves release; a fresh receiver/target slot does not inherit it. Handler identity alone is not the release-lifetime key. |

These cases reject, respectively: `Observe ⇒ Depart`; release-on-emission;
event-only release and release-on-every-observation; pointer/family/global
release; expired-receiver authority or resurrected protection; and automatic
shallow reinstallation or unconditional deep-entry copying. They rely on the
explicit shared hypotheses, not independent source attribution or elaboration.
No general multi-view overlap theorem is claimed from this single-slot set.

### Circular-image countermodel

Use an initially unreleased marked view, one interior handler owned by its
live receiving owner, one protection witness, no grant, and an accepting arm
that consumes `q` without re-emitting. Consider the invalid simultaneous
definition: release exactly when `q` lies in the outward image **computed with
that same new release value**. Write `R` for that value. With no other blocker:

```text
Visible_R(q,h) = R
Out_R(q,s) = ¬R             -- eligible consumes; blocked forwards
R = Out_R(q,s) = ¬R
```

Neither Boolean assignment is a solution. This is the minimum finite
countermodel to that particular circular definition: one event, one handler,
one slot and one bit. The correctly ordered trace instead tests the interior
handler using the unreleased pre-state, forwards if blocked, certifies the
actual later departure, and releases there. It never re-tests the earlier
handler with future release. If another valid grant makes the handler
eligible before departure, consumption gives no trigger, as in case A.

## Independence, coverage and limits

No executable oracle or independent reviewer is claimed. The hand derivation
uses the pinned source equations as its reference and the committed approved
answer as the expected constraint. These are separate inputs, but share the
supplied decoration, attribution, departure and same-target-view premises.
The cyclic countermodel attacks an explicitly named candidate shortcut; it
does not certify any replacement transition system by assuming its rules.

Coverage is exactly the six trace classes and the two Boolean assignments in
the cyclic countermodel. There are no seeds, random trials or enumerated
program ranges. This is one hand-derivation attempt; no equivalent second toy
probe or expanded case-count search was run.

Unverified: raw accepted source examples; full attribution; annotation-to-slot
mapping; identity/continuity for arbitrary structural adapters and multi-input
results; all overlapping protection witnesses; general recursive shapes;
typed-family membership; attachment/subtraction correspondence; complete
source/interface adequacy, finite representation and principality. A source
construction of `Depart` or certified continuity may discharge the exact
premise gap without adding any carrier. No impossible-language or
missing-carrier conclusion follows from this artifact.

Failure conditions for applying the query separation: no valid initial
departure; expired original receiver; no certified same-target-view transport;
later event not independently attributed to `'e`; another protection witness
still blocks; a grant already made the unchanged query eligible; or a governing
dependency changed. The circular countermodel also fails to describe the
candidate if it explicitly orders the departure after interior handling.

## Commands, resources and next action

Checks already run: pinned `git show` reads of the named sections;
`git ls-tree`/`git rev-parse REV:path` for the dependency table; a read-only
Python/subprocess comparison of pinned, baseline, HEAD and working bytes;
focused Markdown/lease inspection. No compiler build, test, executable model,
benchmark, formatter, Git mutation or additional output file was run/created.

Resource budget: at most 15 minutes; lightweight reads/hashes only, no heavy
process, one leased note. Exact CPU, RAM and cumulative wall time were not
instrumented. Hand state space is bounded as above; no incomplete exhaustive
search is concealed.

Recommended next action: have the primary derive `Depart` from the actual
typed computation/slot derivation and certify same-target-view continuity;
then test the derivation against cases A/C/D and the circular-image witness.
Do not use another checker with supplied departure bits as evidence that this
source bridge is complete.

## Commit packet

- Exact lease/changed path: `notes/progress/2026-10-05-handler-release-crossing-falsifier.md` only.
- Baseline SHA: `e4df3c09643babd2e3ced824bf560d8f7c61440a`.
- Dependency SHA/blobs: source pin `659eb05646bb95f10a991bbb9cefdee55721eea1`, answer pin `28dddc75f`; blobs listed above. No committed direct dependency changed at the observed HEAD. Working notation replacement excluded.
- Review status: frozen; independently reviewed by `compiler_referee` with no findings in the assigned scope; no theorem/gate closure or production authority.
- Checks: named pinned-section reads, blob/baseline/HEAD checks, approved-answer working equality and focused lease/Markdown inspection; no compiler/tests.
- Proposed commit message: `research: record handler release crossing query falsifiers`.
- Shared-record deltas intentionally left to primary/curator: add the conditional source-query separation and causality blocker to the handler-release gate; retain the previously selected timing/lifetime; distinguish solved user meaning from the open departure/continuity proof; reference this artifact from task/theory/index records after adjudication. No shared file or question bundle edited.
