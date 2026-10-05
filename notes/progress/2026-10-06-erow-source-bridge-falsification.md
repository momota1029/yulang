# EROW source bridge: outside-arm non-entailment witness

Date: 2026-10-06
Status: frozen unreviewed research checkpoint; conditional source-equation witness
Baseline: `95d5af37ae71cfeedda1b325159353b4c7b1a386`
Branch: `research/simple-sub-intrusion`
Lease: this file only
Method: instantiate the existing deep source expansion; no executable probe
Implementation authority: none

## Objective and exact claim

Attack one EBRIDGE route: deriving absence of a concrete family/type point
from the complete deep-handler output merely because an annotation-matching,
attached input request was selected. The attacked candidate rule is:

```text
an attached input q_t at W = write int is selected by the deep expansion
    implies
W is absent from support of the complete handler image J_out
```

Equivalently, the shortcut computes `support(J_out) minus {W}` after selection,
without an output-absence derivation. Even granting the shortcut its missing
annotation/profile/attachment premises, this implication fails in the
existing source-equation candidate: an arm emits a fresh event at W outside
the selected handler, without invoking its continuation.

This is a **conditional non-entailment witness**, not an accepted raw-source
program, compiler counterexample, reviewed theorem, or new semantic rule.
The source package is Draft, with its shallow/deep expansion locally reviewed.
EROW §9 fixes the selected meaning and explicitly retains arm effects in the
complete image. The note instantiates that meaning; it does not reopen it.

It does not claim that the arm event belongs to the shared abstract component
`'e`. Removing the attached input contribution from that component can coexist
with an independently contributed arm effect at W in the total image. The
invalid route is promoting the targeted removal to total-image support absence.
An event-sensitive projection that retains the arm contribution is unaffected.

## Governing sources and fixed decisions

All semantic reads below used `git show <baseline>:<path>`.

| Source | Exact scope used |
| --- | --- |
| `notes/theory/inference-theorem-dependencies.md`, EROW/EBRIDGE/PPROJ ledger and dependency prose | EROW is scoped user authority; annotation membership and complete-image adequacy remain open. PPROJ requires independent attribution/emission and preserves other evidence. |
| `questions/2026-10-05-function-effect-row-denotation/approved-answer.md`, q1/d1 decisions 2–6; `receipt.md` | Shared polarity-sensitive row, supplied `int <: 'a` instance, deep targeted removal, original event/path/attachment and joint `(nu,K,D)`. Shallow principal type remains tentative. |
| `notes/design/2026-10-03-concrete-compatibility-boundary.md`, §1 “User-directed Function effect comparison” and §9 | Complete handler-image absence is needed before a concrete support point disappears; selector/arm effects, re-emissions, latent results and later uses remain. No general family variance or new carrier is selected. |
| `notes/design/2026-10-02-ordinary-computation-semantics-package.md`, §§2–3 and §5, especially “Primitive shallow image and explicit deep reapplication” | State-threaded bind; request construction versus force; arm executes outside selection; `D_H` wraps exposed raw continuations, including those retained by closures. Arm requests before wrapper invocation remain outside. |
| `notes/design/2026-10-02-typed-boundary-realization-draft.md`, §4 “Structural observation before dispatch” and §6 “Views, signature positions and introductions”, “Receiving ownership and observation”, “Concrete realization and proof boundary” | Observation is from executing typed context before dispatch; it is not outward support or annotation satisfaction. Profiles, receipts and current incidences are distinct. Source profile/elaboration remains an input. |
| `notes/progress/2026-10-05-concrete-capture-profile-derivation.md`, conditional corollary, separate subtraction obligation, missing premises | Given an established profile, local eligibility follows; this does not construct that profile or prove support subtraction. |
| `notes/progress/2026-10-06-annotation-occurrence-profile-bridge.md`, minimum additional judgment and conditional derivation | Admitted annotation and completed contract do not themselves derive correspondence to an original typed profile position. |

The 96-history shallow probe, 256 attachment/output probe, 4,096 conditional
protection filter and graph-route probes are historical bounded evidence.
They supply no premise here, and their domains were not enumerated again.
The new method uses the outside-arm clause of the explicit deep expansion,
with zero continuation invocations, rather than a supplied event-history model.

`'e?` releases only independently attributed protection under its selected
crossing/lifetime rule. It does not establish membership, attach a contribution,
select this arm, subtract W or complete this EBRIDGE proof. No protection
marker, guessed pop count or changed release interpretation is used.

## Explicit hypotheses

Fix one nonempty original `Rel_C` fiber at one joint `(nu,K,D)`. The witness
is conditional on these hypotheses, which are not derived by this note:

1. One declared operation instance W has payload `int` and response `Unit`;
   the fixed assignment admits payload `0` and both requests below. W names
   the same complete concrete instance in both events, not merely a family.
2. Input computation `c_t` explicitly forces a constructed W request.
   Its generated event is `q_t`, with source origin `o_t`, continuation `k_t`,
   and its original symbolic predicates and dependent incidences.
3. At the actual input search point, an active H occurrence is reached and
   its pattern/guard selects `q_t`. Visibility, any needed concrete profile,
   typed incidence, attachment to the selected input contribution, and
   `OpCompat` have their own witnesses under the same assignment. We grant
   these to the proposed shortcut; family or row membership does not prove them.
4. H has a pure selector and one compatible operation arm. The arm explicitly
   forces a new W request with payload `0`, then returns `Unit` if answered.
   It never invokes or stores the received continuation. Its return arm is pure.
   The complete typed output admits this independent arm effect. No outer
   handler consumes the new event before the measured output boundary.
5. Request identity is fresh at emission: `q_t.event != q_u.event`. The arm
   request has origin `o_u`, its own continuation and dependent incidence;
   the two requests can use the same operation/type predicate in the shared
   ledger. Emission does not merge those dependents or discard retained roots.

Hypothesis 4 is essential. A fully specified source signature that rejects
this arm does not instantiate the witness. No annotation-to-complete-signature
rule was found in the inspected chain that establishes this exact source
instance. Therefore this is an abstract source/evidence non-entailment result,
with its source realization gap exposed, rather than a typing failure claim.

## Smallest witness and derivation

Operational notation below abbreviates existing source-demanded forcing;
`MakeRequestThunk` is the package's internal constructor, not proposed syntax.

```text
Emit_W(0) = Force(MakeRequestThunk(W, 0))
c_t       = Emit_W(0)
H.W(a,k)  = Emit_W(0) >>= (lambda response. Return(Unit))
H.return(v) = Return(v)

wrap_H(k) = lambda a. D_H[Resume(k,a)]
D_H[c]   = S_{H with exposed k bound as wrap_H(k)}[c]
```

1. Inside the derived expansion, `c_t` yields `Request(q_t,C_t,k_t)`.
   Hypothesis 3 establishes selection of the attached target by H.
2. The shallow-image equation exits that H occurrence before running the
   selected arm. Let `C_out` be this outside configuration. The arm receives
   `wrap_H(k_t)` as its continuation value.
3. The arm ignores that value. Constructing the wrapper executes no resumed
   suffix. Consequently no fresh H is entered by deep reapplication.
4. The arm's explicit force generates fresh `q_u` at W in `C_out`. Its request
   continuation returns `Unit`; ordinary bind preserves this suffix. The
   selected input event was consumed, but the outside arm event is yielded by
   the full image:

   ```text
   D_H[c_t] yields Request(q_u,C_out,k_u)
   q_t is consumed; q_u is outward; concrete_instance(q_u) = W
   ```

5. Therefore `W in support(J_out)`. The proposed total-image cancellation
   returns no W, contradicting this required image projection. Targeted
   removal of `q_t` succeeds while preserving `q_u` and its evidence.

Replacing the arm by `Return(Unit)` gives an empty immediate request image
with the same input, input attachment, profile, selection and unused raw
continuation. Thus those input facts alone cannot determine output absence;
the arm's complete source image is a necessary discriminating dependency.
This textual mutation was not executed.

For this *immediate fresh-arm-output* obstruction, two dynamic emissions are
minimal: one selected input event and one distinct event that survives.
There is one operation instance, one handler, one pure selector, no resumption,
no nested view, no store mutation and no effect marker. A single emission
cannot be both the consumed input event and a fresh preserved arm event.
This minimality does not cover latent-value dependency or other obstructions.

The derivation preserves the retained `K,D` ledger and every live dependency
of `q_u`; disappearance of an input request is not a license to erase shared
formulas, origins, continuation roots or incidences. It supplies no new
attachment representation. Arm effects also explain why wrapping resumptions
does not turn primitive shallow selection into family-wide deep erasure.

## Precise remaining producer and independence

The first missing source producer in the inspected chain is a Q-independent
derivation from an admitted mixed-row annotation occurrence and completed
original role-indexed contract to its original typed effect position/profile,
the abstract/concrete contribution interpretation, and event-specific
attachment in the same nonempty `(nu,K,D)` fiber. The earlier annotation audit
isolates this occurrence-to-profile correspondence; CAP assumes its result.

After that producer, a complete-image derivation must connect the exact
attachment/removal witness to the handler expansion, preserving independently
contributed arm/selector/latent/resumption effects. To conclude *total support*
absence of W, it must additionally show there is no remaining contribution
at W throughout the complete image and relevant future interactions. This
last condition is deliberately stronger than the selected `'e`-component
targeted removal. A checker supplied with that absence condition cannot prove
that the source annotation generated it.

No independent execution oracle was used. The derivation shares the reviewed
Draft source equations, visibility/typing premises and nonempty-fiber premise.
It validates neither source typing nor those premises through a second
implementation. The source clauses discriminate the shortcut directly;
there is no duplicate checker or claim of independent certification.

Failures or omissions: a rejected arm, unproved operation declaration, missing
input selection/attachment, empty fiber, intervening outer consumption, changed
source equations, or measuring only the shared `'e` component instead of total
output prevents the stated instantiation. Full raw-source grammar/acceptance,
annotation elaboration, arbitrary mixed membership, future latent behavior,
general recursive deep typing, soundness/principality, PPROJ and compiler
adequacy remain unverified. No exhaustive repository impossibility is claimed.

Recommended next action: require an EBRIDGE source producer to keep targeted
input subtraction separate from the independently typed arm image, and use
this no-resumption outside-arm instance as its first complete-image obligation.
If it cannot construct the source annotation/attachment judgment, return that
precise premise rather than another supplied-transition probe.

## Checks, resources and dependency snapshot

Read-only checks: `git rev-parse HEAD`, bounded `git status --short`,
`git show 95d5af37a:<path>`, `rg`/`sed` locators, and a Python read-only
SHA-256/byte comparison of pinned and live dependencies. The embedded approved
draft text also matched the saved draft after trailing-blank normalization;
the integrated receipt supplies its original byte-for-byte validation.
The selected q1/d1 question, draft, answer and receipt all matched the pinned
bytes in the worktree. HEAD remained the assigned baseline at revalidation.

No tests, builds, probes, Oracle commands, randomized seeds, ranges, repeated
samples or Git mutations were run. The lease allows only this note, and it was
absent before creation. Some broad routing reads were truncated; the semantic
conclusions use the subsequent narrow excerpts listed above. Parallelism was
limited to short read-only command batches (maximum five); no heavyweight
process, child agent or measurement process ran. Peak CPU/RAM and total elapsed
wall time were not measured; no numeric wall-time budget was supplied.

SHA-256 of frozen semantic/research dependencies:

| Path | Baseline SHA-256 |
| --- | --- |
| `notes/theory/inference-theorem-dependencies.md` | `5ecd639ae33943c86937b7783da97da5471bdc67205b8c9c619ac9ba7edd4f38` |
| `notes/design/2026-10-03-concrete-compatibility-boundary.md` | `5b0b4321d8644f88a7a946aff31b6b3190d37a9076ac698fa91fdfeef1470f16` |
| `notes/design/2026-10-02-ordinary-computation-semantics-package.md` | `ee3f5cf8185d516775b8915b0fda6dbb07390c3ecad7ac028eb5995581dff917` |
| `notes/design/2026-10-02-typed-boundary-realization-draft.md` | `1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb` |
| `notes/progress/2026-10-05-concrete-capture-profile-derivation.md` | `a7ef12555b688e0e7f22c1c9d8936ab952282da08896f49646cfe78c0afbfc79` |
| `notes/progress/2026-10-06-annotation-occurrence-profile-bridge.md` | `2ace5a896d205d14a75cf90b582802ffc8477800d87e5f1e9da678a369237a46` |
| `questions/2026-10-05-function-effect-row-denotation/question.md` | `a409d431d674301942c94ee4a7f92aff17098272a900eaec95b5801eb7c45f3c` |
| `questions/2026-10-05-function-effect-row-denotation/answer-draft.md` | `e21131cb4dcb7a193ae9f089ce5be4965a7a57eddd6603c5ef4bf3e11909418b` |
| `questions/2026-10-05-function-effect-row-denotation/approved-answer.md` | `032849b8bc8e9398889ed589be9e7598252f53924346de31175538e533bee997` |
| `questions/2026-10-05-function-effect-row-denotation/receipt.md` | `7cd1cea5b6b4649e68b6d57b854e1fa390a4bf671d051256c2f6823b11b2d1d3` |

The live dependency ledger was already concurrently changed; observed live
SHA-256 was `708885dbd29e2677ebb336dbe82cb5ee246409fa4b013444ddcf3faf58170b99`.
Its live edits were not consumed as premises. Other listed inputs matched the
baseline; unrelated task/index/protection/checker/question edits were preserved.
Primary integration must revalidate this dependency cone if the baseline moves.

## Commit packet

- Exact leased path: `notes/progress/2026-10-06-erow-source-bridge-falsification.md`.
- Baseline: `95d5af37ae71cfeedda1b325159353b4c7b1a386`.
- Changed dependency hashes: the live theory ledger differs as recorded above;
  no live change was consumed, and no other listed dependency changed.
- Claim/review status: frozen unreviewed conditional source-equation
  non-entailment witness; no source/compiler counterexample or gate closure.
- Checks already run: pinned source inspection, handoff freshness and
  dependency hash/byte checks; final note hash belongs in the primary packet.
  No executable verification, tests or builds.
- Proposed checkpoint commit: `research: isolate outside-arm obstruction to deep support cancellation`.
- Shared deltas left to primary/curator: link the conditional witness from
  EBRIDGE and `tasks/current.md` if accepted; record the separate arm-image
  obligation and open annotation/attachment producer. No change to EROW,
  PPROJ, authority status, indexes, questions or compiler implementation.
