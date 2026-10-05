# Hinst: boundary birth separated from typed transport

Date: 2026-10-06
Status: Frozen reviewed research-only conditional derivation and bounded obstruction
Assigned baseline: `524682705cb8009ee9c566dfca1380eef75cc688`
Assigned branch: `research/simple-sub-intrusion`
Exclusive lease: this file only
Method: premise factorization; no executable model or compiler experiment
Implementation/semantic adoption authority: none
Reviewed-by: compiler_referee (conditional derivation; one minor finding repaired and delta closed)

## Objective and result

Factor the H2 note's Hinst into the smallest local source premise plus the
existing introduction and transport consequences. Static `Slots(beta)` and a
supplied same-slot `Receive`/typed correspondence do **not** by themselves
derive Hinst. They lack the source activation that instantiates this original
profile at a fresh receiver boundary. A receipt cannot supply that activation:
typed-boundary §6 explicitly says it creates no boundary or concrete contract.

The additional premise is a source-certified activation of the resolved
callback use **with this original profile under this xi**. Once supplied,
introduction gives the initial profile incidence; typed transport preserves
its clause/predicate identities and derives the target incidence. This reduces
the open source obligation; it does not prove its constructor from syntax.
The approved slot-view retention requirement already specifies the intended
profile preservation. The gap is its source realization, not a new choice
about whether that preservation should hold.

## Governing sources and accepted decisions

| Exact source section | Use and claim class |
| --- | --- |
| Approved `function-call-view-formation/q1`, answer `a2`, decisions 4–6; receipt “Validation” and “Integrated decision and affected scope” | Selected static slot identity/scope, source-derived paths/owners/receivers, joint original `nu,K,D`, Q independence; precise generating rules remain open. |
| `inferred-function-call-views` §§1, 1.1, 2 and 5.1/5.4/5.6 | Authoritative direction; source annotation, public type and internal view differ; static slot and dynamic boundary differ. |
| `callback-context-delivery` §§2–2.1, 3–4 | Authoritative B generation and slot invocation view retaining its original boundary/profile. Context delivery is static; boundary creation occurs on receiver activation. Existing actual Pure/Handler role and entry are preserved. |
| `typed-boundary-realization-draft` §6 “Views, signature positions and introductions”, “One relational transport operation”, “Receiving ownership and observation”, “Transport and lifetime theorem package”, “Concrete realization and proof boundary”; §2 | Selected typed transport principle and reviewed conditional Draft realization. Introduction, transport and receipt have different responsibilities. Full source derivation of profiles/correspondences/re-entry owners remains open. |
| `erow-h2-source-judgment-candidate`, “Conditional derivation and failure boundary” | Reviewed research input defining Hinst. Its source producer remains open; this note addresses only that subgate. |

Neither `[io]` permission nor EROW's separate `write int` fragment is used to
construct a clause here. Hloc/Hclause/Hmatch, completed source formation and
any concrete operation-admission predicate are supplied earlier inputs. This
lane does not revisit same-sign/depth, equal-Q or sibling-slot falsifiers.

## Fixed hypotheses and the candidate activation premise

Fix one resolved known instantiated `Value(F_cb)` formal and its original
static `beta`, completed profile `Slots(beta)` and decorated typed graph.
Fix one jointly well-formed, nonempty assignment `xi=(nu,K,D)` and one original
profile clause `g` at protected effect position `p`. Retain g's original source
occurrence, lexical scope and every predicate identity it references in K.
There is no independent instantiation per port. The applicable original
dependency incidences in D are inputs, not manufactured here.

Assume a supplied, source-certified typed-flow derivation for this same use,
from the received source view's original position p to target effect position
p0. Its composite correspondence is M, with `M(p,p0)`. If several edges occur,
their intermediate typed ports match. Also assume the matching receipt
`Receive(u,slot,v,correspondence)` obtains that same target view; a same-slot
label alone is insufficient. These are the requested transport/receipt inputs.
They say nothing by themselves about which boundary was introduced.

Name the following **candidate obligation interface**, not a new source rule:

```text
ActivateOriginalProfile_xi(delta_use, beta, Slots(beta), p, g)
  => (receiver activation r, dynamic slot a, source view v_src,
      realized signature profile Gamma, type endpoints)
```

For this single-clause obligation the output certificate must establish:

1. delta_use is the resolved activation of this callback contract/slot; r is
   the actual receiver activation and a realizes this beta in that activation.
   It identifies the boundary introduction point, independently of Q.
2. Gamma is the realized profile of that original contract at this use under
   xi. At p it retains this same g, source occurrence/scope and predicate
   identities. It neither substitutes a wildcard nor reinterprets g from
   inferred effect support. No new local operation predicate is postulated.
3. v_src's typed position/domain is the source of the supplied M. Its evidence
   retains the same original K,D under nu; endpoints are those of this use.

This interface omits `chi_original`, the fresh boundary b and transport
equations. Those are derived below. For Hinst's one g it need not prove every
other profile clause; full source adequacy requires the full profile inventory
and generalization/use preservation separately. Splitting the certificate
into slot/use association, actual receiver activation and profile realization
can expose separate producers, but does not remove any of these premises.

The approved texts require these invariants. They do not give a completed
source judgment producing this certificate from static Slots plus Receive.
If “same-slot correspondence” is instead defined to include this activation
and original-profile certificate, it is strong enough; the additional premise
has then been supplied inside that phrase, rather than derived by receipt.

## Conditional derivation of Hinst

Assume the fixed inputs and ActivateOriginalProfile's certificate.

1. **Birth.** At the certified source callback boundary, apply typed-boundary
   §6 introduction to allocate fresh `b=(r,a,Gamma,type endpoints)`. Callback
   §3 places this at receiver activation, not literal elaboration. A fresh b
   is indexed by the dynamic activation; it is not an identification `b=beta`.
2. **Original incidence.** By the initial view's persistent-profile recording
   of the supplied Gamma, its protected position p has
   `chi_original(p,b)`. Clause g belongs to `Gamma_b` at p by the activation
   certificate. This is the definitional recording of introduced profile
   information, not an inference from a receipt or a request's family.
3. **Predicate preservation.** Gamma's g uses the original predicate identities
   under nu. For this source packet §6 transports its dependency incidences as
   `M_*D`; a target assembled from multiple source packets retains the indexed
   union of their images while sharing the same `K` under nu. This packet's
   transported incidences still name their original predicates. No copying of
   predicate truth conditions, freshening or independent solving occurs.
4. **Target incidence.** Apply §6 typed-view transport. The supplied
   `M(p,p0)` and step 2 put the tagged source incidence `(p,b)` into the
   relational image, so `(p0,b)` is present in `chi_v`. This is the
   source-contribution inclusion needed for Hinst. The full transported view
   may also contain incidence from independently contributed sources; Hinst
   does not require equality between that complete view and the image of this
   one source. For a flow chain, composition carries the same tagged incidence
   to the target. The original incidence remains in the source evidence graph.
5. **Hinst.** Steps 1–4 supply a boundary introduced from this original beta
   profile at xi, the same scoped g/predicate in Gamma_b at p,
   `chi_original(p,b)`, and the certified M carrying the original evidence to
   p0. These are precisely Hinst's conjuncts in the H2 input note.

The receipt pins ownership of the use and confirms that the transport target
is the received view; it is not needed to allocate b or establish g. Hinst
alone does not establish Path: the event-specific Observe premise is still
needed. Inc_C additionally needs exact current activity. Grant additionally
needs Hmatch and `b.receiver=owner(h)`. None of these facts proves handler
selection, actual removal, complete handler image or a source program accepted.

This is a conditional derivation within the supplied reviewed Draft package.
The established algebra being reused is relational-image composition and
identity/predicate preservation under its stated hypotheses. The candidate
source activation producer is unproved, and this artifact has no independent
source theorem.

## Smallest missing-birth witness and counterconditions

The logical insufficiency of the weak inputs already occurs with one static
slot, one original protected clause/position p, one receiver/use, one typed
view and identity `M={(p,p)}`. Supply `Slots(beta)={g at p}`, the same xi and a
same-slot typed Receive. Supply **zero boundary-introduction witnesses**.
The view's profile incidence is empty: `chi_src=empty`.

Receipt creates no boundary/contract, and `Id_*empty=empty`. Any finite
composition of the supplied receipt/transport rules still has no b and no
`chi_original(p,b)`; Hinst's existential boundary cannot be obtained. Removing
the sole original position/clause would remove the nontrivial Hinst target;
extra slots, handlers, operations and comparisons are unnecessary.

This is a minimized premise-incompleteness witness, not an executable
experiment or an accepted-source counterexample. In particular it is not a
complete source realization satisfying callback §4: that section requires a
slot invocation view retaining its original boundary/profile. The witness
pinpoints what a complete realization must add. It does not refute the
approved contract or license execution without the required boundary.

Failure conditions for the positive derivation include an activation from
another use/receiver instance; a Gamma clause that changed g's scope/predicate
identity; M lacking p in its domain; mismatched intermediate ports or alias
views; independently instantiated xi; or trying to create the boundary from
Q/row support/Receive. Even an expired boundary may retain raw Hinst profile
evidence; expiry prevents current Inc_C/Grant and is not itself a failure of
this persistent-profile factorization. A new re-entry activation requires its
own source-prescribed owner mapping; transport cannot revive the old one.

## Independence, coverage and next action

No execution oracle or transitions checker was used. Source authority supplies
the required retention direction; the conditional derivation shares the exact
activation/profile/typed-map inputs of the reviewed transport package. A
checker assuming ActivateOriginalProfile would test its consequences and
would not prove the source constructor. No seeds/ranges, exhaustive enumeration,
semantic mutations, builds or tests occurred. The only textual countercondition
is deletion of the required boundary-birth witness from the weak premise set.

Unverified scope: raw syntax/CST/HIR acceptance, profile generation, Hloc and
Hclause/Hmatch, unknown formals/shapes, annotation overlap, arbitrary
instantiation/generalization, uniqueness/principality, complete Option 2
admission, dynamic re-entry, event Observe derivation, mixed-family laws and
production implementation. Search was bounded to the named sources; this is
no repository-wide nonexistence claim.

Recommended next action: derive one source activation judgment connecting a
resolved known callback use and its completed original profile to r/a/Gamma
under xi; then apply this factorization. A further receipt/transport-only
checker would leave that exact constructor untouched.

## Integrity, resources and freeze

The lease was absent before creation. Governing sections were reread in narrow
complete captures after one combined read was truncated. Filesystem SHA-256
snapshots were taken before drafting and rechecked before submission. Approved
a2's embedded content matches answer-draft after separator-newline normalization;
the receipt records integrated approval at
`61a3651376166346a5baa03ec6679c310b0edbdb`. No handoff content was edited.
Current-input equality to the assigned baseline and committed handoff freshness
remain primary-owned; no worker claim certifies them solely from these hashes.

Process deviation: one read-only `git show` of the pinned H2 note occurred
despite the packet's no-Git instruction. The primary was notified, acknowledged
that no mutation occurred and directed filesystem-only continuation. All
remaining reads/writes followed that direction. No index/ref/branch mutation,
children, interactive questions, code/tests/builds/probes, formatting or shared
records were performed. One read batch used three concurrent lightweight shell
processes; subsequent commands were sequential. Heavyweight process count zero.
CPU/peak RAM/wall time were not instrumented; no numerical budget was assigned.
Output is exactly one leased note. The independent review identified a minor
overclaim where a single-source relational image was stated as the whole target
evidence packet. The derivation now records the source-tagged chi/D images as
contributions within a potentially multi-source target; the reviewer closed
this delta. No semantic conclusion beyond Hinst's original incidence follows
from the repair.

### Direct dependency SHA-256 snapshot

| Input | SHA-256 |
| --- | --- |
| `notes/design/2026-10-02-typed-boundary-realization-draft.md` | `1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb` |
| `notes/design/2026-10-03-callback-context-delivery.md` | `df4941d4c66e4f3147257024a35e7041a2c51dd528657cc80efaf3d0db62fed5` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/progress/2026-10-06-erow-h2-source-judgment-candidate.md` | `af5990c4f54553c9a11e5913422399a60228f8240f5c3a90aff165901c396df2` |
| `questions/2026-10-05-function-call-view-formation/question.md` | `f3915c64daeccf466115b74a895c2c937f2ec10c1872fc91ff220ed2b0cf7c5f` |
| `questions/2026-10-05-function-call-view-formation/answer-draft.md` | `585211d345ead07c8401576c84d216be858d3c7c81e8b412e8ba36a28460d35c` |
| `questions/2026-10-05-function-call-view-formation/approved-answer.md` | `1071cf1c2d9abce2ffbc829cec7757d2b2f52849174c04751bd63aeefa520536` |
| `questions/2026-10-05-function-call-view-formation/receipt.md` | `6dcf408143c7eb48260d8c4df9ef73834da8d28a7f4ec9744ab381e67414cee0` |
| `rules/research-lab.md` | `ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd` |
| `rules/design-authority.md` | `9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29` |
| `rules/git-concurrency.md` | `e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e` |
| `rules/question-board.md` | `8c617ceb978dfa26ce12f4f71ecc8ece22ffd8f1cf1982125b33142f645ae1c0` |

## Commit packet

- Exact leased path: `notes/progress/2026-10-06-erow-hinst-source-factorization.md`.
- Baseline SHA: `524682705cb8009ee9c566dfca1380eef75cc688`.
- Dependency changes: none authored; start/end integrity and baseline comparison
  must be reported separately. Routing files are locators, not semantic inputs.
- Review status: reviewed research-only conditional factorization and minimized
  premise-incompleteness witness; one minor multi-source image overclaim was
  repaired and delta-reviewed. No source/gate/authority promotion.
- Checks run: bounded section inspection, a2 embedded-draft equality and markers,
  dependency SHA-256, lease absence/scope. No semantic execution/tests/builds.
- Proposed commit: `research: factor Hinst boundary birth from typed transport`.
- Shared deltas intentionally left for primary/curator: link this factorization;
  preserve Hinst's source activation/profile-realization producer as open;
  distinguish existing slot-view retention authority from its missing generator.
  No task/index/theory/authority/question-board writes belong to this lease.
