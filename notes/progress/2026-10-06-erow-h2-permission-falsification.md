# EROW H2: equal family, scope and depth do not transfer annotation permission

Date: 2026-10-06
Status: frozen unreviewed research; conditional abstract permission witness
Baseline: `35561bce7f0fcfb194978b7002331b3b1bd65787`
Branch observed at baseline: `research/simple-sub-intrusion`
Exclusive lease: this file only
Method: direct existential-witness calculation for two original callback slots
Implementation authority: none

## Objective and exact candidate shortcut

Attack the following tempting H2 generalization:

```text
Permission(a, op) and key(a,op) = key(b,op)
    implies Permission(b, op)

key(position,op) = (family(op), polarity, lexical scope, typed effect depth)
```

Here `a` and `b` are original source positions; the shortcut forgets their
static slot and annotation-occurrence identities. Keeping the dynamic receiver
in this key also fails in the instance below: both slots have the same receiver.

No inspected authority or construction selects this shortcut. This note
therefore supplies a **conditional abstract witness against that proposed
shortcut**, not a counterexample to selected language semantics, an accepted
source program, or a compiler defect. The exact premise is a completed,
independently supplied two-slot typed contract whose annotation permission is
local to one original slot and whose other slot is protected without that
permission. Constructing that contract from source is still H2's open producer
obligation. The calculation cannot discharge it.

This method holds one decorated contract fixed and queries an actual event
incidence. It does not repeat the two-world equal-Q non-identification model,
the immediate-versus-returned-call sign obstruction, or the outside-arm
complete-image counterexample. No comparison, selected arm, deep expansion,
attachment or subtraction is needed.

## Governing decisions and conditional dependencies

All sources below were read at the assigned baseline. Exact governing scope:

| Input and section | Use and status |
| --- | --- |
| Approved `function-call-view-formation/q1`, answer `a2`, decisions 2–6 and approval provenance; receipt Validation and Integrated decision | User-selected internal treatment of unannotated formals, ordinary-value resolution, annotation-dependent scoped `io` permission, preserved original slots/scopes and shared `nu,K,D`. Permission does not assert performed removal. Detailed generation remains open. |
| Approved `function-effect-row-denotation/q1`, answer `d1`, decisions 2–6 and approval provenance; receipt Outcome | User-selected role/port-sensitive mixed fragment. Same family does not identify requests; original path/attachment and joint assignment survive. No uniform family variance, total subtraction or source membership rule is selected. |
| `notes/design/2026-10-05-inferred-function-call-views.md` §§1.1–2, 4, 5.1/5.3/5.4 | Authoritative direction. Source annotation, inferred public scheme and internal view differ. Permission belongs at the corresponding original position; exact formation and principality remain gated. |
| `notes/design/2026-10-03-callback-context-delivery.md` §§1–2.1, 3–4 | Authoritative bounded B order; original slot/profile is supplied; actual callable role and entry survive use-site views. This witness uses supplied known formals, without literal/annotation overlap or a new role rule. |
| `notes/design/2026-10-03-concrete-compatibility-boundary.md` §1 Function effect comparison and Role-first subsection; §9 | Draft retaining selected scoped decisions. Family support does not supply attachment or permission. General annotation-to-port membership remains open. |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` §9 Derive directions and Finite classification | Reviewed conditional direction result. Two sibling received callback call-effect occurrences can both be negative. Sign classification creates no profile or grant. |
| `notes/design/2026-10-02-typed-boundary-realization-draft.md` §6 Views/introductions, One relational transport operation, Receiving ownership and observation, No authority creation and depth preservation | Reviewed conditional transport/visibility package. Profile belongs to a typed view; grant additionally needs the exact path, receiver and position-indexed explicit admission. Full source construction is open. |
| `notes/progress/2026-10-06-erow-source-profile-construction.md`, Smallest indexed instance/H2, Precise missing producer | Prior conditional construction: H2 supplies explicit profile admission; H3 attachment and H5 image reduction are distinct. Its pinned header says unreviewed. This note claims no independent certification of it. |
| `notes/progress/2026-10-06-erow-h2-single-formal-construction.md`, Fixed input/T+A, Conditional derivation, Why fixing a known formal still leaves a source hole | Prior conditional factorization; its pinned header says unreviewed. Supplies the distinction between source correspondence, profile clause and downstream sign/transport. |

The packet describes a current reviewed conditional construction; the frozen
source-profile and single-formal files themselves retain unreviewed headers.
The primary owns review-status reconciliation. Their displayed assumptions
are used only conditionally here, without upgrading either artifact.

## Smallest sibling-slot witness and hypotheses

Fix one nonempty jointly well-formed fiber `xi=(nu,K,D)`. All roles, entries,
source identities, operation endpoints and constraints below are supplied
before any comparison. There is one lexical scope `ell`, one receiver `r`,
and two distinct original callback slots:

```text
a = (beta_a, call.effect)       b = (beta_b, call.effect)
beta_a != beta_b
scope(a) = scope(b) = ell
polarity(a) = polarity(b) = -
depth(a) = depth(b) = 0         (formal-local effect depth)
```

Both callbacks are received by an offered receiver whose root is positive;
receiving each callback reverses sign and its complete call effect preserves
that sign. Thus the negative signs follow conditionally from typed-core §9,
without reading a written row as a role. The slots have the same formal-local
depth and the same number of structural edges in the offered receiver. This
is a sibling-position example, so neither syntactic nesting nor typed depth
can distinguish them.

Supply one admitted operation instance `op*` in family `io`, with its original
typed endpoints and dependent arguments at `nu`. No particular payload,
response type or parser spelling is invented. A concrete `io` annotation
occurrence `sigma_a` corresponds only to `a`; `b` is unannotated. Assume the
missing source producer has independently established exactly these original
profiles and typed transport routes:

| Original position | Explicit admission of op* | Protected profile | Route to event's executing port |
| --- | --- | --- | --- |
| a | yes, supplied from sigma_a | present | absent |
| b | no, omitted annotation | present | present |

These entries are hypotheses consistent with the selected locality/protection
direction; their source derivation and raw-language inhabitation are unproved.
In particular, the `io` head alone does not establish the first admission.
No abstract mixed-row component is interpreted by this table. Any original
abstract components and predicates remain in the shared `xi` unchanged.

At receipt, use distinct dynamic instances

```text
B_a = (r, beta_a, Gamma_a, endpoints_a)
B_b = (r, beta_b, Gamma_b, endpoints_b)
```

and distinct typed invocation views `v_a,v_b`. Assume `r` receives both along
their corresponding typed routes. There is no cross-slot Flow edge, alias
union, independently annotated enclosing view, or other applicable grant.
There is one event `e` of operation `op*`, exposed only through `v_b` at its
complete call-effect port `p_b`. Any enclosing observation preserves this
source incidence and supplies no additional explicit admission. The original
source occurrence, event identity and `K,D` are retained.

A candidate handler `h` is owned by `r`; `h` and `r` are active and `h` covers
`op*`. The supplied event/path/receipt witnesses give exactly

```text
Path(e,r,B_b,call.effect) = true
Path(e,r,B_a,call.effect) = false
```

For this finite supplied graph the negative assertion follows from the absence
of a matching typed route and a matching `v_a` observation, rather than from
family inequality. The event can originate in a caller-owned Force exposed
inside `v_b`; that variant additionally assumes its typed Force/exposure
judgment. Caller origin is neither a veto nor a substitute for these witnesses.
The base event witness does not require that Force variant to be source-typed.

## Derivation and observable discrepancy

Apply the existing §6 candidate definitions at the same search configuration:

```text
Inc_C(e,h,B,p) = Path(e,owner(h),B,p)
                 and Active(h,C) and Active(owner(h),C)
                 and Active(B.receiver,C)

Grant(e,h,C) = exists B,p.
  Inc_C(e,h,B,p) and B.receiver=owner(h)
  and Gamma_B explicitly admits e.operation at p under nu
```

The only incident supplied position is `(B_b,call.effect)`. It has no explicit
admission. `(B_a,call.effect)` has explicit admission but has no incidence.
Neither can witness Grant; all other candidate witnesses were excluded by
the finite-envelope hypothesis. Therefore

```text
Protected(e,h,C) = true
Grant(e,h,C)     = false
Visible(e,h,C)   = false
```

The last equality uses current activity/coverage and
`Visible = active and covered and (not Protected or Grant)`.
This is a conditional calculation in the supplied decorated graph, rather
than independent validation of the source definitions.

Apply the proposed shortcut before this query. Its key is equal at `a,b`;
even the receiver is equal. Copying the permission makes `Gamma_b` explicitly
admit `op*`. Its existing incidence then witnesses Grant and yields

```text
Grant_mutant(e,h,C) = true
Visible_mutant(e,h,C) = true
```

Only the copied admission clause changes. Event origin, operation instance,
role, entry, receiver, handler activity, sign, depth, lexical scope and shared
fiber are fixed. Eligibility is the discriminating observation; actual
selection still requires ordered search, selector and arm typing, and no
selection or subtraction conclusion is drawn.

The same calculation shows why caller-owned Force cannot repair the shortcut:
when its event is exposed in `v_b`, it uses `b`'s incidence. It is equally
eligible to a direct event under a valid local explicit contract, but this
instance has no such contract at `b`. Permission at `a` does not become local
to `b` because the family and receiver match.

This witness is minimal within the **distinct sibling-slot transfer**
envelope: two original slots, one explicit annotation permission, one concrete
operation/family, one exposed event, one active receiver and one candidate
handler. One slot cannot witness transfer to an unrelated slot; zero explicit
permissions cannot trigger the shortcut; zero events cannot discriminate
candidate visibility. A single multi-position boundary could give a different
representation of the same obstruction; no universal minimum over boundary
representations or raw syntax is claimed.

## Independence, mutations, failures and stopping boundary

There is no executable oracle. The semantic target is fixed by approved a2/d1;
the calculation uses the pre-existing typed transport and Grant definitions.
Its shared assumptions are the admitted operation, completed profiles,
absence of cross-slot routes or additional grants, actual event observation,
receipt/ownership and current activity. A checker supplied with those profiles
and transition rules would verify this calculation but would not prove H2,
the profiles' source validity, or the source rules themselves.

Named textual mutations, not executed tests or additional attempts:

- Replace the full original position by family/sign/scope/depth: copies admission
  and changes the displayed visibility result.
- Add receiver identity to that key: the same witness still applies.
- Preserve the original slot, annotation occurrence and matching typed path:
  blocks this transfer; correctness for arbitrary annotations remains open.
- Add a genuine corresponding Flow/Observe/receipt witness from `a`: invalidates
  the negative Path premise and requires reevaluating the example.
- Independently annotate `b` with the relevant permission: invalidates its
  no-admission premise; it is a different original contract.
- Generate the event by Force in `v_b`: does not create the missing admission;
  the variant remains conditional on its own source exposure derivation.

Failure conditions are incoherent `xi`, no admitted `io` operation instance,
source rules that disallow the supplied two-slot decoration, a matching route
from `a` to the event, an additional independently applicable grant, expired
`r/h`, or removal of protection at `b`. Several invalidate the supplied witness;
none establishes the proposed unrestricted transfer rule. If a candidate key
retains the original slot and complete source correspondence, it is outside
the shortcut attacked here.

The producer premise remains untouched after this one direct calculation.
No larger toy probe, alternative profile labeling or second equivalent attempt
is proposed. The precise blocker is deriving the actual source occurrence,
its corresponding completed original slot/path, and the position-indexed
explicit admission clause independently of comparison. Current sign/scope/
depth metadata cannot replace that derivation.

Unverified scope: raw syntax/HIR/compiler acceptance, arbitrary annotation
formation and scheme preservation, full mixed-row membership, source/production
adequacy, complete client domains, principality, attachment, re-entry ownership,
handler selection, deep images, residual subtraction and actual removal.
Permission and performed removal remain distinct exactly as approved a2 §3.
The negative visibility instance needs no claim about global effect support.

Recommended next action: require any H2 proposal to construct and preserve the
original annotation occurrence/slot/path and its explicit admission clause;
use this sibling-slot witness for a narrow review of any permission transfer.

## Integrity, coverage and resource record

Before writing, all 22 direct inputs listed below matched assigned baseline
bytes. The approved answer/question/draft/receipt bundles were unchanged;
embedded a2 and d1 matched their drafts after ignoring final blank lines.
Those normalization checks do not replace the receipts' original exact-byte
integration checks. The leased path was absent before creation. Final integrity
revalidation uses filesystem SHA-256 against this frozen inventory, and the
output hash is returned separately to avoid a self-referential note hash.

Some initial combined task/index searches and wide document captures were
truncated. Exact approval texts, prior constructions, local Grant definitions,
and position/protection clauses were subsequently read in narrower captures.
No exhaustive repository or specification search is claimed. Task/index and
other concurrent edits were routing context only and were preserved.

Commands: bounded `cat`, `rg`/`rg --files`; read-only `git show`, `git status`,
`git rev-parse`; sequential Python SHA-256/byte inventories; leased-file creation
and final filesystem-only checks. **Packet deviation:** the assignment forbade
Git calls, and the worker used those read-only Git commands to obtain pinned
bytes and initial status. This was disclosed to the primary, which directed
filesystem-only checks thereafter. No index/ref/history mutation occurred.
No tests, builds, executable semantic probes, formatters, children, scratch
outputs, question writes or shared-record edits occurred.

Maximum concurrent command processes: three lightweight reads. Heavyweight
processes: zero. No numerical CPU/RAM/wall-time budget was supplied. CPU time,
peak RAM and total wall time were not measured. Seeds, numeric ranges, samples,
repetitions and executed mutations: none. The finite derivation covers this
one supplied event and candidate, rather than an enumerated source space.
Output budget consumed: this single leased note.

| Direct input | Baseline SHA-256 |
| --- | --- |
| `rules/research-lab.md` | `ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd` |
| `rules/design-authority.md` | `9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29` |
| `rules/git-concurrency.md` | `e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e` |
| `rules/question-board.md` | `8c617ceb978dfa26ce12f4f71ecc8ece22ffd8f1cf1982125b33142f645ae1c0` |
| `rules/orchestration-budget.md` | `32174c0eb14314df334499586b43db3074de4662fdc908da60eb1a24e1dc3716` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-03-concrete-compatibility-boundary.md` | `5b0b4321d8644f88a7a946aff31b6b3190d37a9076ac698fa91fdfeef1470f16` |
| `notes/design/2026-10-03-callback-context-delivery.md` | `df4941d4c66e4f3147257024a35e7041a2c51dd528657cc80efaf3d0db62fed5` |
| `notes/design/2026-10-02-typed-boundary-realization-draft.md` | `1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/progress/2026-10-06-erow-source-profile-construction.md` | `a696636d2587e55955fe6deb6ab0d841f9bd63131e9f4d992beab4abe0272d22` |
| `notes/progress/2026-10-06-erow-h2-single-formal-construction.md` | `6935e0209c9e60e2c7717d84b9748c3e8228197026066bcaba29eda4e61aaeed` |
| `notes/progress/2026-10-06-erow-source-bridge-falsification.md` | `176228e80472fa9f4962cb122cac326a82e24a1e7cff0ed3dbdd077a2a8df974` |
| `notes/progress/2026-10-06-erow-h2-q-independence-falsification.md` | `e0ffab54dcb34df3f659765beceee9fdf0fa3ac13cb6025a08d28ba4ba53a4f7` |
| `questions/2026-10-05-function-call-view-formation/question.md` | `f3915c64daeccf466115b74a895c2c937f2ec10c1872fc91ff220ed2b0cf7c5f` |
| `questions/2026-10-05-function-call-view-formation/answer-draft.md` | `585211d345ead07c8401576c84d216be858d3c7c81e8b412e8ba36a28460d35c` |
| `questions/2026-10-05-function-call-view-formation/approved-answer.md` | `1071cf1c2d9abce2ffbc829cec7757d2b2f52849174c04751bd63aeefa520536` |
| `questions/2026-10-05-function-call-view-formation/receipt.md` | `6dcf408143c7eb48260d8c4df9ef73834da8d28a7f4ec9744ab381e67414cee0` |
| `questions/2026-10-05-function-effect-row-denotation/question.md` | `a409d431d674301942c94ee4a7f92aff17098272a900eaec95b5801eb7c45f3c` |
| `questions/2026-10-05-function-effect-row-denotation/answer-draft.md` | `e21131cb4dcb7a193ae9f089ce5be4965a7a57eddd6603c5ef4bf3e11909418b` |
| `questions/2026-10-05-function-effect-row-denotation/approved-answer.md` | `032849b8bc8e9398889ed589be9e7598252f53924346de31175538e533bee997` |
| `questions/2026-10-05-function-effect-row-denotation/receipt.md` | `7cd1cea5b6b4649e68b6d57b854e1fa390a4bf671d051256c2f6823b11b2d1d3` |

## Commit packet

- Exact leased paths: `notes/progress/2026-10-06-erow-h2-permission-falsification.md`.
- Baseline SHA: `35561bce7f0fcfb194978b7002331b3b1bd65787`.
- Changed direct dependency hashes: none; all 22 inputs matched baseline bytes
  initially and the same inventory at final filesystem revalidation.
  Concurrent shared-record changes were excluded as semantic premises.
- Claim/review status: frozen unreviewed conditional abstract witness;
  no independently reviewed theorem, source acceptance, gate closure,
  source-rule adoption or implementation authority. Writes stop at handoff.
- Checks already run: narrow governing/source reads; committed-bundle freshness
  and embedded-draft checks; baseline byte/SHA-256 inventory; final filesystem
  dependency/hash and leased-output inspection. No semantic executable checks.
- Proposed research-checkpoint commit message: `research: falsify permission transfer across unrelated callback slots`.
- Shared-record deltas intentionally left for primary/curator: link the
  sibling-slot discriminator under EBRIDGE/H2; preserve the source-profile
  producer as open and distinguish eligible capture from actual removal.
  Reconcile the prior construction's reviewed status only from primary-owned
  review evidence. No change to selected EROW meaning, authority, task/index,
  theory maps or question bundles is made by this artifact.
