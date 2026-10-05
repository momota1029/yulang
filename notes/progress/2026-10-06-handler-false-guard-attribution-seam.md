# False-guard example: attribution seam and outer-query discrimination

Date: 2026-10-06
Status: frozen, unreviewed research; conditional equation lemma and bounded source-rule audit
Baseline: `45b81a28d614f9f0a4d15c7a861347cb14506566`
Exclusive lease: this file only
Implementation authority: none

## Objective and result

Inspect whether the exact false-guard example can acquire independent `'e`
attribution and a marked-slot association from existing source rules, then
reach the existing outer-query definitions. Method: audit original annotation
and profile introduction, derive the maximum existing `Path`/`Inc_C` join,
and compare the two candidates' equations. The previous operational trace is
a locator for the instance, not authority for the missing association.

Two bounded results:

1. **Conditional equation lemma:** in the exact instance, inner and outer
   handlers share owner `r`, request evidence and coverage. The false guard
   changes neither receipts nor profiles and only the inner handler expires.
   Inner eligibility consequently implies unreleased outer eligibility. This
   example cannot discriminate release-dependent eligibility, even if a
   correct marked-slot association is supplied later.
2. **Precise source-rule blocker:** original annotation occurrence, original
   static callback slot, dynamic boundary, typed profile transport and event
   observation can be retained. None of the inspected rules derives the
   independent event-to-`'e` attribution and marker-to-full-protection-witness
   association. The notation rule uses those facts as premises. No admitted
   marked surface program or smallest source counterexample was established.

This does not reject the approved meaning or require a new carrier. It
separates an already available ordinary evidence join from a missing judgment.

## Exact governing sections and dependency hashes

All reads use the assigned committed revision. At collection, `HEAD` equaled
the baseline. The approved q1/d1 meaning remains actual outward crossing after
intervening processing, same target while the original receiver is active,
no release caused by consumption without crossing, and protection-only change.
It supplies no selection, capture, consumption, subtraction or implementation.

| Source | Exact inspected sections / baseline lines | Git blob |
|---|---|---|
| `questions/2026-10-05-handler-protection-release-crossing/approved-answer.md` | Exact approved draft, decisions 1–7 | `358438b2a6d7b61408713c5dc48bb84b307c75d7` |
| Same directory, `receipt.md` | Validation; Outcome and reason | `154641f508ea224b5e907639e6c685b207cb3a84` |
| `questions/2026-10-05-function-effect-row-denotation/approved-answer.md` | Decision 6: shared role/port/`Rel_C` fiber, retained occurrence/path/attachment, source-evidence derivation still required | `77e28d7826634421a98e556a0023b29c762420ad` |
| `notes/design/2026-10-03-callback-context-delivery.md` | §§2–4, lines 38–78, 82–112, 130–178: supplied formal and original slot/profile, independent endpoints, dynamic boundary and invocation view | `eeed5c2b5dd38404a4c774cda486864a63992fad` |
| `notes/design/2026-10-02-source-computation-role-elaboration.md` | §4, lines 144–180; §8, lines 392–414: original annotation occurrence and role projection; requirements versus finished rules | `10775573537d8b56423f796db3c7ac6bb427e252` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | §2, lines 55–85; §7, lines 537–565: derivation-indexed supplied annotation positions and checking preserves slots | `d0948191bbc2d1eb10a7e6e360dc8852a185db1d` |
| `notes/design/2026-10-02-typed-boundary-realization-draft.md` | §4 Structural observation before dispatch; §6, lines 670–753, 792–868: typed views, original profiles, tagged transport, `Path`, `Inc_C`, `Grant`, `Visible` | `5e0499e43b3dbf04de0bcdb6c0fa5994224d8a87` |
| `notes/design/2026-10-02-ordinary-computation-semantics-package.md` | §2, lines 46–84: event/origin versus type binder; §4, lines 293–345: capture join and concrete callback eligibility; §5 outside shallow search | `640bbfa85630d1dd496a3fd1ccb757536385d720` |
| `notes/design/2026-10-02-typed-source-owner-realization.md` | §6 Selected outside-image equation and control preservation | `d0c6c5e2d10cf1b72da0e8613b74641bd25b2caf` |
| `notes/design/2026-10-05-handler-hygiene-public-provenance-notation.md` | Small-step / relational interpretation candidate, lines 89–149; Recommendation, lines 350–366 | `0b249e14d1ecb3bea076549b52af121478552491` |
| `notes/progress/2026-10-06-handler-marked-slot-outward-trace.md` | Smallest supplied source instance; B. Handler processing then same-event forwarding; used as instance locator only | `8f96d65358de362c0e9a800c79d6c4a95067a2cc` |
| `notes/progress/2026-10-05-handler-protection-filter-derivation.md` | Conditional derivation; exact remaining premise; used only to delimit the already conditional query extension | `9663da0c8928a0a567bd8c2a7dbd6e450ebe2853` |

The view-identity falsifier and transport attempt were inspected to exclude
their identity/continuity attacks from this lane. Their results are not used
as premises. This note neither repeats the operational trace nor compares
released and fresh latent targets.

## What the available source introduction actually supplies

The Authoritative callback contract starts with a **supplied** instantiated
formal `F_cb`, static slot template `beta` and original profile `Slots(beta)`.
It preserves those inputs before elaborating a literal body. It independently
synthesizes the literal endpoints and checks `F_lit <: F_cb`; it expressly
does not copy the expected ports into the literal. Dynamic boundary `b` is
introduced when the receiver executes, not during static checking.

The source-role package retains an annotation coordinate
`(boundary site, annotation occurrence, role projection)` and distinguishes
the immediate result computation contract from a returned latent Function's
own call-effect slot. Its §4 explicitly calls the general source judgment a
requirement, not a finished rule set. The core realization takes original
annotation positions and `Flow`/receipt data in its input derivation. Its
checking preservation theorem does not generate another boundary or receipt.

These are useful original anchors. They do not conclude that a particular
dynamic request derives from the row component named `'e`. Event origin is
a source computation/value-flow index; type binders in `nu` are distinct
from runtime identities. An operation admitted by a supplied row is not,
solely for that reason, assigned to one original row component. Approved
effect-row decision 6 explicitly retains the source-evidence derivation gate.

## Maximum identity-path join, with explicit hypotheses

Take a known callback formal with one supplied protected executing effect
position `p_b`. Fix one assignment `nu`, the original `K,D`, an active receiver
`r`, its boundary `b`, and the typed received view `T`. Assume the supplied
formal/profile is admitted and its ordinary use is typed; this is not an
accepted raw-source program assertion. Use identity transport at this same
known position, so `p_b=p` and no result/latent projection is involved.

The existing derivation is:

```text
original protected profile entry chi_source(p_b,b)
and identity Flow gamma: (source,p_b) -> (T,p)
    => chi_T(p,b), retaining its original source witness

Observe(q,T,p,o) and actual Receive(r,slot,T,gamma_receipt)
    => Path(q,r,b,p_b)

owner(h_o)=r and Active(h_o,C_o) and Active(r,C_o)
and Active(b.receiver,C_o)
    => Inc_Co(q,h_o,b,p_b)
    => Protected(q,h_o,C_o).
```

The full proof witness retains the original profile and annotation anchors,
tagged `gamma`, observation occurrence `o`, exact receipt, event/origin,
attachment and `nu,K,D`. The existential `Path` tuple is not substituted for
that witness. This derives ordinary protection incidence without selecting
any public marker or attributing a contribution to `'e`.

Neither identity transport nor known finite shape generates either missing
fact. Identifying the proposed output marker occurrence `s` with the profile
entry `p_b` would be an additional source judgment. Defining
`AttributedTo(q,'e)` by this `Path` would be another additional judgment;
the notation explicitly says a path alone does not establish attribution.
An outer annotation is also not copied to all nested paths by the source rules.

## Conditional lemma for the exact false-guard example

Retain its exact hypotheses: `owner(h_i)=owner(h_o)=r`, both cover the same
operation `E`, the original request `q` is forwarded, the false guard produces
no effects or new receipt/boundary, and `r` remains active. The configurations
being compared differ by expiry of `h_i`; the request's recorded `Path`
evidence and every boundary receiver's activity used in this instance are
unchanged. Additional receiver expiry or target-side computation is outside
this lemma.

For each original profile witness `(b,p_b)`, expand the displayed definition:

```text
Inc_Ci(q,h_i,b,p_b)
 iff Path(q,r,b,p_b) and Active(r,C_i) and Active(b.receiver,C_i)
 iff Path(q,r,b,p_b) and Active(r,C_o) and Active(b.receiver,C_o)
 iff Inc_Co(q,h_o,b,p_b).
```

The first and last equalities discharge the actual candidate's own activity.
They do not assert that the expired `h_i` has a live incidence in `C_o`.
Corresponding full witnesses are retained; this is equality of the
candidate-independent witness conditions at two queries, not identity of
handler activations.

Let `P` be their common existential protection condition and `G` their common
grant condition. The grant formula uses the same owner `r`, `b.receiver`,
profile predicate, operation and assignment `nu`, so it also agrees. Hence

```text
Visible(q,h_i,C_i) = (not P or G)
                  = Visible(q,h_o,C_o) before any release.
```

The instance assumes the first query true so that the false guard actually
runs. It follows that the second query is already true. In the explicit
receiver-local admitting-contract subcase, `G` is true at both candidates.

Conditional on a valid protection-only release selecting some of these
witnesses, grants and activity stay unchanged and remaining protection `P'`
is a subcondition of `P`. If `P` was false it remains false; if `P` was true,
initial visibility forces `G=true`. Thus outer visibility remains true after
such a release as well. This uses only the approved protection-only frame;
it does not construct a selector or prove source adequacy of the filter.

The false-guard example is still a boundary/crossing witness. Equality of its
two outer eligibility outcomes is **not** evidence that the marker was
correctly associated or implemented. For a release-dependent query witness,
one needs different owner/receipt/contract conditions making the next query
protected without a grant before release. That is a future derivation task,
not an asserted admitted counterexample or a reason to alter this instance.

## Precise missing premise and stopping point

Two attempted source routes were inspected:

1. Known callback-context delivery preserves `beta,Slots(beta)` but takes
   the formal/profile as input and does not derive component attribution.
2. Role/core annotation retention preserves original occurrence and typed
   paths but likewise takes the annotation/flow derivation as input. Checking
   preservation cannot introduce the missing attribution or boundary facts.

Both stop at the same premise. The smallest unresolved obligation is a typed
source derivation, for this known immediate computation position, connecting
original marker occurrence `s` and component binder `'e` to its target `(T,p)`,
independently attributing forwarded event `q` to that component, and selecting
the intended full protection witness. The candidate release rule uses these
as antecedents. It does not provide their introduction rules.

A separate source refinement must relate the ordinary outward boundary to
the marked-slot crossing and apply the protection query change before the
next candidate. The literal existing `Protected = exists Inc_C` formula
contains no such selector. The earlier conditional filtering note already
exposes that seam; this note does not turn its assumption into a proof.
No third toy route, guessed label assignment, marked-delimiter transition,
or new carrier is proposed.

## Coverage, checks, resources and next action

Bounded source audit covered the twelve dependency rows above, the original
slot/profile introduction routes and identity-path incidence. A committed
`git grep` for `AttributedTo`, `EmittedFrom`, `ProtectedAt`,
`ReleaseProtection` and related protection names under `notes/design`,
`notes/theory`, `spec` found the named attribution/release judgments only in
the notation candidate's premise rule. This vocabulary search does not prove
that no equivalent rule can exist elsewhere; the negative derivation claim
is restricted to the exact inspected source packages.

Checks performed: bounded read-only `git show`, `git grep`, `git ls-tree`,
`git rev-parse`, `rg`/`nl`/`sed`, and an absent-path lease check before creation.
All dependency hashes are committed baseline blobs; no dependency was changed
by this worker. No test, build, compiler command, checker, random seed or
enumerated range was run. No independent executable oracle or independent
review was used. The equation lemma shares the source candidates' supplied
view, receipt, profile and eligibility assumptions; it does not prove them.

Shortcut failures examined textually: treat preservation as attribution;
equate an effect binder with a dynamic origin; identify a typed route with
a marker occurrence; use unchanged outer visibility as proof of release.
These are not runnable mutation results. Omitted: source grammar/acceptance,
general marker elaboration, inferred shapes, latent continuity, overlap,
deep/multi-shot source correspondence and production query implementation.

Resources: sequential lightweight reads and one note write, no heavyweight
process, no Git mutation or delegation. The new assignment used a bounded
textual investigation; CPU/RSS and exact wall time were not instrumented.

Recommended next action: supply an explicit source introduction judgment for
the marker/component/full-witness association at this immediate known port.
Validate it on a query-discriminating owner/receipt configuration; the exact
same-owner false-guard instance cannot validate release-dependent eligibility.

## Commit packet

- Exact leased path: `notes/progress/2026-10-06-handler-false-guard-attribution-seam.md`.
- Baseline SHA: `45b81a28d614f9f0a4d15c7a861347cb14506566`.
- Dependency hashes changed: none by this worker; exact committed blobs listed above.
- Review status: frozen, unreviewed research; conditional equation lemma and
  bounded unsuccessful attribution-rule derivation. No independent review,
  accepted marked program, source counterexample or theorem closure claimed.
- Checks already run: source/locator audit, baseline and blob identity queries,
  absent-path lease check; no tests/builds/executable experiments.
- Proposed one-line message: `research: isolate false-guard marker attribution and query seam`.
- Shared-record deltas intentionally left for primary/curator: record that the
  exact same-owner example has no release-dependent next-query distinction;
  retain independent marker/component/full-witness introduction and boundary
  refinement as open. No authority, index, task, theory or question files changed.
