# Annotation boundary: upper exposure and seed-applicability audit

Date: 2026-10-08
Assignment baseline: `d3df71936` on `research/simple-sub-intrusion`
Status: research producer; frozen on submission; independent review pending
Claim class: finite conditional constructor/inversion lemma and minimized
owner-input table; no unconditional annotation source theorem
Method: annotation-boundary constructor inversion and separation of premises
Write lease: this file only
Language/implementation authority: none

## 1. Objective and result

Determine which facts the approved annotation boundary can supply to
`SourceUpperUse` and `ProtectedVarAt`, without manufacturing protection from
annotation syntax. The annotation-specific result is a separation: an
original annotation comparison can be inventoried independently of success,
but identifying it as a protected inferred-variable exposure requires two
additional source judgments. The approved `[io]` permission supplies neither
judgment. Its connection to a particular contribution is a further open
constructor obligation.

The sources therefore suffice for the conditional lemma below and the
minimal owner table, not a complete annotated-formal seed constructor.
No supplied-record checker or additional toy experiment is run: it would
assume precisely the applicability and contribution correspondence at issue.

## 2. Exact authority and retained boundaries

- [Directional addendum](../design/2026-10-06-directional-inferred-effect-protection-addendum.md)
  §§1–6 supplies the current user decision and the scoped rule
  `ProtectedVarAt(k,v,sigma,u)`, `SourceUpperUse(u,v,U,sigma)` imply
  `NewProtection(k,u,outEff(U))`. An existing Function lower/provider bound
  receives no new protection from this rule. Its own inherited evidence survives.
- [Local source producer](../progress/2026-10-06-directional-protection-source-generation.md)
  §§1–3,5,8 derives the selected unannotated pattern and the exact join after
  seed-at-exposure justification. It does not derive generic annotation seeds.
- [Inferred call views](../design/2026-10-05-inferred-function-call-views.md)
  §§1.1–5 and the integrated
  [q1/a2 approval](../../questions/2026-10-05-function-call-view-formation/approved-answer.md),
  exact decisions 1–6, distinguish written annotations from public schemes and
  internal views. In the selected annotated example only the specified `io`
  removal is permitted; actual removal and contribution correspondence remain
  open (§4 and §5.3). Absence of annotation is a declaration fact in the
  selected unannotated seed derivation, not metadata of each Name use.
- The retained
  [annotation-boundary q1/d1 approval](../../questions/2026-10-05-source-annotation-boundaries/approved-answer.md),
  exact decisions 1–5, covers binding, argument and expression `as Type`
  boundaries. Each checks its current endpoint directly against its target.
  A successful boundary exports that target and local realization evidence,
  preserving previous evidence and the existing parameter entry role. It
  grants no transitive concrete comparison and no source-free adaptation.
- [Upper-exposure coverage](2026-10-08-directional-source-upper-exposure-coverage.md)
  §§3–7 constructs the direct-Name Call inventory under H1–H4, composes it
  conditionally with H5–H6, and leaves annotation upper checks and their
  applicability outside that inventory. This note addresses only that leaf.

The integration receipts were read as provenance, not as a replacement for
the exact approvals. Callback-literal B, actual callable entry/role, one
original joint `xi=(nu,K,D)`, original scopes and comparison-independent
admission are retained. E/R is not an open choice here.

## 3. The smallest annotation site and its distinct occurrences

Use the already approved example, without claiming parser or compiler support:

```text
apply(f: _ -> [io] _, x) = f x
```

Register the declaration of `f` as `b`, its written annotation boundary as
`a`, the callee Name occurrence as `n`, and the Call occurrence as `c`.
These are four identities. The annotation on `b` remains present when `n`
has no locally written annotation. No unannotated-formal seed can be
obtained by inspecting `n` alone.

When their owning elaborations exist, retain these records separately:

```text
annotation a:  E_a <: T_a                 original boundary comparison
              on success export T_a + local evidence + prior evidence
Call c:       E_n <: U_c                 original complete Call demand
provider l:   L_l <: v_b                 if this lower record is generated
```

`T_a` is the annotation's elaborated target, not its literal written text.
The holes `_` do not by themselves specify an internal Function constructor,
shared root, effect occurrence or complete public scheme. `E_a` is the
current endpoint at the *actual boundary*, not necessarily `v_b`: for
example, an incoming provider comparison may have an already constructed
Function endpoint. The scope and entry role of that actual boundary must
come from its source derivation.

`E_n` likewise needs its actual lookup/export correspondence. It cannot be
identified with an earlier inferred variable by printed type equality.
Even when `T_a` and `U_c` eventually have equal denotations, `a` and `c`
remain different checking occurrences. A declared Function signature is
also not a provider lower edge merely because it describes a callable.
Orientation and source origin must be retained from their constructors.

Deleting the annotation removes the permission issue; deleting the Call
removes the annotation-to-use issue. Thus one annotated formal and one
governed Call is the minimal site for the combined boundary. This is a
minimal missing-constructor site, not a counterexample to accepted semantics.

## 4. Finite conditional annotation constructor and inverse

Let `B` be a finite set of original annotation **boundary derivations**.
These are not a supplied set of protected upper exposures. The exact
conditional premises are:

```text
A1  Each actual boundary a has its original source identity, binder/contract
    correspondence, scope, entry role, current endpoint E_a and target T_a.
A2  Its source elaboration emits one original direct checking occurrence
    u_a: E_a <: T_a, before comparison success is known. Replayed or
    structural child obligations retain their origin and are not counted
    as additional original annotation boundaries.
A3  The annotation-normalization derivation supplies the internal target,
    including a designated output-effect OCCURRENCE when T_a is a complete
    Function. No shape is obtained from successful Q or from the surface
    arrow alone. All dependent constraints remain in the original xi.
A4  Source identities and the dependent current/target fields survive;
    equal endpoint denotations never merge their originating occurrences.
```

A1–A4 are explicit inputs of this bounded result. The approved boundary
direction motivates them, but does not complete raw annotation normalization
or prove every source tree meets them. In particular A2's symbolic emission
before success is a construction premise, not a consequence of the rule
about what a successful boundary exports.

Traverse the actual derivation occurrences once. At each annotation
boundary copy `(a,b,scope,role,E_a,u_a,T_a,originalConstraints)` from its
constructor. If its actual current endpoint is still an inferred variable
`v` and its normalized target is complete Function `U`, retain the tagged
record:

```text
C_a = (annotation,a,b,v,scope,u_a,U,outEff(U),originalConstraints)
```

Keep all other boundary records in the unfiltered inventory. The tag says
**candidate variable-to-Function annotation check**. It does not assert
`SourceUpperUse`, protection, membership or permission realization.

**Lemma AB (finite conditional inventory).** Under A1–A4 the filtered
inventory is in bijection with the original annotation boundary occurrences
whose actual current endpoint is an inferred variable and whose normalized
target is a complete Function. Inversion recovers that same boundary,
orientation, endpoints, scope and designated output occurrence.

**Proof.** Each constructor occurrence emits its one original record by A2;
the filter tests the actual fields supplied by A1 and A3. A4 makes distinct
boundary occurrence keys distinct despite endpoint aliases. Projecting a
retained record to `a` recovers its unique creating occurrence. Reapplying
the constructor at that occurrence recovers all dependent fields. Every
qualifying occurrence passes the filter and every retained record qualifies.
Replay, Call and provider/lower records have different origin tags and
cannot be additional images. This proves both directions and uniqueness.
No comparison answer is read. QED.

This is an inversion of a supplied boundary derivation class. It neither
reconstructs annotation elaboration from raw text nor classifies every
direct annotation comparison as the user's original source upper-use rule.

For actual directional conclusions two additional premises are necessary:

```text
A5  The owning annotation inference judgment certifies that u_a is an
    original SourceUpperUse(u_a,v,U,sigma), through its original scope route.
A6  An authentic seed derivation proves ProtectedVarAt(k,v,sigma,u_a),
    with the relevant variable stage and logical dependency order.
```

**Conditional composition.** On exactly the records with A5–A6, joining the
same-root/same-scope/same-exposure witnesses emits exactly
`(k,u_a,outEff(U))` conclusions of Dir-Protect for these annotation exposures.
Soundness applies that rule to the two certificates. For completeness,
invert its annotation exposure by AB and recover the same seed-stage
certificate by A6. Provider lower records match no such exposure head.

This last composition shares the selected Dir-Protect rule with the local
producer. It adds no proof that A5 or A6 follows from annotation syntax;
those are precisely the remaining constructor heads. No late-seed replay,
arbitrary SCC policy or target-to-variable back propagation follows.

## 5. Permission does not discharge either protection premise

The accepted statement for this example is that its specified `io`
contribution may be removed. It does not state that this annotation seeds a
protected inferred variable, that every annotation comparison is a
directional exposure, or that the Call's output is unconditionally exposed
to removal. It also does not say an annotated declaration loses unrelated
or inherited protection.

The useful separation is:

```text
written a contains [io]                 accepted scoped permission direction
owner certifies current variable upper  candidate record + A5
source seed applies at that upper       A6
owner relates permission to contribution and typed scope/use
                                        missing annotation correspondence
actual operation realizes permitted removal
                                        separate realization obligation
```

The fourth item can eventually relate an annotation's approved permission
to an already justified directional incidence without generating that
incidence from the annotation. It must identify the original contribution,
annotation position, contract and scope, their typed correspondence at the
governed use, and the same original joint assignment. Type equality,
shared `io` spelling, or a common normalized effect endpoint cannot replace
that certificate. Permission alone creates neither a receiver nor a receipt,
grant from an arbitrary handler, request observation or operational removal.

No formula for that correspondence or for applying the permission to a
protection profile is selected here. In particular, subtracting `io` from a
row, deleting every seed on the annotated binder, or copying protection
backward to an incoming provider would add unsupported rules.

## 6. Minimized owner-input table and next falsifier

| Minimal boundary input | Available from selected sources | Exact missing head or certificate | Owner |
| --- | --- | --- | --- |
| One `f: _ -> [io] _` declaration | Annotation identity/presence and the scoped permission decision | Normalized target with actual holes, role, scope and occurrence paths (A1,A3) | Annotation elaboration |
| That annotation's direct boundary | Current-endpoint/target comparison direction and successful target export | Which actual current endpoint is checked, original symbolic emission (A2), and whether it is an inferred variable | Annotation/parameter boundary construction |
| A qualifying variable-to-Function annotation check | AB inventories it under A1–A4 | Classification as original `SourceUpperUse`, rather than a direct check of another class (A5) | Source upper-use inference rule |
| Same annotated root at that exposure | Annotation presence is retained; no absence premise is available | Authentic seed origin and stage applicability, if any (A6); no seed is demanded by this note | Protection/annotation inference constructor |
| One `f x` governed use | Distinct ordinary Call demand and resolved declaration identity | Export/lookup correspondence to its actual callee endpoint; applicability there if claimed | Typed Name/Call and evidence transport |
| Specified `io` at that use | Permission for the selected contribution; unrelated effects are excluded | Annotation-to-contribution and scope/use correspondence, followed separately by realized removal | Annotation evidence and typed realization |
| One incoming provider lower | Preserve origin, orientation, actual entry and inherited evidence | No backward protection follows from the formal's seed; independent provider facts need their own source proof | Provider construction |

The precise blocker is a missing **owner-generated annotation certificate**,
not an insufficient enumeration range. It must decide its actual current
endpoint and target, supply A5/A6 when justified, and relate the annotation
permission to its governed contribution without deriving one from the other.
Retaining this evidence at construction follows the existing proof-obligation
economy policy; the note proposes no new runtime carrier or language clause.

**Next falsifier:** inspect the actual annotation/parameter source judgment
for the single approved example and request its original heads and dependency
order. If it exports a completed target at `f`'s body use without an
inferred-variable upper exposure or an applicable seed, the attempted A5/A6
route fails for that boundary. If its `io` permission has no typed contribution
correspondence, the permission-to-incidence bridge remains open even when
A5/A6 hold. An incoming provider comparison `L <: T_a` is a discriminating
failure of the shortcut “every annotated formal creates `v <: T_a`.” These
are conditional derivation tests, not executed source counterexamples.

## 7. Independence, checks, resources and omissions

There is no executable oracle. AB depends explicitly on A1–A4; composition
shares Dir-Protect and A5–A6 with its rule-relative conclusion. Neither
validates those source premises independently. An executable accepting the
same boundary and seed certificates would check consistency after the open
heads, so another such probe would leave the blocker untouched.

No random seeds, finite numeric ranges, exhaustive search or executed mutants
are claimed. The proof applies to any finite supplied derivation inventory
meeting A1–A4. Named shortcuts discriminated by the source audit are annotation
syntax as a seed, Name spelling as binder annotation absence, every boundary
as inferred-variable exposure, equal endpoints as shared occurrences, permission
as realized removal, and formal upper protection as provider lower protection.

Checks: full requested rule reads; exact governing-section and approval reads;
integration-receipt inspection; SHA-256 reads of the nine direct dependencies;
narrow final link/whitespace/dependency integrity check reported at submission.
No compiler edit, tests, builds, execution probe, Git command, temporary
output file, child process wave or subagent was used. One small shell/Python
command at a time; no numeric CPU/RAM/wall budget was supplied. Aggregate CPU,
peak RSS and wall time are unmeasured; no performance claim is made.

Unverified: raw annotation normalization; actual production boundary and
constraint emission; universal seed eligibility or applicability; generic
annotation-to-profile rules; typed contribution/event/receiver realization;
recursive inference/generalization; public-scheme completeness, principality
and production conformance. No source restriction or gate closure follows.

## 8. Dependency snapshot

The primary pinned `d3df71936` and confirmed the governing dependencies were
unchanged while the branch advanced. At the last primary notification HEAD
was `e3aa8939c274c178efd495cad20132f5c1d46b2a`, adding the reviewed upper-use
inventory note. The exact frozen inventory bytes are pinned below as a
dependency in addition to the assignment baseline. This producer performed
no Git read or mutation; baseline/current equality is the primary's report,
not an independently repeated producer check. Full expansion of the assigned
short baseline SHA and final committed-byte validation remain primary duties.

| Direct input | Frozen SHA-256 |
| --- | --- |
| `notes/design/2026-10-06-directional-inferred-effect-protection-addendum.md` | `6b1779933499b360627fa5852c292ce97bda9830d146863b1b7ef440706054a7` |
| `notes/progress/2026-10-06-directional-protection-source-generation.md` | `3702eb2ea5108eba1adc8ab7a557542abb9993cee09f70b738e2999a05a2d185` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/theory/2026-10-08-directional-source-upper-exposure-coverage.md` | `ec48183efd1914c1a2f6bf52a9ed56ad58b1043bd9c03c215679ee9eeb030111` |
| `questions/2026-10-05-function-call-view-formation/question.md` | `f3915c64daeccf466115b74a895c2c937f2ec10c1872fc91ff220ed2b0cf7c5f` |
| `questions/2026-10-05-function-call-view-formation/approved-answer.md` | `1071cf1c2d9abce2ffbc829cec7757d2b2f52849174c04751bd63aeefa520536` |
| `questions/2026-10-05-function-call-view-formation/receipt.md` | `6dcf408143c7eb48260d8c4df9ef73834da8d28a7f4ec9744ab381e67414cee0` |
| `questions/2026-10-05-source-annotation-boundaries/approved-answer.md` | `e1e2ff77b181fe42edd404ee0d69cfc6d3bb0fbc99ba7e7f092710025d11fb12` |
| `questions/2026-10-05-source-annotation-boundaries/receipt.md` | `7cf351cd6abf654f70982c7269d7286b50faaca69461db8d88b1e22da314b4a9` |

## Commit packet

- Exact leased path: `notes/theory/2026-10-08-annotation-upper-exposure-constructor.md`.
- Assignment baseline SHA: `d3df71936` (primary-supplied pinned identifier).
- Changed dependency hashes: none during this lane's snapshot/check interval;
  frozen direct-input hashes above. The inventory note's later reviewed
  checkpoint is explicitly a dependency; pinned-commit comparison is primary-owned.
- Review status: frozen producer research; no independent review of this note;
  conditional lemma and open source heads remain explicit.
- Checks already run: requested rules/sections and integrated approvals,
  dependency hashes, narrow final document integrity and dependency recheck;
  no tests/builds/executable experiments or Git use.
- Proposed checkpoint message: `research: isolate annotation upper-exposure premises`.
- Shared-record deltas intentionally left for primary/curator: record AB's
  conditional annotation inventory inverse; keep A5/A6 and scoped contribution
  correspondence open; add no semantic authority, gate closure or implementation
  status promotion. No shared path was edited.
- Recommended next action: inspect the owning annotation/parameter judgment
  for the one selected annotated example and obtain its actual constructor
  heads, scope/use correspondence and seed dependency order.
