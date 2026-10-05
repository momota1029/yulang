# Recursive origin discharge: bounded source-stage falsification

Date: 2026-10-06
Status: unreviewed research-only bounded characterization; frozen on submission
Method: adversarial derivation table, not constructive source-rule design
Baseline: `ba35b1b1341fe70f4445675e0d4c5d664c7c4875`
Branch: `research/simple-sub-intrusion`
Exclusive lease: this file only; no implementation authority

## Objective and result

Test whether the reviewed origin/guard minimality result already has a
source-level counterexample or an unconditional discriminator, using the
source stages before and during the inherited incoming route. No such witness
is established in this bounded audit. The actual trace identifies where a
future source certificate would discriminate; it does not supply that
certificate. This result neither proves that no counterexample exists nor
independently certifies the reviewed notes.

The [minimality note](2026-10-06-recursive-origin-guard-minimality.md) claims
relative local minimality of a hypothetical first-obligation rejection D,
not source rejection or a full-calculus countermodel. None of the examined
source stages contradicts that limited claim. The
[closure synthesis](2026-10-06-recursive-origin-guard-closure-review.md)
already distinguishes an ordinary inference witness, a rigid binder with
declared bounds, and a new restriction of that binder. The bounded table
below tests whether any preceding stage forces one of those roles.

## Governing sections and accepted decisions

- [Charter](../design/2026-09-29-scc-intrusion-redesign-charter.md) §§1–2:
  F5 scheme shape and extrusion are historical comparison material;
  successor soundness/principality precede final acceptance compatibility.
- Charter §§19–20: generic arms check uniformly under declared interfaces
  and bounds; request opening retains the original joint witness and
  dependent correspondence; caller-private specialization is not an arm
  assumption; inference existentials and hidden request binders differ.
- Charter §21: the ordinary parameters x/y receive fresh inferred value
  endpoints. This fixes their role without providing a §22 origin judgment.
- Charter §§22–23: introduced-existential checks re-enter every actual
  derived comparison; levels belong to variables; exact variable/extrusion
  coverage and preservation remain open. No constructor-level convention,
  identity exemption or general replay exemption is selected.
- [Result synthesis](../design/2026-10-02-source-result-synthesis-choice.md)
  §§1,3–5, especially §4: Name copies a supplied interface; Result forwards
  known computation interfaces or adds the specified pure value wrapper;
  joint profiles and K,D are transported; recursive checking remains open.
- [Call views](../design/2026-10-05-inferred-function-call-views.md)
  §§1.1,2,5: public schemes, source contracts and internal evidence differ;
  generalization/use preserves the shared source relationship, identity,
  lexical scope and one joint assignment. Exact construction is a proof gate.
- [One inequality](../design/2026-10-03-concrete-compatibility-boundary.md)
  §1: oriented variable bounds and replay belong to the same inequality;
  concrete successes cannot be assumed to form a transitive preorder.

The design index was used as a locator. `tasks/current.md:510–582` was read
for gate continuity, not as a replacement semantic source. No pending question
bundle or candidate recursive calculus is adopted as authority.

## Finite envelope and inherited observation

The bounded source has exactly these three items and no use of h:

```text
my f x = g
my g y = f
my h = f
```

The inherited successful-owner observation ends before h generalization or
publication. All current rows have level one. With distinct occurrence row c,
alias root R_h and fresh recursive representation z, the value inventory is:

```text
B(z) = PureFun(Top,PureFun(Top,z))
prefix: c <: R_h
q1: B(z) <: z
q2: z    <: Top
q3: B(z) <: c
q4: B(z) <: R_h       // replay through the prefix
```

This is documentary production evidence inherited from the reviewed notes;
no compiler owner was re-executed or freshly audited here. In particular,
there is no supplied z/c or z/z variable task, Function/Function comparison,
or request/arm opening. The source instance is minimal only relative to this
inherited one-alias route: deleting h deletes the incoming route, and deleting
either recursive definition abandons the fixed two-member envelope. No global
source-program minimization is claimed.

## Bounded derivation table

“Open” below means a missing premise, never permission to accept.

| Stage | What the selected clause gives | Candidate shortcut tested | Exact surviving premise / verdict |
|---|---|---|---|
| Parameter introduction | x/y have fresh inferred value endpoints and fixed Value roles (§21). | Fresh allocation itself makes a §22 existential, or inferred endpoints must be ordinary. | Neither implication is supplied; origin event, introduction level and later row correspondence are open. |
| Recursive SCC environment | Given Gamma_S(f)=I_f and Gamma_S(g)=I_g, Name synthesizes those interfaces. | Body copying constructs Gamma_S, or a copy cycle grounds its own origin. | Recursive formation and its grounded ledger are open. Conservation conditional on supplied Gamma does not solve recursive binding. |
| Lambda result synthesis | Supplied I_g/I_f produce Fun(P_x,Result(I_g)) / Fun(P_y,Result(I_f)). | Pure source or unused parameters erase all origins. | Known interfaces and existing correspondence are preserved. Purity/unusedness supplies no negative origin certificate. |
| Generalized member formation | Joint relationships, static identity and lexical scope must survive. | An R ordinal proves an existential source binder, or projection equality proves binder identity. | The origin-bearing generalized interface and its R realization are open. Retired F5 storage is not a source judgment. |
| Member use and alias Name | A supplied MemberUse interface is copied without another Name introduction. | The Name rule proves that the use allocator z or occurrence c is ordinary. | Supply/transport and occurrence/root/recursive row realization are open; Name conservation covers only its supplied interface. |
| q1 restoration and extrusion | The selected discipline checks every comparison and any actually derived variable/extrusion consequence. | A Function-headed lower bound is ground narrowing; equal current levels produce z/z; restored syntax proves a declared bound. | B contains z, no z/z task is supplied, and restored syntax does not identify source assumptions. q1 permission is open. |
| q2 terminal | q2 is an actual comparison requiring its source/guard certificate. | Empty variable support or legacy Top success proves a selected exemption. | Terminal permission/non-refinement is open; no level is assigned to Top. |
| q3 and q4 replay | Actual replay re-enters the guard with the same retained witness correspondence. | Equal target levels let q4 inherit q3's result automatically, or nested Ex proves an escape violation. | Origin-relative insertion/transport and a justified reusable certificate are open. §20 adds no general escape ban. |

Every attempted shortcut either lacks the source antecedent or replaces it
with a representation fact. Thus the table does not yield a source acceptance
or rejection derivation for the complete three-item program.

One useful boundary check concerns the prefix. Conditional on its source
realization as a §22-governed comparison, an admitted level-one c <: R_h
rules out Ex(c,l) and Ex(R_h,l) for l >= 1. It does not establish that either
row has no introduced-existential origin at any level. The minimality note
explicitly fixes c/R_h ordinary for its local paired perturbation; that fixed
assumption is stronger than this conditional prefix consequence. It does not
purport to derive arbitrary source origins. Replacing the fixed assumption
with “prefix admitted, therefore all rows ordinary” would be an invalid
promotion, rather than a counterexample to the stated result.

## What would actually discriminate q1

The hypothetical clause D and support rule K are not used as source premises
in this audit. The existing uniformity obligation supplies only the following
conditional rejection criterion:

1. A complete source derivation certifies that z denotes a genuinely opened
   rigid binder, retaining the original declared domain and fixed captures.
2. The source correspondence identifies q1 as a new demand, rather than an
   assumption already included in that declared domain.
3. An admitted original instance makes the source demand represented by q1
   false.

Then uniform checking fails at that unchanged instance; narrowing the domain
to successful instances cannot repair the proof. This is the already reviewed
conditional uniformity argument, retained here to identify the exact
falsification certificate. It is not another constructed Int/Top probe or a
new source witness. None of premises 1–3 is established for this component.

For an originally declared bound, premise 2 fails; the same argument cannot
reject restoration. That observation does not prove that §22/23 permits the
actual solver insertion. A separate guard/realization theorem is still needed.
For an ordinary inference witness, premise 1 fails. An Ex flag by itself does
not establish the §20 binder mode, declared domain or demand status.

A genuine counterexample to the claimed local minimality would need either a
smaller discriminator within the same fixed production envelope or a selected
source derivation that makes D's assumed distinction inconsistent in that
envelope. Merely choosing one missing source role proves neither. A complete
source counterexample to a future implementation additionally needs a source
permission verdict and a contradictory implementation verdict on the same
original joint assignment and admitted input.

## Independence, coverage and stopping point

There is no executable oracle. The selected source clauses ground the table;
the trace and reviewed claims are shared documentary dependencies. Their
reviews are historical inputs, not this producer's independent certification.
An implementation/reference checker sharing assumed formation, origin or
transition rules would test consistency under those assumptions. It would not
prove the source supplier or the declared-domain premises above.

Coverage is eight named stages, one three-item source and its inherited prefix
plus four comparisons. Finite additional unused aliases are covered only by
the prior conditional copying/trace results, not a new enumeration. No seeds,
numeric ranges, executed mutations or automated shrinking exist. The table's
shortcut substitutions are logical stress cases, not a mutation campaign.
Two earlier local completion methods D/K both leave source supply untouched;
this lane stops at that exact premise instead of producing another decoration
checker. Missing source introduction/formation is not a discovered semantic
counterexample.

Failure conditions: a governing clause changes; a selected source derivation
already provides the missing supply/realization certificate; the inherited
route inventory changes; declared assumptions are confused with new demands;
current levels are substituted for introduction levels; or retired F5 and a
transitive candidate carrier are silently imported as successor authority.

Unverified: recursive source formation, complete generalization/use judgments,
origin-complete row realization, §23 coverage, q2 permission, principality,
source admission, diagnostics, alias generalization/publication, arbitrary
callers, applications, annotations, effects and lifecycle. Searches were
limited to the named sources and locators; no repository-wide absence claim.

## Checks, resource use and frozen dependencies

Read the three required rules in full; inspected the named authority sections
with cat/rg/sed; checked initial HEAD/branch; scoped
`git diff ba35b1b1341fe70f4445675e0d4c5d664c7c4875 -- <ten dependencies>`
was empty; captured SHA-256; confirmed the lease path was absent. Final
verification consists of scoped dependency equality, leased-note integrity
and whitespace inspection. Truncated batched used passages were reread
narrowly. A locator query for two guessed candidate filenames failed; those
nonexistent paths contribute no premise.

Zero tests, probes, builds, formatters, children, interactive questions, Git
mutations or shared-record writes. At most four lightweight read command
processes were concurrent; heavy-process count is zero. CPU time, peak RSS
and total wall time were not instrumented. The assignment supplied no numeric
CPU/RAM/wall-time cap. Only this leased note was written.

SHA-256, all ten checked unchanged against the pinned baseline:

```text
547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed  charter
71326de0897159343797d6aec083860ee0f57a1bc04f9c4ae77e579ea0ba5992  source-result-synthesis-choice
4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1  inferred-function-call-views
5b0b4321d8644f88a7a946aff31b6b3190d37a9076ac698fa91fdfeef1470f16  concrete-compatibility-boundary
cb9e998ebf5292c18ca4a77cea4e47e6c6aa2abef31b2d59d03b828f0fcf37fb  recursive-origin-guard-minimality
816f1bb3d563e6024e7770c806bf03c7c6eb1bd58cdb7e9378bb5ee2a5330f38  recursive-origin-guard-closure-review
4ce4ce98c4c5f2091c820d90f95c0855addba2564f79d53e59cc7d0cb2b65a31  recursive-name-origin-authority-closure
a3c9fe8c36d20df649a52c7750d0bf581e0f480f94776e2849bb4a1f1abba8d9  section22-guard-authority-closure
d9911dc127a684c9a2a471d02e2513958de428cd1de5589d88bc3fb9ac85fc53  generalized-alias-source-bridge
8963987e193efe9c4778a457a163df0076391b4056734def0087164b4795e300  universal-scheme-use-origin-audit
```

Recommended next action: obtain one provenance-bearing recursive
Form/Generalize/MemberUse derivation and its q1 assumption-versus-demand
realization; use its original declared domain as the next falsification
oracle. Further D/K variants cannot supply that derivation.

## Commit packet

- Exact leased path: `notes/progress/2026-10-06-recursive-origin-discharge-falsification.md`.
- Baseline SHA: `ba35b1b1341fe70f4445675e0d4c5d664c7c4875`.
- Changed dependency hashes: none at final check; fingerprints above.
- Claim/review status: unreviewed research-only bounded characterization and
  retained conditional rejection criterion; no source counterexample,
  independent certification, closed gate or implementation authority.
- Checks already run: authority/source-stage inspection, initial branch/HEAD,
  scoped dependency equality, SHA-256, target absence and final scoped
  whitespace/integrity inspection; no executable semantic checks.
- Proposed one-line research-checkpoint commit message:
  `research: bound recursive-origin discharge falsification`.
- Shared-record deltas intentionally left for the primary/curator: record no
  source counterexample found in this bounded table; retain the missing
  provenance-bearing supply and q1 role/domain premises; retain the prefix's
  conditional introduction-level restriction without promoting it to global
  ordinary classification. No shared path edited.

Writes stop at frozen submission; any repair requires primary handoff.
