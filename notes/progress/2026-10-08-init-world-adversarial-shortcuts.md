# INIT_WORLD / INIT_VALID: adversarial shortcut analysis

Date: 2026-10-08
Pinned baseline: `8a3f7ecbc0aef25fd448593fea1cf8fd5891ddf4`
Status: frozen research-only artifact; compiler-referee reviewed, one minor precision finding repaired and primary delta-checked
Claim class: partial-schema non-entailment and conditional logical derivation
Implementation / semantic authority: none
Exclusive lease: this note only

## 1. Objective, method and authority boundary

Test four proposed shortcuts: delete imports/world from the original tuple,
clear the initial context, infer admission from silent control, and define
admission using an extant source solution or checked-hole membership. The
method is a logical audit of the supplied conjunction and quantifiers. It is
distinct from constructing world clauses or realizing a source prefix.

The governing [DAG](../theory/successor-proof-obligations.md) nodes are
INIT_WORLD, INIT_VALID and SEM_JOINT. INIT_WORLD still owes the independent
filling-independent EnvStore/JointWF clauses, including imported roots and
hole-dependent aliases. SEM_JOINT still owes one justified simultaneous
interpretation. INIT_VALID then constructs an actual base in that meaning;
it does not define admission by solution existence. These nodes are research
navigation, not semantic authority.

The [source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
§§2.1–3,6–9 retain independently interpreted primitive relations, same-tuple
conjunction, complete descriptor typing and four independent admission
classes. Their mathematical results are conditional; concrete clauses remain
Draft. The [typed core](../design/2026-10-02-typed-computation-core-elaboration.md)
§§6,9 preserves actual entry, the complete carrier, current configuration,
receipt, ordered suffix and future histories. Its body/result skeleton is
not a complete incoming-carrier contract.

The committed [inlet decision](../../questions/2026-10-05-production-function-inlet-context-domain/approved-answer.md),
q1/d1, fixes all independently compatible punctured contexts at the original
`xi=(nu,K,D)`, including other-program and future uses. The direct callable
and entire carrier are holes; other environment values remain independently
valid. Checked membership and Q cannot define this domain. Option 2 permits
independently licensed providers without source bodies. The integrated
[receipt](../../questions/2026-10-05-production-function-inlet-context-domain/receipt.md)
records commit `28dddc75f` and the still-open environment characterization.
This note uses the primary's accepted decision; it does not revalidate or
modify a question bundle.

The [initial-admission construction](2026-10-06-independent-initial-admission-construction.md)
§§1–4 already constructs a bounded source/control prefix and isolates the
profile/inlet cuts. The [profile construction](2026-10-06-source-profile-admission-construction.md)
§§1,3–8 expands Init and explicitly rejects silent-run completeness. The
[initial-context construction](2026-10-06-initial-context-source-construction.md)
§§4.1,5,8 separates open source references from independent import/world
leaves. Concrete compatibility §8's rigid-hole/open-graph discussion preserves
this separation; its captured-cell example remains conditional.

Keep the original source

```text
my apply f = { my step x = f x; step }
```

and its original graph, roots, beta/profile, scope tree, xi and whole X. No
lower-provider backflow, replacement source, invented heap cell or altered
meaning of protection is used. Oracle is historical evidence only.

## 2. Exact partial premise and one minimal valuation

At that same original X, abbreviate the profile note §5's supplied factors:

```text
G(X) = OpenSourceGraph(X)
P(X) = OriginalProfilePositions(X)
A(X) = ArgumentCodeContract(X)
W(X) = JointImportsAndCurrentWorld(X)
S(X) = OriginalDistinguishedPortAndOrderedSuffix(X)

Init(X) <=> G(X) & P(X) & A(X) & W(X) & S(X).              (F)
```

These abbreviations retain every original operand and binder. They are not
definitions of the missing complete primitive meanings. In particular,
declaring G true below does not prove complete local source typing.

Let T_partial contain only (F), ordinary Boolean logic, and the fact that a
control observation can be described as outwardly silent. T_partial omits
the exhaustive descriptor/world/import clauses and their SEM_JOINT model;
it omits constructor typing and any theorem connecting this actual X to W.
It does not assert that all supplied semantic clauses have been satisfied.

The following is a **partial candidate valuation**, not a sorted complete
counterinterpretation of Yulang:

| Factor at the one X | Value |
| --- | --- |
| G, P, A, S | true |
| W | false |
| Silent control observation | true |
| Init, by (F) | false |

This satisfies the displayed partial formula (F). Hence

```text
T_partial does not entail
  (G(X) & P(X) & A(X) & S(X) & Silent(X)) => Init(X).
```

This logical non-entailment is established for T_partial. It is deliberately
weaker than claiming the antecedent is realized by an independently typed
source tuple. Completing primitive definitions could rule out this valuation;
that is exactly the missing premise which the shortcuts do not supply.

One false Boolean factor suffices, with no distinct world, new scope,
different assignment, request or history extension. Removing W removes the
failure; changing W to true makes Init true under (F). Minimality is relative
only to these factors. No smallest source witness or semantic-world model is
claimed. In particular, this is not an inadmissible import smuggled into an
admitted source program, and not two competing complete language meanings.

For finer bookkeeping one may *candidate-decompose* W into independent
import-descriptor, environment and joint-world checks I,E,J. Such a
decomposition needs its own definition theorem; this note does not assume
that W is already exactly `I & E & J`. Even where that decomposition is
supplied, an empty import set can discharge only its universal import check;
E and J remain. No arbitrary invalid receiver record is asserted to arise
from the fixed source prefix.

## 3. Discriminating the four mutations

### Delete imports/world from X

Keep X itself fixed. The actual logical mutation is to remove W from (F),
obtaining `Init_drop(X)=G(X)&P(X)&A(X)&S(X)`. In the partial valuation,
Init_drop is true and Init is false. This demonstrates loss of the supplied
world obligation; it does not demonstrate an admitted-source failure.

Projecting a tuple also requires a separate issue to be resolved. For a
retained clause R, sound evaluation through projection pi requires a
well-defined R_bar with `R(X) <=> R_bar(pi(X))` on the relevant original
domain. If a world-sensitive clause is not constant on a projection fiber,
such an R_bar cannot exist: equal projected operands would need different
truth values. This is a conditional elementary proof, not an exhibited
pair of admissible Yulang worlds. No fiber constancy, legal joint hiding or
independent admission certificate was supplied for deleting this coordinate.
The source contracts §3.4 require those certificates for joint hiding.

### Empty-world / context-clearing

For X's original world w, replacing it by an empty world w_empty evaluates
the predicates at a different tuple. The necessary theorem would preserve
every original predicate and the actual hole references/aliases, scopes,
xi, receipts and suffix under that map. Empty-looking syntax supplies no
such theorem. This lane does not perform the replacement.

If the actual original import list is empty, retain it as an original fact.
An empty universal import check alone cannot discharge the remaining current
environment, activation and shared-dependency clauses. The bounded no-import
prefix from the prior construction has exactly this limitation. Deleting the
open captures also removes the fixed source's captured f and future step
interaction, rather than proving it independently valid. Clearing a saved
suffix similarly changes the complete challenge.

### No outward events equals Init / EnvStore

The partial valuation distinguishes Silent from W and Init. The prior
construction supplies an actual source/control identity trace; it explicitly
does not establish its complete independent profile/inlet/world admission.
This note does not rerun or inflate that trace into an admission counterexample.

Independently, source contracts §§3.2,6 and typed core §§6,9 preserve inert
returned providers, receipt and current state even when there are no outward
requests. Empty effect support also does not imply return or a particular
entry mode. These are retained obligations invisible to the proposed support
test. They do not prove a particular internally handled carrier belongs to
the original inlet; that would again require independent admission.

### Extant source solution / checked-hole membership defines admission

Suppose a genuinely complete J_S at the **same original X** already contains
Init, EnvStore and JointWF as conjuncts. Extracting those facts is valid.
It assumes an existing satisfying witness of precisely the independent
obligations INIT_VALID must construct. It is not a method for deriving that
base without the witness. If those conjuncts are absent, their extraction
needs a separate independently justified entailment theorem. The partial
valuation demonstrates only that the weaker displayed factor theory
`T_partial` supplies no such entailment; it does not refute a stronger
complete `J_S` that might derive `Init` by other clauses.

Defining `Admit_by_solution(S) := exists original-scope witnesses. J_S`
makes `Admit_by_solution(S) => exists witnesses. J_S` tautological. It does
not prove equality with the independently selected admission domain. A
solution in a separately selected world cannot be substituted for the
actual original world; this note performs no such witness change. Even at
one X, a full solution is a stronger premise, not evidence that weaker
control or schema generation constructs it.

The hole rule licenses hypothetical open typing and explicitly emits no
`DescMem(T_checked,actual_f)`. Adding that membership as an admission
condition asks for part of the membership under test before admitting the
challenge. A different candidate filling's membership then changes the
putatively filling-independent domain. Proving this extra premise redundant
would require an independent theorem on the original domain. None is
supplied by a silent trace or existing solution. No actual accepted/rejected
pair of source fillings is claimed here.

## 4. Independence, coverage, failure conditions and next action

The reference is the inspected relational factors, source constructors and
accepted domain quantifiers. No numerical oracle or executable checker was
used. The valuation and deductions share Boolean logic and the supplied
factor schema, but deliberately do not share a completed world definition.
A checker hardcoding (F) and this table would verify only this rule-relative
non-entailment. It would not prove the missing source rules or SEM_JOINT.

Coverage is four named mutations at one original tuple and one independent
world factor. There are no seeds, ranges, sampling, enumerated histories or
search shards. No second model with the same untouched premise is proposed.
The precise remaining premise is the complete independent world/import and
descriptor/admission clauses, plus a justified joint interpretation and an
actual base constructor at this original X.

The result fails as a source-level falsification if T_partial is presented
as exhaustive, G/P/A/S are presented as already semantically realized, the
false W is presented as an admissible source world, or any witness is moved
to a different X/xi/scope. The projection argument needs an actual differing
fiber to become a source-level counterexample; none was constructed.

Unverified: complete ordinary descriptor and carrier meanings, admission
clause exhaustiveness, SEM_JOINT existence/uniqueness, actual Init validity,
recursive captures, State/reference transitions, arbitrary imports,
response/resume/future-use coverage, production acceptance and both
production inclusions. No undecidability or user-choice blocker follows.

Recommended next action: obtain the independent INIT_WORLD clause inventory
from the constructive lane, then have the primary check whether its actual
base rule supplies W at the unchanged original X without checked-hole
membership. Expand this lane only when that clause snapshot is fixed; then
a sorted counterinterpretation or source realization can discriminate it.

## 5. Commands, resources and commit packet

Checks: targeted source/section reads; factor truth-value and quantifier
audit; direct-dependency SHA-256; note-local whitespace and relative-link
inspection. Read-only `git show BASE:path` was used to obtain pinned source
contents. This deviated from the packet's literal no-Git-command budget;
there was no Git mutation. Some oversized combined reads were truncated;
the clauses used in this note were subsequently read in bounded slices.
No complete repository search was performed.

Local process budget: lightweight reads and one small hashing process,
serial after initial rule reads. The initial rule-read wave used three
concurrent lightweight processes, exceeding the assigned serial-process
limit for that wave; no computation/build concurrency occurred afterward.
No tests, builds, solver, Oracle, child agent, background calculation or
shared-file write. Wall time was not measured from startup; elapsed wall time
and CPU/RAM peaks are unknown. No long-running calculation was launched.
There is no independent review of this artifact.

The following SHA-256 values freeze the live dependency snapshot inspected
at artifact creation. Core/source-contract/compatibility and source-profile/
initial-context values also match their previously recorded dependency
hashes. Equality of every live dependency to the assigned commit remains a
primary integration check; it is not asserted from these live hashes alone.

| Dependency | SHA-256 |
| --- | --- |
| `notes/theory/successor-proof-obligations.md` | `1b4d27e80fb8437fc78adde55853cdbd7b5cc0a9e819c7eb3474dc83a09aeeb3` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-10-03-concrete-compatibility-boundary.md` | `5b0b4321d8644f88a7a946aff31b6b3190d37a9076ac698fa91fdfeef1470f16` |
| `notes/progress/2026-10-06-independent-initial-admission-construction.md` | `4feb8131e9360ba8508b0eace82d882e446433d5b5f75beee402027e4986284f` |
| `notes/progress/2026-10-06-source-profile-admission-construction.md` | `00f9e4e8db427fe97a46bd25245cf235c02d2e38007c5b9bb9088d9b40db8636` |
| `notes/progress/2026-10-06-initial-context-source-construction.md` | `10e86ed3bac72d91f03c83acf50ed8e8336ab3c3d0df4a90a03cbe4efdc7ef75` |
| `questions/2026-10-05-production-function-inlet-context-domain/approved-answer.md` | `9b63603890cd522ec80ef81e6208c52acdb1f09ab0a847a9b51368a8f563acf3` |
| `questions/2026-10-05-production-function-inlet-context-domain/receipt.md` | `a952c4588f6020ba1c51f69c623bf12ef695d73fe086496bf6ecdeee37450021` |

Commit packet:

- Exact leased path: `notes/progress/2026-10-08-init-world-adversarial-shortcuts.md`.
- Baseline SHA: `8a3f7ecbc0aef25fd448593fea1cf8fd5891ddf4`.
- Dependency changes: this producer changed none; live snapshot hashes above,
  with complete baseline/current equality deferred to the primary.
- Review status: compiler-referee reviewed; one minor precision finding was
  repaired in the paragraph above and primary delta-checked; partial-schema
  result only, with no gate closure.
- Checks already run: targeted pinned/live source reads, factor/quantifier
  inspection, dependency hashing, note whitespace/local links; no executable
  experiment, test, build or Oracle.
- Proposed commit: `research: audit initial-world admission shortcuts`.
- Shared-record deltas intentionally left to primary/curator: record the
  partial-schema limits; distinguish complete same-X solution readout from
  construction of that solution; retain INIT_WORLD/SEM_JOINT/INIT_VALID open;
  schedule a stronger falsifier only after the independent clauses freeze.
