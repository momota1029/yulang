# Independent review: semantic Plan transport and selected-only outcomes

2026-11-18 UTC. Reviewed other authors' new PlanSemantic, PlanSemanticExamples,
SemanticObserver, SemanticTrace and SelectedSafety modules. Also read the called
FactSemantics Models definition, value/equivalence congruence lemmas and quadratic
fact-budget proof. No reviewed source file was edited.

## Result

No correctness or quantifier-scope defect found in the versions recorded below.
All five modules independently rebuilt into a separate focused cache with strict
kernel checking, exit0. A standalone base-relative compatibility probe and nine
selected axiom audits also passed. Source SHA256 values and complete output:
`semantic-independent-build.txt`. Reproduce with `rebuild-semantic-review.py`.
Earlier dependencies were reused, not independently rebuilt here. This is not a
whole-repository build or a runtime/benchmark result.

## Layout versus semantic agreement

PlanSemantic.Layout fixes the declaration, constructors and interpretation. These
are exactly the syntactic/compilation data used in schema/keys/facts equality.
No binder or center identity equality is required to prove the proposal-table
identity. Layout equality alone is correctly NOT used to prove model equivalence.

Compatible adds semantic equivalence of binder values and positional default-center
values at one explicit assignment. Centers are compared by actual positional lookup
with the same getD0 fallback; no permutation invariance is silently assumed.
actual_value reduces expression evaluation to actual-mode variable assignments and
uses the existing expression congruence theorem. Endpoint modes are not asserted to
agree. owned_transport uses the fact that body schema equations are actual-mode.
The request target itself is unchanged in both equations; only the evaluated body
is transported via equivalence. This justifies body/effect transport without
replacing semantic equivalence by syntactic equality.

## From one assignment to all assignments under base

SemanticObserver separates LayoutCompatible from BaseCompatible. This matters even
when base is empty: vacuous BaseCompatible cannot establish syntactic layout equality,
so the observer-table equality and no-outside result still require LayoutCompatible.

write_actual first rewrites to the fixed-Plan write semantics. In each direction
of the iff, it obtains the prior Models conjunction and uses prior.1 to recover
`base assignment`. Only then does it instantiate BaseCompatible for that exact
assignment and transport ClassEffects. Outside base, both sides are false because
Models explicitly contains base. No inference from one assignment's compatibility
to universal assignment compatibility occurs.

The chosen root is extracted from the actual proposal before introducing assignment.
SemanticTrace uses a given position-sensitive planned trace, so its history likewise
is independent of the assignment. Each event retains the exact snapshot, root and
observed Plan at its own intermediate finite state. The base predicate stays fixed
throughout the run, and the proof does not reinterpret earlier facts under an arbitrary
new Plan. The premises still require base-relative binder/default-center agreement
for every selected root at every finite state. They are explicit obligations not yet
derived automatically from general source models.

## Examples and their limits

The recenter example modifies a Plan's center identities while keeping its packet.
A constant assignment makes the relevant values equivalent. With an actual positional
input index and a changed center, structural Same is impossible. Thus the semantic
condition is genuinely weaker at that assignment. The example is NOT a certified
source transition, a valid Frame, or a claim that all assignments support recentering;
its comments correctly say so. Zero-arity Plans are not silently used to witness the
strictness claim because the theorem explicitly requires a positional Fin index.

SemanticReviewProbe additionally constructs LayoutCompatible and BaseCompatible for
recentered Plans on the explicit base `assignment = constant cell`. This validates the
base-relative interface without claiming unrestricted agreement.

## Source theorem and checked outcome

SemanticTrace.source_certificate places the finite pool existential outside all
choices of base, fixed Plan, owner, inspector and Plan schedule. Actual source Initial
formation derives that pool. The inspector's reachability proof and the layout/base
compatibility assumptions remain visible. The theorem is conditional on actual
selected-check run success; that success supplies readiness of recorded events and
the terminal selected list, without a universal Ready premise.

As in the earlier dynamic-source review, each inspected snapshot is reachable from
the same start, but consecutive inspected snapshots need not be linked by a source
Step. The caller still supplies roots and Plans; no complete compiler, Frame/packet
producer or old-Step simulation is constructed by the theorem.

SelectedSafety.no_outside needs only LayoutCompatible and request coverage. It uses
actual error-path provenance to reach the failing finite state, transfers the observer
to its fixed-layout equivalent, derives finite-basis closure and contradicts the
existing checked scheduler's unsupported-fact error. It does not rule out selected
missing/untranslated body errors, and does not need semantic BaseCompatible.

outcome is correspondingly limited and correct: successful checked execution OR an
internal selected-body diagnostic at a genuinely finite-rebase-reachable state. The
proof carries actual run equality, selected-root membership and the exact ClassCheck
error. The polynomial bound counts nontrivial finite writes and includes pool list
multiplicity. It follows from at most one body fact per request plus at most n² pair
facts; it is not a complexity bound for inspection, alias search, compiler execution
or old source transitions. The outcome theorem proves neither satisfiability nor
source-language acceptance/rejection. These limitations should be retained in the
final user-facing summary.

Only standard propext, Classical.choice and Quot.sound appear in the selected audits.
No runtime experiments, new source semantics, forbidden placeholders or native proof
evaluation were used in this review.
