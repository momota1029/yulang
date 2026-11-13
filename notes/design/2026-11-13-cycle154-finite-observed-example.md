# Finite nominal output regression

Scope: conditional soundness/auxiliary evidenceNode work, not general V5 completion.
Construct an inhabited ternary nominal source and an actual named output request. The
source certificate must justify all three projection tests. Check that the older binary
certificate cannot describe this query. Connect the actual declaration output request
to generated materialization Models for every source model; do not assume generated
Models. Reachability, stable classification and complete dictionary evidence are separate
obligations unless proved explicitly below.

## Verified refinement

The concrete source has two slots: ternary nominal `N(int,int,int)` at slot 0,
and scalar `int` at slot 1. The sole checked role declaration has scalar input
and a closed ternary named output targeting slot 0. The source model is explicit;
the output is not freshly allocated. Arbitrary source models satisfy all four
materialization tests, hence the real recursive semantic Instance and leaf Evidence.
The initial source is reachable by the empty trace. It is already stable: its
terminal declaration and entailed output schema require no installation. We exclude
all actual feedback updates, including refreshed knowledge for unconstrained source
identities by two distinct scalar assignments. Current support and newest captured-value
boundaries both classify the source as the exact selected leaf dictionary.

This closes this concrete stable non-scalar output fixture, not general evidenceNode.
There is no claim of a nonempty journal, nonzero execution, fresh-output allocation,
general alias coverage, or full-language progress. General V5 remains 8/14 unresolved.

## Nonterminal extension

Use the same two-slot source with a checked ternary nominal head `N(a,b,c)`
and one strictly smaller scalar child `Display a`. The three distinct binders
capture the same scalar slot. The parent retains a named ternary output at the
existing nominal slot. The actual guarded installation creates a child edge and
a nonempty journal; the child is justified by a checked scalar declaration.

The new nonterminal modules prove the complete initial → one Value Step →
reached stable endpoint chain, independent recursive Classify and full two-node
Evidence in every final model. A finite separating model rules out raw and
feedback cycles, including equality-transported projection edges. A varying
assignment rules out extra refresh knowledge at identities above the source.
Ordinary constraints are exact, not replaced by the desired semantic conclusion.
The output remains an already observed target, not fresh allocation.

Both regression chains remain concrete examples, not the general V5 bridge.

## Reserved-target negative regression

A final bounded follow-up changes only the named output to reserved identity 2
(seed 2, initial slots still 0 and 1). The module
`GeneralDictionaryFiniteObservedExampleReserved` proves InitialSource, initial
reachability, the exact actual named-output request list, and absence of both a
target slot and any finite Observed certificate. The original concrete source
model remains valid but assigns int to 2 and refutes the generated ternary
request. Thus reservation alone does not entail output constraints; an actual
installation would genuinely strengthen the model set. This is a checked
countermodel/coverage boundary, NOT a completed install regression. No actual
install, final model, stable classification, or recorded-request application is
claimed here. The target is reserved, not newly allocated by an execution.

Next exact obligation: construct a satisfying branch model assigning target 2
its ternary output, then discharge actual Local/decision/joint guards for the
changed root and use the countermodel for installation novelty. The older
observed fixture's all-source-model branch lemma cannot be reused: this module
proves that premise false for the changed output.

### Follow-up closes the reserved-target installation obligation

The preceding negative checkpoint is now extended, rather than left as an
installation gap. `GeneralDictionaryFiniteObservedExampleReservedPositive`
constructs a second concrete source model assigning ternary nominal(int,int,int)
to reserved identity 2, proves its generated request semantics directly, derives
Prepared/Local/decision/Joint guards, and proves an actual Value installation.
Novelty uses the negative checkpoint's int-at-2 countermodel. The installed state
has the positive model, is Value-reachable, and records a nonempty journal.

`GeneralDictionaryFiniteObservedExampleReservedRecorded` applies
`GeneralDictionaryRecordedRequestModels.reachable_root_requests` to this actual
recorded packet, deriving the current ternary request semantics for EVERY final
model without an initial targetslot or Observed certificate. This is the
positive regression for the recorded-request theorem. No Stable/Classify/full
Evidence is asserted for this reserved-target variant. Identity 2 was reserved
in the initial source, not freshly allocated by the transition. The earlier
8/14 general bridge limit is unchanged.
