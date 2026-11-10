# Cycle82: source role discharge from associated saturation state

Status: Draft. Date: 2026-11-10. Scope: finite, scope-resolved source boundary.

## Partial goal and stop condition

Compute a joint finite allocation for every source role receiver and every
associated-equation endpoint, then run the existing associated saturator and
ordinary solver before checking every role against the resulting explicit scalar
evidence. Remove the total caller head map used by cycle81. Bare clauses must
retain a receiver slot even when the equation program is empty.

The table is the ordered role receiver list followed by the existing equation
endpoint table. Equation slots are shifted by the role count. Same-name type
identities use the existing identity closure. No dummy equation or dictionary is
introduced for a bare clause. Duplicate names are intentionally separate
occurrence slots that share their type, not their effect row.

## Independent judgment and theorem shapes

For every checked package p, old ordinary state s, well-formed core impl list and
associated environment, the emitted evidence at each allocated slot is equivalent
to DeclarativeDerives on the computed graph and identity-extended initial state.
This judgment uses independent declaration resolution, not executable output.

For every original Source src and package accepted by the cycle81 checker, the
joint Boolean readiness test is true iff the emitted ordinary state has a model
and every source clause has a corresponding retained role occurrence, a scalar
head independently derived at that occurrence, and a structurally filled goal
that independently Resolves. No successful run, caller head map, enough fuel or
chosen assignment is assumed. The model-existence conjunct is checked by the
actual solver. A separate theorem describes every model through old constraints,
source coherence and independent closure facts.

This is an evidence-backed readiness test, not final selected/pending/ambiguous/
rejected diagnostics. Missing explicit paired scalar evidence, bool/unit encoding,
unknown names and invalid signatures do not acquire new language semantics.
General semantic entailment, source expression inference, dynamic where generation,
visibility and the five general B4 bridges remain outside. The initial State and
finite scope-resolved Source remain explicit inputs. Spec6.3 fixes source sharing,
associated equations and sibling stabilization; no language decision is made.

## Verification

Focused module build; trust=0 theorem audit; bare receiver allocation, unknown
receiver, evidence propagation into a bare receiver, missing dictionary, invalid
source and conflicting ordinary evidence. Preserve existing Lean files and append
imports/audit/README only. No full local build or full Audit.


## Implemented strengthening

The final theorem `ready_declarative_exact` has no executable result on its
independent side: SourceModels relates the original state and source identity
to SourceDerives, whose recursive steps inspect original source clauses. The
allocation-to-source and source-to-allocation proofs cover every finite accepted
source and every original state. A successful source checker remains an explicit
premise because the old state is indexed by its computed package table. This is
not a claim that arbitrary unchecked syntax or an unconnected caller package
is accepted. There are 19 new theorems, all connected to the joint readiness goal.
