# Cycle126: checked declarations to computed output transactions

Status: Draft implementation bridge. I-18 item5, shrinking the output side of
dictionary evidence; general B4Bridges V3 remains12/12 unfilled.

The source of truth is spec06 §6.3: associated output binders are ordinary
variables produced by actual where children. Cycle125 computes their local
terms but does not tie that computation to the declaration selected by Plan.
This cycle joins those operations through one checked visible declaration
lookup, using the same key, root role, and invocation-specific frame.

Data: registry, checked certificate, state, actual source occurrence/key, resolved
frame, and BinderLocations.Inputs (head/endpoint/target locations only). Runtime
returns the complete canonical child list plus a Located package. Any missing
key, wrong role, unsupported RHS or unavailable binder source defers the whole
package. It does not assert semantic rejection or candidate selection.

The independent remaining head predicate sees only root, actual declaration,
capture, and supplied head vector, not output terms or child lists. The output
term relation is fixed to actual OutputBinderTerms.Interpreted for the same
visible declaration. A lookup-success theorem constructs Plan and this concrete
term relation. The whole-tree bridge then constructs Transactions.Valid from
successful local lookups, head certificates, exact complete child roots and
recursive child certificates. It supplies every recorded equation internally.

Quantifiers: arbitrary checked registry, state, per-occurrence frames, remaining
head predicate, finite prepared tree and its local-build certificate. The one
recorded batch yields one fixed source dictionary witness satisfying the node
equations in every final model. No model-existence assumption is concealed;
joint feasibility remains the existing exact transaction_models equivalence.

Still inputs: head elaboration, input/target locations, capture/allocation and
source identities, selected key and solved child tree. Nominal/default/input
interval interpretation is not invented. No changes to Astra-owned declaration
or state definitions, spec, plan or lake configuration. No new fragment
classifier. Yulang2 ROLE-MORE-001–008 were refetched; old advertised-where
behavior is not imported into the new candidate preconditions.
