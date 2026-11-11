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

## Proven terminal-output obstruction and conservative next step

`GeneralDictionaryBinderOnlyBoundary.built_root_outputs_empty` proves for every
finite Built tree that its root has no output obligations. An output-only RHS
requires an actual producer child with another output. Thus the old transaction
theorem cannot yet witness any completed output-bearing root.

We preserve that theorem and boundary, rather than weakening Produced or child
completeness. The next partial interpreter also supports an actual explicit
input-variable RHS only when capture.inputs assigns the exact same source ID to
both interval endpoints. There is then no midpoint choice: the source variable
is that shared endpoint. Unequal intervals, defaults, constructors and compound
RHSs remain deferred. Capture/head correctness is still not proved by Capture
itself, and the actual root/child target equations still have to be recorded.
A finite two-node checked declaration example should end at such a singleton
input alias, with repeated root outputs and one shared final model.

## Independent materialization and fixed-input order

Materializes fixes lower/upper/head/target fields to Inputs and requires, at
every output occurrence, an actual Denotes proof for the state's source of a
local variable slot. It contains no build or lookup success. Build iff this
relation makes the partial compiler complete for its declared supported source
relation. The registry lookup then iff the same actual visible checked
declaration has key/role, canonical children and independent materialization.
Visible and where reorderings retain output binders, head and associated RHSs,
so lookup/build and the entire returned child/Located package are equal at fixed
source inputs. This does not establish final-state or candidate-order invariance.

## Planned whole-tree preparation

To remove caller-supplied output vectors from the complete input tree, use a
finite Recipe containing only occurrence, chosen key, Inputs and child recipes.
Preparation computes each local package, recursively prepares children, and
checks their full occurrence roots against the complete canonical child list.
Failure defers the entire tree; no child is discarded. Successful preparation
should yield Built from a recursive head-only certificate, not from manually
provided child success/output certificates. Keys, tree shape and source frames
remain explicit: this is not search or general saturation.

## Capture realization and remaining head input

`Realizes` specifies the capture facts still owed by head matching: each input
value lies between its captured endpoint values and each output value equals
its captured source. The normalized variable RHS then agrees with its computed
source term for every realization. Recording relates every root target to that
RHS variable value, without assuming head matching or model existence.

The final supported head-materialization step may compute head terms only for
normalized plain variables whose captured endpoints have identical source IDs.
HeadlessInputs has only lower/upper/target fields; a successful head builder must
refer to each actual positional declaration head and return existing Inputs.
Compound/nominal heads remain deferred, and input-range applicability still
comes from actual stored inequalities. This is not general candidate inspection.

The final head builder is exact for its independent positional relation and
validated against the terminal fixture. Whole Recipe still receives Inputs;
automatically composing HeadlessInputs through registry lookup and the full
recipe remains next work. The mid-cycle upstream addendum4 requires every
unnamed lower head to be known before role resolution. None of these term
materializers performs role resolution or weakens that pending guard. Astra now
owns item3 as well as1/2; all candidate judgments stay untouched.
