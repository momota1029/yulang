# Computed source-name allocation

Status: proof interface, 2026-11-10. Representation only, not language semantics.

## Objective and data

Remove the last caller-chosen renaming map at the finite source boundary.
Compute a name map directly from source receivers, equation outputs and all
input assumptions. Encode a name by its first occurrence index in that list.
This uses finite occurrence capacity, not a promise of minimal distinct-name
capacity. Repeated identities keep one index; gaps are harmless. Role/member
identifiers and structural Goal binders remain unchanged.

## Independent judgment and executable entry

Use the existing independent named Derives and Models judgments. No new
meaning of inference is defined. The allocator constructs both source and
input and calls the existing checked/allocated/saturating entry. No external
map, injectivity proof, package, state, model, fuel or solver success is input.

## Statements and proof chain

For every finite source/input:
1. Supported names encode below computed support length, with exact decoding.
2. Encoding is collision-free on that support, so the checker always accepts.
3. Independent evidence at every query name, source model existence and
   readiness are preserved after allocation (arbitrary env/roles/wf/awf).
4. Under every collision-free input renaming, computed first-occurrence indices
   agree, hence the allocated source/input pair is identical. This is canonical
   for preserved occurrence order, not for arbitrary sibling permutations.
5. Reallocating an already allocated pair is idempotent.

The finite scalar/one-binder fragment and well-formed registries remain explicit.
The source syntax carrier and input assumptions still need deriving from actual
source. No dynamic child closure or language diagnostic is claimed.

## Authority and remaining boundary

Reread spec 6.3 and work/dots-audit x-oracle C3-PARENT / C3-PARENT-NEG, which
cover sibling conjunction and required-child behavior. Numeric compaction is
an encoding invariant, not an additional Yulang2 rule. No new Yulang2 run.
Roles.Impl.constraints still loses grouped receiver/output annotations; do not
pretend that compaction reconstructs them or chooses invocation sharing.
All five B4 bridges and the full I-13 semantic audit remain open.

Proof refinement: unused names encode to capacity, outside the used range.
Therefore exact evidence reflection needs no query-support premise.
