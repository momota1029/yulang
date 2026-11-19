# Cycle 271: exact visibility for finite record-origin edges
The mixed recurrence checker excluded every record because a coarse record
tag does not determine a literal shape; cycle270 proved a shadowed second
position can never be semantically equal to a target. Keep the unchanged
old semantic judgment and derive the first-visible label contract:

1. Compute first payload by label in a finite list. Show every field probe
splits on that lookup; equal lookup tables preserve all probes and the full
type. Equivalent finite records have the same visible labels and equivalent
first payloads. Preserve the separate exact-empty meaning.
2. Given a noncanonical projected index and all-model equality to a target,
a single full model excludes hidden indices by changing the hidden
payload while keeping every first lookup unchanged. A visible index then
agrees with the corresponding canonical recorded child in all models.
Infer the actual unrestricted semantic Edge iff at least one recorded
child is equal to the target; unknown target equality remains unknown.
3. Combine this exact edge inversion with rigid/nominal closure and a
model witness. Synthetic journal fixtures should include nontrivial
record fields; no claim about surface reachability, general model
construction, or kernel termination.

The arbitrary literal record test now reduces to the certified
canonical layout even if its label order or multiplicities differ.
First lookup of a different field is unchanged by updating a hidden
value. A live noncanonical index must survive the full-carrier Int/Str
comparison in one actual model, which proves it is visible. The set
of visible labels is fixed by field-presence probes, and the visible
payload equivalence at that same key holds in every valid model.
Exact-empty is separately distinguished by an actual carrier probe;
it has no semantic type edges. All normalized structural shapes now
share a single edge support theorem.

The executable comparison now also checks distinct canonical record
signatures, and distinguishes exact-empty from a width record despite
the common coarse tag. A literal normalized structural projection
can be replaced by its actual child source. Equality of other sources,
nested projections, and deferred observations is not guessed.
The new full-structural window keeps closure and totality distinct:
positive or negative finite graph answers require checked semantic
conditions; missing information is still unknown.

## Recover visible positions in a differently ordered literal query

A record query should not be forced to use exactly the normalized
shape. If the supplied label list has exactly the known visible label
set, construct an observation by filling its entries from the original
first-visible table. Retain arbitrary order and multiplicity; only the
first occurrence of the requested key is observed as a semantic
representative. Forward and reverse equality use, respectively,
the actual existence witness and the all-observations readback lemma.
Wrong label sets and hidden positions must never be returned as positive.

The two new finite-window fixtures are independent initial journals:
an acyclic record with outgoing record and exact-empty children, and
a guarded one-field self-reference inside a two-field record (the other
child is exact-empty). All edge entries are total and both root outcomes
are proved against full models. The guarded example also demonstrates
distinct projected results at the earlier and later child.
