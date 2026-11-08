# Cycle 1: finite endpoint occurrence slots

Status: Draft, 2026-11-08. Scope: a finite table of original lower/upper
endpoint occurrences, not a complete source allocator for recursive resolution.

Data: `Table := List (Ty × Ty)` and `Source table := Fin table.length × Bool`.
The row is source occurrence identity; false/true selects lower/upper. Equal Ty
values at distinct rows remain distinct slots. The concrete allocation uses
`2 * row + side : Fin (2 * table.length)`; no slot function is an input.
The inverse recovers the row and side using division and remainder.

Execution: `collect` maps a finite list of actual open requests to its endpoint
rows. `requestSource` addresses each original row and side. Then allocate/decode,
endpoint lookup, and a slot assignment obtained by
composing any Ty interpretation with decode/lookup.

Theorems: for every finite table and source, decode(allocate(source))=source;
for every slot, allocate(decode(slot))=slot; allocate is injective; for every
interpretation and source, the slot assignment at its allocated slot equals
the interpretation of its original endpoint. In particular nominal constructor
identity and the original endpoint graph/root are preserved by lookup, not
reinterpreted by a structural erasure.

Boundary: the table is supplied. Collecting all endpoints produced by narrowing
and recursive children into this table, proving semantic adequacy of the Ty
interpretation, and connecting these occurrence slots to existing Ty→Fin n
Allocation are not proved. A Ty-only allocator cannot distinguish duplicate
source occurrences, so no such identification is silently introduced.
