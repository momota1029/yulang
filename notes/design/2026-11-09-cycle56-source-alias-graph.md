# Cycle56: canonical source-alias graph references

Status: Draft implementation boundary. Date: 2026-11-09.

## Bounded objective and data
Close the source-identity boundary left by cycle54's flat scalar graph: different
occurrences of one source variable must point to one actual finite node identity,
even while unresolved. Do not merge distinct source names just because both are
unknown or have equal scalar values. Reuse the existing executable first-occurrence
representative scan. A prepared graph retains the finite occurrence-sized storage
but exposes a canonical root map; unused duplicate storage is not observable via
that root map. This is not physical graph compaction or recursive graph creation.

## Independent meaning, execution, theorem types
Independent alias meaning is equality of source table names. For every finite table
and slots i,j, canonical i = canonical j iff source i = source j. The scan preserves
the source name and is idempotent. No knownness, model, or source scope premise is
needed for this identity claim.
Execution feeds the actual cycle54 graph to the existing graph inspector at the
canonical root. For every finite positive-string/equality source table, initial
problem and finite supplied updates, string-head matching at this canonical root
is equivalent to every independent original source model forcing the original
occurrence to string. Unknown snapshots are equivalent to two original source
models assigning inequivalent types at the original occurrence. Connect original
occurrence diagnostics and the actual checked Index producer to the canonical
inspection result without hiding aliases or missing request names.

## Scope and authority
This adapter retains the fixed finite table and supplied finite updates. These
are proof-fragment restrictions, not language rejection rules. Explicit equality
links can imply equal types but do not identify different source names. Effects
are not identified. Scalar labels preserve int/bool/str/unit as in cycle54, but
the unconditional source theorem still concerns the positive-string fragment.
Read work/dots-audit x-oracle X13-X17 and C3-PARENT, and spec 6.3. Those examples
support shared-source/associated equality behavior; they are not a generic graph
proof. No new Yulang2 instance or semantic decision is needed for this adapter.

General B4 still has five open bridges. Recursive graph construction, dynamically
generated source slots, declaration-derived requests, general applicability,
dictionaries and language-level four-way classification remain open. This closes
a named finite source-identity sub-boundary, not a whole general B4 bridge.

## Capture routing and verification contract
The inspector captures node indices for variable/shared patterns even if the node
is unknown. Literal old/new observations therefore differ in those references.
Define a total routing operation on observations that maps every capture and cycle
reference through canonical. For every table, initial problem, finite update list,
pattern and original occurrence, inspection at the prepared canonical root equals
routing the old inspector result. This is exact for all pattern constructors in
the flat graph, rather than just equality of knownness bits. In every independent
original source model, a routed captured node has an equivalent type to its
original occurrence. No equation between effect components is asserted.
