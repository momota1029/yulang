# Executable term decoding connects scoped publication to regular solutions

Date: 2026-10-26. Producer: `/root/paper_allocation_execution`, generic
`lean_prover` fallback. This is the bounded final connection packet following
regular constraint-history soundness and owner-local scoped publication.

Status: frozen source checked and complete originating-module audit passed.
Fresh non-author review, integration and Git operations are primary-owned.
The original full source inference-soundness target remains unchanged/OPEN.

## Frozen artifacts

- Source: `notes/theory/lean/YulangClosure/SimpleSubRegularPublication.lean`.
- Source SHA256:
  `18fc6f138204e1529dcd0bb9c01a20de7444a26e4dadc87677460ccd8ac9fc99`.
- Owned isolated project, cache and evidence:
  `/workspace/scratch/f98087c7ac1a/inference-regular-publication/`.

All frozen dependencies and their isolated checked copies were rehashed and
compared byte-for-byte after the final audit:

| Dependency | SHA256 |
| --- | --- |
| `SimpleSubConstraintSyntax.lean` | `a9ec574d31223e0484fd827838b45cd019fc858eece9f326c95ebc2e1e77a1f6` |
| `SimpleSubConstraintSoundness.lean` | `33709d3978e8071708c10bba23d85b1b025c11dfd988220501acb7c6e3220293` |
| `SimpleSubGeneralizationSoundness.lean` | `3f6114e4173d6cade6ad135ed83ad543116e28e87845b0f6a834cb8f727f6246` |
| `SimpleSubScopedPublication.lean` | `d64e9bffca5d513985237a9ff78dcf3d9e43baae1594edbc93dff4b5410d428f` |
| `SimpleSubRegularSolutions.lean` | `755d267714bd23bcfc17ec37d43d258392567b7d1356afc4897f541ae9855b29` |
| `SimpleSubRegularConstraintSoundness.lean` | `1d2266867115fc27afe39dbb80a3ca0e8f75247a2e16b739145137e83999de33` |

The primary reported these prerequisites pushed in `e172e3b` during this
packet. No existing source, compiler, root import, shared record, repository
manifest or Git state was edited. No children were launched. Only the two
leased deliverables and owned scratch/cache/log paths were written.

## Concrete connection achieved

The regular-history theorem and finite-Term scoped-publication theorem used
different interpretations. This module connects them through an actual total
recursive decoder returning `Option Nat`. It does not supply abstract model
laws or equate regular cyclic graphs with finite-Term valuations.

The proved chain is:

1. Decode an explicit finite inventory of target published clauses and
   transported client clauses into concrete graph comparisons.
2. Run a represented `Regular.ConstraintHistory` from those comparisons to
   terminal demands.
3. Accept the terminal finite regular certificate. The existing checked
   certificate and history theorems construct regular satisfaction of every
   original decoded inventory comparison.
4. Use the existing `ScopedPublication.publication_clause_image` theorem to
   derive the image of every original published clause. This is a theorem
   application, not a newly assumed clause-inclusion law.
5. Use the proved decoder renaming equation to pull those regular
   interpretations back under one reference assignment shared by all original
   finite uses and every client clause.

The main theorem is `publication_history_with_clients`; its zero-history
specialization is `checked_publication_with_clients`. Neither takes a final
satisfying valuation, a supplied semantic model, an arbitrary preservation
law, or an already-solved original publication as an input.

## Executable decoding and exact fidelity

Namespace: `YulangClosure.SimpleSub.RegularPublication`.

`References := Kind → Nat → Nat` is plain kind-indexed data. It assigns a graph
reference to a syntactic variable identity and carries no semantic proof.

A derived structural `DecidableEq` instance for the frozen `Regular.Node`
compares exact constructors and all fields. `findList` / `findNode` search the
existing finite graph table and return the first exact matching constructor.
`findList_sound` and `findNode_sound` prove the corresponding actual lookup.
No native evaluator or unchecked equality oracle is used.

`decodeTerm graph refs` handles the frozen structural `Term` syntax as follows:

| Term | Actual decoding action |
| --- | --- |
| Variable | Look up `refs kind identity` in that kind's graph table; reject a missing reference. |
| Atom, bottom, top | Search the corresponding exact existing node. |
| Function | Recursively decode argument, argument effect, result effect and result; search the node with those exact four ports in that order. |
| Empty record/tuple/variant | Search the respective empty finite carrier. |
| Record cons | Decode field and tail; require the tail lookup to be a whole finite record list; prepend the exact label, optional bit and child reference; search that exact record. |
| Tuple cons | Decode head and tail; require a tuple tail; prepend to its finite ordered element list; search the exact result. |
| Variant cons | Decode payload and tail; require a tuple payload and variant tail; prepend the exact tag and whole ordered payload list; search that exact variant. |
| Union/intersection | Return `none` explicitly. |

`decodeTerm_found` proves that every returned reference exists in the same
graph. `decode_function_exact` exposes all four recursively decoded ports and
the exact resulting graph lookup. `prependRecord_exact`, `prependTuple_exact`
and `prependVariant_exact` expose the actual finite tails/payloads and exact
metadata-preserving output lookups. Structural cycles can occur through the
returned child references, but decoding never unfolds a cyclic row spine into
infinitely many fields or alternatives.

The decoder is total as an `Option` function. Success requires the input graph
to contain the exact constructors used by the serialized finite syntax,
including necessary intermediate empty/tail/payload nodes. No completeness
claim says that every current native graph already contains those entries.
Providing such a faithful finite serialization is an explicit remaining native
bridge, not a new assumed semantic law or runtime validator requirement.

In particular, a semantically representable full record, tuple or variant node
is insufficient for this decoder if its finite syntax also requires an absent
nil node or intermediate record/tuple/variant suffix node. The same applies to
an absent tuple node used to decode a variant payload list. No graph completion
or graph augmentation operation, nor a preservation theorem for adding those
nodes, has been proved. This exact-existing-node/suffix requirement is part of
the actual native decoder boundary in addition to lattice rejection.

## One reference assignment and freshening

The structural-induction theorem is exact, including failure results:

```lean
decodeTerm_rename :
  decodeTerm graph refs (term.rename q) =
    decodeTerm graph (fun k i => refs k (q k i)) term
```

`decodeConstraint_rename` lifts the equation to clauses, and `clause_rename`
lifts it to regular satisfaction. `decodeTerm_congr_bounded` proves dependence
only on the bounded variable coordinates of the actual term.

`decode_freshen_transport` directly applies the frozen
`Generalization.transport_freshen` commuting square to the concrete decoder.
Under bounded original variables, use bounds and anchor preservation, decoding
an original fresh use under the pulled-back references equals decoding its
quotiented/freshened counterpart under the target references. No separate
reference assignment is selected for different ports, clauses or uses.

`publicationTransport` is exactly the frozen transport with boundary zero
and `ScopedPublication.guardLevels afterUse`. The main conclusion uses
`fun k i => refs k (publicationTransport n count afterUse q k i)` for both
original `PublishedSatisfied` and arbitrary `StoreSatisfied` clients.

## Independent regular interpretation and finite checking

`decodeConstraint` decodes both endpoints into one kind/lower/upper comparison.
`decodeStore` preserves the finite clause list, including duplicate entries,
and fails if any clause fails to decode. `decodeStore_member` proves every
input clause has its decoded comparison in a successful output list.

`ClauseSatisfied graph refs clause` means there is an actually decoded pair
for that clause and that pair satisfies the frozen, independently defined
`RegularSub graph` relation. It is not defined by checker acceptance.

`checkStore` executes `decodeStore` and, on success, the existing finite
`Regular.accepts` check. `checkStore_sound` derives graph validity and regular
satisfaction of the entire store from Boolean success alone.

`history_store_sound` takes successful executable inventory decoding, the
concrete regular constraint history, and final certificate acceptance. It
consumes `Regular.accepted_original_demands` directly and proves regular
satisfaction of the original finite syntax inventory. This is the point that
connects finite syntax to the already-proved regular history result.

## Exact main premises and serialization boundary

`publication_history_with_clients` retains the existing publication theorem's
explicit structural conditions:

1. Original bound owners and bodies lie in the allocated scope (`BoundsBounded`).
2. Inactive allocation images remain inactive (`InactiveImages`).
3. Dependencies below stopped target capture owners remain stopped (`StoppedClosed`).
4. Stopped capture also stops allocation.
5. Every requested use is below the finite use count.

These are the unchanged conditions needed by the imported source-pinned
publication argument. This packet does not newly claim their all-history
native invariants.

The new inventory coverage premise is precisely:

```lean
∀ clause,
  ScopedPublication.Published n
    (bounds.map (Bound.rename q)) afterCap afterUse
    (roots.map (Row.rename q)) uses clause →
  clause ∈ inventory
```

This is a **syntax-only finite serialization boundary** for the TARGET
publication. It does not assert any subtype relation, model existence,
satisfaction, or correctness of the original program. The theorem derives
original-clause images by calling `publication_clause_image`; it does not
assume that image-inclusion law again.

Clients are appended automatically as
`clients.map (Constraint.rename (publicationTransport ...))`, so no extra
client-image coverage hypothesis is introduced. Their bounds are unrestricted;
the frozen transport preserves future-client coordinates outside the finite
use allocation region.

The remaining inputs are all explicit data/checks: successful decoding of
that inventory plus transported clients, a concrete regular history, and final
finite acceptance. The conclusion is graph validity and simultaneous regular
interpretation of EVERY original published clause and EVERY original client
under the one pulled-back reference assignment.

The direct `checked_publication_with_clients` specialization replaces decoding
and history premises with the executable `checkStore ... = true` condition.
It constructs a zero-step history and invokes the same main theorem.

## Checked examples

### Finite carriers

`carrier_record_decoded`, `carrier_tuple_decoded`, and
`carrier_variant_decoded` compute exact node identities for real cons syntax.
The record carries label 7 with optional bit true; the variant carries tag 8
and the full tuple payload `[0]`. `carrier_store_checked` verifies a finite
certificate for all three resulting clauses, and `carrier_store_regular`
derives their independent regular interpretations.

`optional_metadata_mismatch_rejected`, `wrong_kind_reference_rejected`, and
`missing_reference_rejected` compute rejection when the required metadata,
kind table or reference is absent. `lattice_decoding_unsupported` exposes the
union/intersection boundary for arbitrary terms, rather than silently
coercing them to an available structural node.

### Cyclic publication, two uses and a shared anchor

`cyclicGraph` contains a Function whose argument and result point to itself,
with both effect ports resolving to the separate effect table. The finite
source bound's four-port body refers to a shared lower-level anchor. Its owner
is eligible in the original flags, producing distinct use coordinates 3 and 5
for uses 0 and 1. Both uses leave anchor coordinate 0 unchanged.

After quotient/lowering, the target owner is inactive. The target publication
inventory contains its retained base clause; target copies disappear.
`cyclic_inventory_coverage` proves that exact syntax coverage by cases on
`Published`. This example does not assume the coverage conclusion.

`cyclic_inventory_decoded` computes the actual pair list for that inventory
and the transported cross-use client. `cyclic_inventory_history` performs
actual four-port Function decomposition. `cyclic_terminal_accepted` computes
finite acceptance. `cyclic_publication_and_clients` invokes the complete main
connection, and `cyclic_two_uses_and_client` extracts satisfaction of both
original fresh clauses and the original client comparing coordinates 3 and 5.

`two_distinct_uses_one_shared_anchor` also checks that coordinates 3 and 5
transport to anchor 0 while future coordinate 6 remains 6. The semantic graph
is genuinely recursive; the result was not obtained by pretending its model
is a finite `Term` valuation.

## Source correspondence and remaining obligations

The exact original obligations and native owners remain those documented in
the frozen regular/history/publication receipts:

- Original source-preservation and birth-level corrections require the same
  source scope, actual retained copies, immutable source-value qualification,
  and joint Call/effect witness. This packet does not redefine those claims.
- Native `term.rs` supplies the four-port and finite carrier correspondence
  represented by the decoder. Complete native effect/Call admission remains
  outside the structural interpretation.
- `candidate_scheme` owner-local expansion and `prepare_candidate_fresh_use`
  capture/allocation guards motivate the imported scoped publication theorem;
  actual native dependency closure, active images, provenance and first-image
  coherence remain obligations of the actual producer.
- Native successful public export/use paths must include final no-error and
  admission/ownership checks. `Result::Ok` alone does not establish success.
- Native ordinary coalescing and recursive-bound owners must produce the
  faithful graph, syntax inventory, references, concrete history and finite
  certificate. The legacy serializer's empty effect ports are not identified
  with this four-port decoder.

The precise first remaining native connection is to prove that an actual
accepted no-error/admission path provides this finite serialization and its
syntax-only coverage, the successful decoder equations, the concrete history,
and terminal certificate acceptance. A proof could extract finite evidence
from existing native data; no runtime validator or compiler change is mandated
by this theorem.

The next original source connection must derive the unchanged source-scoped
Call/effect judgment and joint witness from these actually generated original
constraints. No original `SourceProblem.InferenceSoundness` instance is proved
here. References are now interpreted coherently in a regular graph, but
full-source generation, native decoding/trace correspondence, ordinary
coalescing, quantifier/provider/guard coverage and contextual effect strategies
remain explicit work.

Represented limits: union/intersection terms fail decoding; no unguarded
alias or lattice cycles; finite whole record/tuple/variant shapes, no native
open row tails or complete width/presence/variant admission; exact existing
constructor entries are required. These are limits of this intermediate proof
bridge, not a redefinition or smaller replacement of the original source
language theorem. Full soundness, principality/completeness, termination and
progress roots remain unchanged/open.

## Verification

Pinned native Lake:
`/workspace/scratch/e41512dd7957/toolchains/lean-4.35.0-linux/bin/lake`.
Lean 4.35.0, `LEAN_NUM_THREADS=1`, `-j1 -M1024`, one owned Lean process at a
time; every call bounded by a 60-second subprocess timeout. Five focused
calls consumed approximately **40.0 seconds** total, within the assigned
300-second checker budget. Source was frozen immediately after the successful
full build, before the audit.

| Log | Result |
| --- | --- |
| `check-01.log` | Exit 1, 22.921s including fresh dependency builds: generic atom/bottom/top search needed the explicit matched kind; missing-tail proofs needed their lookup equation; qualified the regular Certificate name. |
| `check-02.log` | Exit 0, 3.608s: executable decoder, lookup soundness, rename/freshening commutation, finite store checking and regular-history connection. |
| `check-03.log` | Exit 1, 6.231s: exact carrier inversion proofs needed reflexive equations after dependent lookup cases. Main publication theorem itself elaborated. |
| `check-04.log` | Exit 0, 4.860s: frozen complete module and all examples; clean diagnostics. |
| `audit-05.log` | Exit 0, 2.379s: complete originating-module type/axiom audit. |

Reproduction commands:

```text
lake build YulangClosure.SimpleSubRegularPublication
lake env lean -j1 -M1024 RegularPublicationAudit.lean
```

All **148 originating theorem constants** passed, comprising **42 authored
public theorems** and **106 generated helpers**, including generated equality
machinery and private equation helpers. There are 148 matching begin/end
receipts. Every authored printed exact type was inspected.

Axiom sets: **89 empty**, **42 `{propext}`**, **17 `{propext, Quot.sound}`**.
The auditor allows only `propext` and `Quot.sound` and rejects project axioms.
No `Classical.choice`, `sorryAx`, native proof evaluator or kernel bypass
occurs. Source scan found no hole or unsafe/bypass token.

| Evidence | SHA256 |
| --- | --- |
| `RegularPublicationAudit.lean` | `a2a0f8b0274d9e37635e38e4fad7e9f5e2844997eb7da955bbeb6e287a98dfcf` |
| `audit-05.log` | `07142e459a90c18bcec796c224469da753ae415ca892210d028da81b08da2775` |
| `check-04.log` | `57c821ec5a00f599a841a9e0da0f7344195a2161bf465aacc3133902bd93a85a` |

Source map: executable decoder and lookup proofs 12–202; regular clause/store
interpretation and accepted-history connection 204–290; exact constructor
inversions 293–338; main scoped/client connection 340–411; carrier and cyclic
shared-anchor examples 414–547.

Writes stopped after this receipt. No owned Lean process remains running.
The frozen packet is ready for fresh independent review and primary integration.
