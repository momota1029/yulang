# Regular certificate acceptance reconstructs original constraint demands

Date: 2026-10-26. Producer: `/root/paper_allocation_execution`, generic
`lean_prover` fallback. This is the bounded constructive application packet
following the frozen regular-solution certificate construction.

Revision r2: primary applies the independent review's MINOR-1 terminology
correction, replacing equality insertion's ambiguous "forward preservation"
with its exact backward solution-reflection direction. Initial r1 receipt
SHA256: `7b9c333d6f097271c83434cf4eb6c92589f717af8354caddd7ad1fb52ff62225`.
No Lean source, theorem, check or dependency changed.

Status: complete new module checked, all originating theorem constants
individually type/axiom audited, source frozen. Non-author review,
integration, repository records and Git operations are primary-owned.
The original full inference-soundness claim remains OPEN.

## Frozen source and dependencies

Source: `notes/theory/lean/YulangClosure/SimpleSubRegularConstraintSoundness.lean`.
SHA256 `1d2266867115fc27afe39dbb80a3ca0e8f75247a2e16b739145137e83999de33`.

Unchanged frozen dependencies:

| Dependency | SHA256 |
| --- | --- |
| `SimpleSubConstraintSyntax.lean` | `a9ec574d31223e0484fd827838b45cd019fc858eece9f326c95ebc2e1e77a1f6` |
| `SimpleSubConstraintSoundness.lean` | `33709d3978e8071708c10bba23d85b1b025c11dfd988220501acb7c6e3220293` |
| `SimpleSubRegularSolutions.lean` | `755d267714bd23bcfc17ec37d43d258392567b7d1356afc4897f541ae9855b29` |

The primary reported integration of the earlier packets as `bd4178c` and
`dce3d2f` during this work; the exact dependency bytes above were independently
rechecked after the final audit. Only the new leased proof file, this receipt,
and the owned isolated project/cache/logs were written. No existing proof,
compiler, root import, shared record, repository manifest or Git state was
edited; no children were launched.

## What premise this actually removes

The previous finite-Term history theorem requires a satisfying final
valuation. The regular-solution module independently obtains regular
subtyping from an accepted finite certificate, but alone did not reconstruct
pre-transformation constraints. This module applies that construction:

```lean
accepted_original_demands :
  ConstraintHistory graph ref birth first last →
  accepts graph certificate last.obligations = true →
  graph.Valid ∧ first.Satisfied graph
```

Here `first.Satisfied graph` is every original comparison interpreted in
`RegularSub graph`, the frozen all-finite-unfolding-depth semantics. No final
valuation, subtype model, transitivity law, preservation law, original-demand
solution or local-law package is an input. `accepted_original_joint` supplies
one postfixed relation covering both the original and final demands together.
Its concrete witness is `RegularSub graph`; this means one shared
interpretation, not uniqueness among all possible mathematical solutions.

The history is a concrete graph-indexed structural history, not an assertion
that the existing Rust solver already emits this history. It does not treat
regular graphs as finite-Term valuations and does not claim to subsume all
constructors of the earlier finite-Term history.

## Semantic facts proved from the existing graph interpretation

`NodeRel` is an auxiliary, syntax-directed relational description of the
existing `expandNodes` function. `nodeRel_iff` proves exact equivalence to
successful expansion with all child comparisons satisfied. Records retain
whole finite field lists, labels, optional bits and order; variants retain
whole finite alternatives, tags and payload arities/order. Function uses all
four ports, with argument and argument-effect reversed and result-effect and
result covariant.

`regular_trans` proves transitivity by induction on actual unfolding depth.
At every positive depth, both semantic premises force successful endpoint
lookups and compatible constructors. Consequently transitivity needs no
global graph-validity premise for already-related endpoints. The structural
list and four-port cases are proved, not imported as a semantic-model law.

`regular_refl` uses coinduction on existing diagonal references. It requires
`graph.Valid` and an actual lookup for the endpoint. Those are legitimate
well-formedness requirements: a missing or dangling reference cannot be
silently assigned a reflexive regular type. The main accepted-history theorem
obtains global validity from the final certificate's existing `checkGraph`;
reflexive history rules retain the relevant endpoint existence fact.

## Concrete operations and source correspondence

`ConstraintState` retains a list of kind/lower/upper comparisons and the
existing frozen `Occurrence` objects. `ConstraintStep` has these explicit
operations:

- Remove an existing reflexive demand, using the proved regular reflexivity.
- Replace a demand by its actual `expand graph pair` children. This includes
  leaf discharge and complete structural decomposition, without a generic
  premise saying the step is sound.
- Insert actual lower-to-row or row-to-upper obligations, retaining the rest
  of the store.
- Discharge a demand by replaying two opposite bounds actually present in the
  retained store. `replay_solution_iff` proves that this discharge preserves
  the whole solution set, using the derived regular transitivity.
- Replace a positive lower demand or negative upper demand by its rewritten
  endpoint, while adding exactly the traversal's emitted copy links and
  retaining the exact occurrence record.
- Add both equality directions for selected copies belonging to an actual
  retained occurrence, qualified by the frozen immutable-birth `Qualifies`
  predicate. Parent, child, kind, polarity, occurrence identity, origin and
  receiver are not regenerated or replaced.

`Extrusion` is a finite inductive derivation with three concrete rules:

1. An exact frozen `Copy` leaf emits its directed parent/child comparison.
2. An unchanged reference retains its actual endpoint lookup.
3. A structural node checks the actual `expand` result and recursively
   traverses its child comparisons. The emitted list is exactly the
   concatenation of those children's copy lists, in order.

`Extrusion.sound` proves the directed result from satisfaction of emitted
links. The constructor does not take the desired subtype result or an
arbitrary preservation law. Row-copy leaves form finite cuts around graphs
that may themselves be cyclic. This is a forward semantic structural
certificate; native levels, fresh allocation, memo reuse and the actual
extrusion traversal still need a correspondence proof.

`ConstraintStep.sound` proves every operation by cases, and
`ConstraintHistory.sound` composes the proven steps. The accepted-history
result immediately consumes the frozen `accepted_graph_valid` and
`accepted_demands_sound` results, so final interpretation existence is
constructed from the final finite check.

`copyLink_asConstraint` and `copyEqualities_asConstraints` prove exact equality
with the frozen finite syntax's `Copy.link` and `Copy.equalities` under the
explicit variable-constraint embedding. `comparison_interpretation` and
`holds_variable_store` prove the precise graph interpretation of that embedded
store. This is explicitly a variable/pointer interpretation; it is not a
claim that finite `Sub` equals regular `RegularSub` or that all finite-Term
constructors have been decoded.

`ConstraintStep.retains_occurrences` and
`ConstraintHistory.retains_occurrences` prove immutable event retention.
`accepted_retained_equalities` reconstructs both directions for every selected
actual copy, together with the rest of the store, after arbitrary subsequent
represented transformations. Qualification and actual membership restrict
the intrusion rule; backward solution reflection for equality insertion itself
only needs that the old constraints are retained. This is the implication from
new-state satisfaction to old-state satisfaction, not preservation of every old
solution after adding equalities.

## Exact structural renaming/quotient consequence

`renameNode` preserves all constructors and metadata while renaming only
kind-indexed references. `GraphRenaming source target names` is the explicit
lookup equation

```lean
∀ k identity,
  target.lookup k (names k identity) =
    (source.lookup k identity).map (renameNode names)
```

It covers missing lookups too. It is a strong concrete compatibility condition,
not an arbitrary semantic subtype-preservation assumption. Names may identify
references. `layer_rename` proves exact one-step semantic correspondence from
this lookup equation; `regular_rename` proves the all-depth equivalence.

`accepted_renamed_original` combines a finite source `checkGraph` success,
this exact graph compatibility, a source history, and acceptance of the
renamed final demand list in the target graph. It derives all original source
graph demands without a supplied model. The separate source validity check
is explicit and executable. This is not a claim that every native union-find
merge, equality class or extrusion quotient satisfies the lookup equation.
An actual native quotient decoder must prove that condition for any use of
this theorem.

## Checked concrete examples

- `cyclic_structural_extrusion`, `cyclic_history`,
  `cyclic_final_accepted`, `cyclic_original_solved`: a genuine shared cyclic
  graph with four-port Functions, finite records with required/optional
  fields, tuple children and variant payloads returning to the Functions.
  A structural extrusion emits precisely four copies, reversing both input
  ports. An actual retained occurrence supplies all four equality pairs.
  The final finite certificate derives the original demand. The example's
  origin and receiver are both zero, so birth qualification uses the valid
  reflexive paths; general history qualification uses the unchanged full
  induced-path predicate.
- `cyclic_missing_effect_rejected`: removing one required effect direction
  causes final acceptance to compute to false.
- `mixed_decomposition_history`, `mixed_decomposition_accepted`,
  `mixed_original_reconstructed`: actual four-port decomposition feeds the
  earlier mixed cyclic certificate and reconstructs its original root.
- `quotient_compatible`, `quotient_identifies_distinct`,
  `quotient_original_solved`: a concrete non-injective mapping identifies two
  distinct, identically labelled atom nodes and reconstructs the source demand
  from a single target comparison.
- `acyclic_original_absent`, `acyclic_original_reconstructed`: the original
  Function comparison is absent from the entire terminal certificate. That
  certificate contains only value/effect child pairs. The history theorem
  still reconstructs the original Function demand, demonstrating that final
  acceptance was not defined to assume the original conclusion.

All finite acceptance/rejection equations above are kernel computations,
not native execution or a trust bypass.

## Source map and exact open bridges

The governing sources and native ownership are unchanged from the frozen
regular-solution receipt `20261026-inference-regular-solutions.md`:

- `notes/theory/2026-10-13-intrusion-source-preservation-proof.md`: forward
  directed links, retained actual parent/copy equalities, same original source
  interpretation; no diagonal-lift/completeness claim follows from this work.
- Immutable birth-level correction and `Contracts.LevelPath` / `Qualifies`:
  qualification uses the source value reference graph and immutable birth
  levels, not mutable type-bound levels or an unrestricted global SCC.
- `2026-10-11-parreaux-simple-sub-proof-import.md` §§3–5: guarded recursive
  assumptions and the distinction between proof-only unifying interpretation
  and ordinary output coalescing remain in force.
- Native `term.rs`: full four-port Function, record optional metadata and
  finite variant payloads are represented in the structural fragment.
- `lib.rs` `SolvedModule::solve`, `run`, `finish`, `errors`: `Result::Ok` does
  not by itself mean no-error successful inference.
- `shadow_apply.rs` public `export`, `fresh_use`, selected-use/ownership and
  operation receipts: actual final no-error and admission/provenance checks
  remain the native-success boundary.
- `f5c_generalization.rs` recursive bounds and coalescing owners, plus legacy
  `finalize_generalization_draft_raw`: transaction completion or serialization
  is not already the required semantic decoder. In particular legacy Function
  serialization that substitutes empty effects is not a full four-port bridge.

The first still-open native bridge is: a real accepted public inference/export
path, including its final no-error/admission conditions, yields a faithful
represented graph, original/final demand lists, a concrete `ConstraintHistory`
and a finite certificate whose existing Boolean acceptance succeeds. The
actual native memo/cache/worklist and immutable occurrence data must supply
those objects. This proof certificate need not become a newly mandated
runtime validator, and no compiler behavior was changed.

The fixed graph in this theorem is the common interpretation of all history
references. Showing that an actual changing native allocation/merge trace can
be decoded in such a shared graph is part of that correspondence obligation.
Freshness, levels, source occurrence provenance and active-cache invariants
are not silently established by the generic structural history.

The next source bridge must reconstruct the unchanged original source-scoped
Call/effect judgment and joint witness from the actually generated demands.
This module proves neither native-to-history production nor that source
reconstruction. Generalization/independent-use regular interpretations remain
separate from the frozen finite-Term theorems.

Explicit represented limits: no union/intersection nodes or their cycles;
no unguarded aliases; no native open row tails, width/presence weakening or
complete variant admission; no general native recursive coalescing theorem;
no original Call/context strategy or quantifier/provider/guard coverage.
Cycles through represented structural field/payload references are supported.
The original full inference soundness, completeness/principality, termination,
progress and full-source/native correspondence roots remain unchanged/open.

## Verification and reproducibility

Owned isolated project: `/workspace/scratch/f98087c7ac1a/inference-regular-constraints/`.
Pinned native Lake:
`/workspace/scratch/e41512dd7957/toolchains/lean-4.35.0-linux/bin/lake`.
Lean 4.35.0, `LEAN_NUM_THREADS=1`, `-j1 -M1024`, one owned Lean process at a
time. Each call had an explicit 60-second process timeout. Eight focused calls
used approximately **52.8 seconds** total, within the existing 300-second
budget. No source changes followed the final build or audit.

| Log | Result |
| --- | --- |
| `check-01.log` | Exit 1: core imports lack `List.Forall₂`; replaced it with explicit recursive `ZipRel`, and repaired elaboration identifiers. |
| `check-02.log` | Exit 1: structural equivalence simplification, relation inference and projection equality elaboration. |
| `check-03.log` | Exit 1: nested variant relation needed its explicit kind-indexed relation. |
| `check-04.log` | Exit 1: constructor case used reserved `structure`; renamed constructor to `structural`. |
| `check-05.log` | Exit 0, 7.644s: complete semantic and backward-history core. |
| `check-06.log` | Exit 1: renaming equivalence needed unfolding of `renamePair`. |
| `check-07.log` | Exit 0, 7.568s: frozen full module and every example, clean diagnostics. |
| `audit-08.log` | Exit 0, 1.306s: complete originating-module exact-type/axiom audit. |

Commands:

```text
lake build YulangClosure.SimpleSubRegularConstraintSoundness
lake env lean -j1 -M1024 RegularConstraintAudit.lean
```

The audit enumerates actual originating-module theorem declarations,
including private and compiler-generated helpers, and rejects any project
axiom. All **169 theorem constants** passed, comprising **50 authored public
theorems** and **119 generated helpers**, with 169 matching begin/end receipts.
Every authored printed theorem type was inspected. Axiom sets: **43 empty**,
**83 `{propext}`**, **43 `{propext, Quot.sound}`**. The auditor allows only
`propext` and `Quot.sound`; there is no `Classical.choice`, `sorryAx`, project
axiom, unchecked native proof or kernel bypass. Source scan found no hole or
unsafe/bypass token.

| Evidence | SHA256 |
| --- | --- |
| `RegularConstraintAudit.lean` | `4e7c096bd759314b553af34ac69150c6e21e6845fe698d442ad089d498d889d3` |
| `audit-08.log` | `0e40ac4b14e9a6dcab3a19a3435a876b49a6039ba287a7487af635e8ed2d7559` |
| `check-07.log` | `356004804ba91637c9468a7c88416496ebbb78668d62379baa408e16563f4cbb` |

Source declaration map: regular semantic laws 12–213; frozen Copy/store
interpretation 216–265; concrete extrusion/history and main application
270–418; exact structural renaming and retained equality reflection 422–520;
cyclic, quotient and absent-original-certificate examples 524–657.

Writes stopped after this receipt. No owned Lean process remains running.
This packet is ready for fresh independent review and primary integration.
