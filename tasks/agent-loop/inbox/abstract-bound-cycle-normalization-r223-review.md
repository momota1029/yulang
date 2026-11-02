# R223 fresh adversarial review — frozen, primary transcription

Reviewer: `/root/r223_bound_cycle_review` (`compiler_referee`, read-only).
The reviewer returned the report in its final response; Luna transcribed it
here and normalized the axiom-group formatting. No reviewer edits, builds,
checkers, cache writes, tests, scratch files or Git operations occurred.

## Verdict

**PASS for the frozen incomplete structural packet; BLOCKING for completion of
the unchanged R223 gate.** No major or minor correctness defect was found in
the asserted structural theorems. The findings below concern missing
applications and invariants, not refutations of those theorem statements.

## Frozen inputs

| Input | SHA-256 |
| --- | --- |
| Contract revision 3 | `df9393be7ea3432ca8cf28af13610fdded5430b20b6fdf0f49668e2b83edf980` |
| Lean revision 2 | `65335f3b8c6834e1e1cd34429a8fd7330162648a62d532c3a45f44305b255aee` |
| Proof handoff revision 2 | `82a30aaea95f67830f8459932c8240064831cacaba94d17188d192d27f4abcc0` |
| Independent falsifier | `e7a5d0e5ae8340020e9f7664e108fe1a74416a4da62307db2ac5595523fb7eed` |

The review checked the authoritative inference principles, immutable Value-birth
correction, original A/B claim, paper §§3.5.1 and 5.3, structural `Term`/`Sub`,
finite reachability, generalization, owner-local `Published`, R212 storage and
operation, and original `SourceProblem` roots.

## Findings

### BLOCKING — Generic owner-local shared factorization remains open

Locations: `AbstractBoundCycleNormalizationR223.lean:418,585,731,819,835`;
`SimpleSubScopedPublication.lean:93,154,281`; falsifier lines 93–156.

`actual_fresh_use_transport` is an algebraic pullback equation. It does not
construct reverse solution factorization for arbitrary owner-local publication.
`mixed_level_two_use_factorization` assumes complete-store copying;
`closed_publication_joint_factorization` derives needed premises from actual
`Published` constructors for one concrete closed fixture.

Two independent model derivations expose missing premises:

- **NonGeneric/capture closure:** equal levels do not repair a stopped
  nonGeneric owner. With `x.upper=[y]`, `y.upper=[x]`, levels `[1,1]`,
  nonGeneric flags `[true,false]`, root `y`, boundary 0 and one use, numeric
  bound closure holds but only `copy(y)<:x` is published. Assigning anchor
  `a∪b` and copy `a` defeats joint factorization.
- **Query coverage:** even numeric and nonGeneric dependency closure do not
  constrain copies of an unreached SCC. With empty roots, base clauses equate
  original `x,y`, while fresh copies may receive distinct atoms. Quotienting
  merges their fresh images and cannot factor both assignments through one
  normalized valuation. An isolated root can be added without reaching the SCC.

These derivations follow existing `Published`, `Reach`, `fresh` and
`captureGuard` definitions. They are not checked new Lean declarations or
source-qualified failures. The first violates nonGeneric closure; the second
lacks query coverage.

**Required closure:** derive actual capture/allocation/representative coherence
and dependency closure, plus source-derived coverage of queried fresh classes;
then prove generic joint factorization under one shared anchor valuation. Do not
replace `Published` with complete-store copying or narrow the original source
domain.

### BLOCKING — Physical extraction is not connected to lawful solver state

Locations: `AbstractBoundCycleNormalizationR223.lean:349–425`;
`AbstractSimpleSubCore.lean:135–195`.

Extraction visits both bounds of every physical row, including duplicate
representatives. But `resolve` performs one lookup with identity fallback. No
accepted-history invariant establishes representative validity/idempotence,
retained-store correspondence, per-kind allocation or metadata coherence.

For example, with one Value row at level 1, two Effect rows, and malformed
Value representatives `[0,0]`, `scopeSize=2`; nonexistent Value row 1 has
default level 0 and lowers the computed class level. This is allowed by
arbitrary `CoreState` data and does not contradict the stated theorems, whose
scope and fixed-point premises are explicit.

**Required closure:** derive per-kind allocation and representative invariants,
physical-bound/retained-constraint correspondence, and metadata preservation
from actual solver transitions. Apply the SCC and class-level results through
those invariants.

### BLOCKING — Guarded readout remains unconstructed

Locations: `AbstractBoundCycleNormalizationR223.lean:29–40,277–285,840`;
falsifier lines 158–172; `SimpleSubLatticeCertificates.lean:73,113`.

The construction handles variable-to-variable cycles in the structural
constraint model: it retains a free parameter and removes reflexive variable
clauses. It does not eliminate every unguarded lattice cycle. A level-0 row
with upper `union(var 0, atom 0)` contributes no variable edge; that structural
bound survives normalization. The corresponding R212 partial insertion passes
allocation and level checks. Literal negative unifying coalescing still has a
lattice-only recursive path. No theorem connects that recursive syntax to a
guarded decoder.

**Required closure:** construct the Fig. 12/readout correspondence and required
guarded interpretation or justified normalization, preserving free parameters
and structural bounds. This packet supplies a prerequisite, not guarded
readout or an original parent theorem.

## Surviving theorem scope

- `quotient_exact_scc` requires bounded store endpoints and in-scope query
  coordinates; finite closure does not claim to enumerate all naturals.
- Both solution directions are constructive. Normalized solutions pull back
  by composition; an original solution supplies the normalized class valuation.
- `all_term_factorization` covers every structural term, including later client
  coordinates, without bounding the term or valuation values. Function
  variance is handled at all four ports, including both effect ports.
- Normalization preserves order and multiplicity of retained clauses and
  removes only syntactically reflexive variable clauses. Structural labels,
  optional bits, tags, payloads and ports survive.
- Self-upper and upper-only fixtures identify actual R212 partial-operation
  outputs. Other states are data discriminators, not complete accepted runs.
- Closed and stopped mixed-level layouts have the same extracted constraints
  but different publication behavior, exposing owner information lost by
  store extraction.
- The Boolean observation refuting `Sub(a∪b,a)` respects every existing `Sub`
  constructor. It does not treat rigid atoms as substitution parameters.

## Checker and axiom evidence

The primary's bundled checker exited 0 for all 65 unique authored declarations
in the frozen source. It found no unapproved axiom, project axiom, `sorryAx`, or
missing type. The reviewer did not rerun Lean. No audit log file was retained;
the exact per-declaration groups below were supplied by the primary from a
fresh checker run.

All names have prefix `YulangClosure.SimpleSub.BoundCycleR223`.

**No axioms — 4:** `Equivalent.refl`, `Equivalent.symm`, `Equivalent.trans`,
`subst_equivalent`.

**`[propext, Quot.sound]` — 27:** `connected_trans`,
`quotient_eq_of_connected`, `quotient_idempotent`, `quotient_canonical`,
`quotient_eq_iff`, `edge_endpoint_bounds`, `reach_complete_in_scope`,
`quotient_exact_scc`, `edge_solution`, `reach_solution`, `connected_solution`,
`all_term_factorization`, `normalized_solution_iff`, `solution_pullback`,
`solution_pushforward`, `solutions_and_all_terms`, `retained_clause`,
`factorization_after_substitution`, `physical_row_retained`,
`actual_class_level_le`, `actual_class_minimum_at_fixed`,
`actual_anchor_preserved`, `actual_fresh_use_transport`, `self_upper_all_terms`,
`mixed_bound_levels_not_closed`, `fresh_capture_without_nonGeneric`,
`closed_publication_joint_factorization`.

**`[propext]` — 34:** `connected_refl`, `connected_symm`, `classMinimum_le`,
`classMinimum_member_le`, `classMinimum_selected`, `quotient_future`,
`quotient_le`, `quotient_in_scope`, `quotient_connected`,
`clauseEdge_solution`, `trivialVariable_solution`, `filter_solution`,
`quotient_substitution`, `self_upper_actual`, `self_upper_quotient_free`,
`upper_only_actual_and_preserved`, `two_cycle_free_external_preserved`,
`duplicate_physical_bounds_and_levels`,
`recursive_function_all_ports_and_kinds`, `mixed_level_shared_anchor`,
`mixed_use_store_exact`, `mixed_before_value`, `mixed_before_effect`,
`mixed_physical_value`, `mixed_physical_effect`, `mixed_after_fixed`,
`mixed_level_two_use_factorization`, `sub_observation`, `union_not_left_atom`,
`stopped_publication_separated_satisfies`,
`stopped_publication_no_joint_factorization`,
`closed_mixed_same_constraints_and_levels`, `closed_mixed_bound_levels`,
`closed_publication_supplies_mixed_store`.

Zero declarations use `Classical.choice`. Source inspection found no authored
proof holes or checker bypasses. The earlier rejected elaboration environment
is historical failure evidence, not evidence about the final dependencies.

## Classification

No theorem is applied to a concrete original `SourceProblem`; mutual structural
`Sub` supplies neither `sameScoped` nor original `instanceOf`.

**Original parent delta: 0. Roots: 0/4. Packages: 0/5.**
R223 completion and production promotion remain blocked. The packet is reviewed
incomplete research, with all blockers above preserved.
