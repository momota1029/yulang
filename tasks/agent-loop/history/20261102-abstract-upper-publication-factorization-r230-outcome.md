# R230 outcome — operational owner-local publication factorization

Status: **CLOSED, reviewed structural result**. Baseline HEAD:
`9137e14caa418cd3f686fc892b9cea9502a70b5f`. Contract revision 1 SHA-256
`38139890a715aa7c11a8a788d04ee442696c7755a38c7401988ad6201d3d5ef3`.

## Result and exact boundary

The checked theorem
`YulangClosure.SimpleSub.UpperPublicationR230.terminal_solution_factorization`
constructs a single diagonal valuation that satisfies owner-local publication
and R223's normalized target, preserves inactive allocated anchors, and
factorizes each requested allocated query under every use. It derives closure,
SCC capture uniformity, and computed query roots from R229's actual successful
upper-insertion histories. The actual self-upper and upper-only histories are
instantiated. Both kinds, all four Function ports, labels/optional flags,
tuple ordering, variants, unions/intersections and constants remain covered.

Its premises are `inputValid`, an R229 successful upper-insertion `History`,
terminal empty pending work, `problem.termAllocated query = true`, and a
satisfying valuation for the original abstract constraints. The allocated
query premise is necessary for diagonal substitution to preserve the query;
arbitrary unallocated queries are excluded. The theorem does not assume
publication satisfaction, stopped closure, SCC capture uniformity, root
coverage or a shared valuation.

Fresh independent review: **CLEAN within the explicit structural,
allocated-query scope**, with no blocking, major, or minor finding. Reviewer
receipt is frozen at
`tasks/agent-loop/inbox/abstract-upper-publication-factorization-r230-review.md`,
SHA-256 `2b70dd2260446a9334c09f6641e341924dd3ef7c96cc56dbc6e9e4b780d7c85e`.
The reviewer independently confirmed the allocated-query boundary and native
exclusions. Reviewer ran no Lean/build/test/axiom check; Luna's separate
verification below supplies that evidence.

## Primary verification

Pinned native toolchain: Lean/Lake 4.35.0, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. Focused command:

```text
lake build YulangClosure.AbstractUpperPublicationFactorizationR230:olean
```

The final bundled checker rebuilt the exact final source and checked all 51
authored theorem types and complete axiom lists; exit 0. Axiom groups:

- `[propext, Quot.sound]` (6): `owned_clauses`, `owned_view`,
  `subst_equivalent_vars`, `use_guard_same_snapshot`, `diagonal_fresh`,
  `diagonal_fresh_term`.
- `[Classical.choice, Quot.sound, propext]` (37): `owned_upper`,
  `owned_bounded`, `bound_levels_closed`, `nonGeneric_false`, `captured_eq`,
  `stopped_closed`, `edge_level`, `reach_level`, `connected_levels`,
  `class_levels_same`, `capture_class_uniform`, `mapped_bound_levels_closed`,
  `mapped_stopped_closed`, `publication_base`, `edge_bound`,
  `capture_backward`, `path_publication`, `physicalClass_eq`,
  `class_connected`, `equal_classes_connected`,
  `reachable_class_factorization`, `query_factorization`, `reach_same_class`,
  `mapped_reach_lift`, `mapped_owner_reach`, `reached_term_factorization`,
  `publication_pushforward`, `mapped_normalized_base`, `publication_pullback`,
  `pullback_query`, `operational_publication_factorization`,
  `class_minimum_level`, `publication_diagonal`,
  `terminal_solution_factorization`, `terminal_publication_pullback`,
  `self_upper_application`, `upper_only_application`.
- `[propext]` (8): `query_covered`, `bound_clause_covered`, `use_lt_count`,
  `normalized_roots_computed`, `diagonal_anchor`, `diagonal_base_term`,
  `self_upper_history`, `upper_only_history`.

No `sorry`, `admit`, `axiom`, `unsafe`, `debug.skipKernelTC`, or `native_decide`
appears in the proof file. The checker is theorem/type/axiom evidence for this
module, not source-wide inference closure. No full project build or tests ran.

The only cache touched was the pre-existing
`notes/theory/lean/.lake/build`: baseline 132,786,132 bytes; final 133,953,489
bytes; growth 1,167,357 bytes, below the authorized 67,108,864-byte cap. No
environment, worktree, project copy, or cache directory was created.

## Source/native and parent application

The independent native owner review is `NO_SAFE_CODE_SLICE`. Native capture
uses current representatives and extra interface/evidence roots; FreshUse
re-resolves representatives, combines stored locality with live eligibility,
and reuses a first representative image. No correspondence was established
from these operations to R229 histories. Representative changes, eligibility
coherence, extra effect evidence, source witnesses, and self-pair elision stay
open. No Rust/Cargo/tests ran.

**Original parent delta: 0. Roots: 0/4. Packages: 0/5.** The result does not
instantiate `SourceScopedCoverage`, the same-scoped source witness,
`InferenceSoundness`, `PrincipalCoverage`, principality, or termination.
R230 replaces R223's fixture-only owner-local factorization with an operational
structural theorem, but the source-generated-history/readout bridge to the
unchanged parent is still open.

## Frozen inputs and next direction

- Proof: `notes/theory/lean/YulangClosure/AbstractUpperPublicationFactorizationR230.lean`,
  SHA-256 `ee16a4e68bb6357a51877a83e78239db08a0789eecd090f387760db2c2632a50`.
- Proof handoff:
  `tasks/agent-loop/inbox/abstract-upper-publication-factorization-r230-proof.md`,
  SHA-256 `51cd2e92e40dd1a7545e539aa9adc30eae8fae3e2991efcebb69d550ad494848`.
- Native owner handoff:
  `tasks/agent-loop/inbox/abstract-upper-publication-factorization-r230-owner.md`,
  SHA-256 `686d767736c3a813afbd0410fefdb1b9c6b60ea42b1deeaf60ab369a40cfb302`.
- Independent review: the path/hash above.

The dispatcher recommends R231 attack the literal edge of the unchanged
`InferenceSoundness` root: derive the original literal constraint/readout
equation from independent generated Value/Effect clauses, then apply it to
the same literal, descriptor/value/root/event and original scope/witness. Reuse
the adopted all-payload L1 rule and R220's exact atom/bottom rigidity, while
keeping synthesis and written-target ports distinct and retaining all
contextual-effect and checking obligations. Do not assume `LiteralAtom`, a
source judgment, or the desired readout. The R213 model-conformance activation
gate remains binding: Luna must first construct a derivation-backed equation
in the original carriers and obtain fresh conformance review; any genuinely
open semantic equation is frozen as `MODEL-INCOMPLETE`, with no conditional
proof packet. This is the next direction, not a claim that the parent is now
closed.

Dispatcher: `/root/r230_boundary`, read-only result; no file writes. R230 proof
and owner workers stopped; reviewer stopped after returning its receipt.
`python3 tools/agent_sprint.py check` passed (static consistency only).
