# R271 primary handoff — Tuple Value-reference graph

Sprint contract: `tasks/agent-loop/sprints/tuple-value-reference-graph-20261021-r271.md`.
Baseline: `37c1745bc8716e4b2bb4a534aaaa435af75dae84`.
Status: primary-only implementation checkpoint; no independent review.

Parent: unchanged Yulang2 playground samples and proof-backed compiler/evaluator behavior. R270 fixed candidate constraint traversal, capture, and FreshUse; R256 identifies that source Value-reference traversal still omits Tuple. This work repairs that missing SCC/intrusion input.

Exact write paths: `crates/yu-solver/src/candidate_value_graph.rs`, this contract, `notes/theory/2026-10-21-r271-tuple-value-reference-graph.md`, this inbox, and primary-owned `tasks/agent-loop/current.json`.

Success/falsifier: direct/nested Tuple expression references reach all child Names with original Value identity and owner; nested block initializers keep their local owner; source traversal order is retained; Tuple-only graph construction does not invent SCC changes. Missing/reowned references, flattened nested fragments, changed unrelated SCCs, or unaccounted adjacency are falsifiers.

Checks planned within the 600-second envelope: focused source Value-graph tests and tuple-filtered solver tests, static sprint check, `git diff --check`. These are finite implementation evidence only. Public types/runtime, imports, host continuation, R149 samples, general source/native proof, A/B, soundness, principality, and production remain OPEN.
