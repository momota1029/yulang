# Inference soundness: source-grounded incremental proof work

## Goal, authority and ownership

The user's continuing instruction explicitly prioritizes type-inference
soundness and authorizes small commits and pushes along the way. Initial
baseline: `0f6346a2de0a8bff863f41d487eb4b29cf8fb5f3` on `yulang3`.
The original full source theorem remains the one in
`docs/yulang-whole-proof-closure-ja.md` §1 and
`SourceProblem.InferenceSoundness`; no smaller component theorem replaces it.
The inference top-level principles and the authoritative 2026-10-24 immutable
Value-birth/induced-SCC correction govern the work.

This is an isolated primary-owned checkout. Foreign R63/UNKNOWN leases,
`tasks/agent-loop/current.json` and the reserved `YulangClosure.lean` remain
untouched. Only the primary stages, commits and pushes exact reviewed paths.
Generic workers use the repository proof/review role instructions; effective
custom-role/model execution is not inferred from role names. All are leaves.
Each coherent proof receives one non-author semantic review, bounded pinned
Lean checks and full originating-module type/axiom inspection. Rust corrections
to adopted semantics additionally require focused tests and independent review.

## First checkpoint: the actual birth-induced qualification contract

`YulangClosure.BirthLevelSCC.finite_helper_qualifies_iff` proves that executable
finite eligibility on the filtered helper graph is equivalent to the unchanged
`Contracts.Qualifies` on semantic Value incidence. Its local helper invariant
requires only that edges entering a helper preserve its actual planning level.
Whole-path projection/filter commutation is derived, not assumed.

The proof preserves raw cross-level references, includes singleton SCCs, and
rejects both a cross-birth cycle and equal-birth endpoints whose connecting
path requires a different-birth intermediate. The latter shows why comparing
endpoint births after one global SCC computation is insufficient.

The finite reference algorithm is a Warshall specification. Native Kosaraju
correctness, actual source births and exact incidence remain separate owner
obligations. Qualification does not establish lawful equality publication,
source-scoped coverage, principal inference or the inference-soundness root.

Frozen source SHA-256:
`2c76b82d4dc85a4bf4c122731ba014b07df4c863ad679e9a795a57e6546243f0`.
Fresh isolated Lean 4.35.0 checking accepted all 32 named theorems and all
57 module-originated theorem constants: 37 empty axiom lists, 19 with only
`propext`, and one generated congruence theorem with only `Quot.sound`.
The complete source, all printed types/axioms and input hashes received a
CLEAN non-author review. No new warning or unapproved axiom occurs.

- [Proof handoff](../../tasks/agent-loop/inbox/20261026-inference-birth-scc-proof.md).
- [Independent review](../../tasks/agent-loop/inbox/20261026-inference-birth-scc-review.md).

`InferenceProofs.lean` is an additional default-build glob, leaving both
previous roots intact. `AuditInferenceProofs.lean` enumerates exact originating
modules, rejects project axioms, requires the named application roots and checks
all private/generated theorem constants. Reproduce from `notes/theory/lean`:

```sh
lake build
lake env lean -j1 -M1024 AuditInferenceProofs.lean
```

The integrated default build passed **60 jobs**, exit 0 (1.536 seconds with
unchanged dependencies cached). The final complete audit passed **57** records,
exit 0 (1.487 seconds), log SHA-256
`f883ec8d08d9637b1c8c8c35aa49f7a05b1def8f7329a81753d158b940811b16`.
An initial audit elaboration failure from an unannotated mutable counter was
repaired by giving it the intended `Nat` type; both logs remain in task scratch.
No proof source changed for that audit-script repair.

## Current critical path

The native graph still used global SCC qualification at the initial baseline;
the existing nested loop/helper fixture encoded that superseded expectation.
Actual source planning assigns the outer definition birth 1 and nested local
initializer birth 2. The accepted rule makes both reciprocal events
nonqualified. This is an evidenced qualification/coverage mismatch, not by
itself a proof of unsound acceptance: faithfully retained equality constraints
restrict the solution set.

The constructive forward-soundness lane therefore separately targets the
one-sided extrusion links, concrete retained-constraint transformation, and
solution pullback through quotienting and finite independently freshened uses.
A successful native return must still supply an actual solution, and generated
constraints must reconstruct the original source judgment with the same scope
and shared witnesses. Complete source/Call/effect interpretation, recursive
solution existence, actual occurrence attribution and general native trace
correspondence are still OPEN; this checkpoint supplies none of them by
assumption or reclassification.
