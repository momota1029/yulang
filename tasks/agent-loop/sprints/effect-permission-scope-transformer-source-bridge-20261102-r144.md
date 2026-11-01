# Sprint R144 — connect scoped effect transformer to its Lean law

Status: admitted by Luna under the continuing Yulang effect-hygiene goal.
Sprint ID: `EFFECT-PERMISSION-SCOPE-TRANSFORMER-SOURCE-BRIDGE/20261102-R144`.
Baseline: `77cf25096f8271590b89380fc988d7e2dd11e7d6` (`yulang3`).

## Original goal and scope

Original parent remains `YulangClosure.SourceProblem.InferenceSoundness`, with its unchanged all-supported-source quantifiers and shared scoped witness. Effect hygiene H and A/B remain OPEN. R143 established kernel-checked table-local permission projection facts only; it did not establish a Rust/native bridge.

The admitted bounded outcome is a source-level regression candidate for the existing private `ScopeTransformer` implementation. It shall compare the Rust composition/remap operations against direct sequential execution and map those laws to their clean native callers. This is validation coverage, not a production behavior change, theorem closure or semantic adoption.

## Frozen inputs and authority

- `crates/yu-solver/src/candidate_scope.rs`: 11,060 bytes, SHA-256 `9fdb36b4bbd66d702fbd3fcfaf593bfbc5dce0c52ff3252442aeb998bbb52c2a`, Git blob `c06f725510c1f35ab89020de86d5846e9fd0a3ad`.
- `crates/yu-solver/src/candidate_context.rs`: SHA-256 `a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905`, blob `9d24adc6cec7a3df8072b543e326a20afd017ea5`.
- `crates/yu-solver/src/candidate_source.rs`: SHA-256 `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49`, blob `b43f37f4cca246a072b73329aed84e89aef4ebe1`.
- `notes/theory/lean/YulangClosure/NativeScopeTransformer.lean`: SHA-256 `68f37763bcaab831ec6248a28144e7b76ede42b7813681850f7c67b0d8df10f6`, blob `8c975d2e549e9c5f358c036d1e8ac1d079f99cdd`.
- Authority: `notes/design/2026-10-15-compose-scoped-effect-release.md` and `notes/progress/2026-10-26-whole-metatheory.md` §2. No source semantics are reopened.

At admission all four frozen input paths were clean and unleased. Recheck `candidate_scope.rs`, `candidate_context.rs`, and `candidate_source.rs` against these exact bytes before applying any handoff. Dirty/quarantined files remain untouched: `candidate_effect.rs`, `candidate_receiver.rs`, `candidate_scheme.rs`, `shadow_apply.rs`, and the runtime machine/receiving files.

## Success evidence and exact work

The implementation worker may add one bounded `#[cfg(test)]` module only to `crates/yu-solver/src/candidate_scope.rs`; no production definitions may change. Use an independent primitive oracle over `BTreeSet` rather than copying `Missing` predicates or the canonical merge implementation. Cover:

- `evaluate(first.then(second), initial)` equals sequential `evaluate(second, evaluate(first, initial))` for a small exhaustive finite set of initial states and short `stamp`, `protect_body`, `release` sequences;
- order distinctions including stamp→protect, protect→stamp, protect→release, and release→protect;
- release tombstones, unsorted and duplicate initial inputs/protections, and unrelated pre-existing protections;
- injective scope/input renaming commuting with evaluation, separate scope-map and input-map collision rejection, and one map-closure call per distinct support ID.

Finite coverage is regression evidence only, not a universal proof. Keep the loop bounds and allocations small and deterministic.

The source/proof lane maps the algebraic laws to the actual callers in `candidate_context.rs`/`candidate_source.rs`, including argument stamping, result protection, composition order and remapping. It must state the first missing premise for authentic caller-level injectivity or source/native behavior; do not invent one.

## Fixed limits and stop conditions

No Cargo, Rust compiler, build, test execution, Lean, Lake, benchmark, cache, generated output, scratch file, environment, target directory or worktree is authorized. The test candidate must therefore be labeled uncompiled and unexecuted. User has complained about WSL storage; do not create any build/environment artifacts.

No production semantics, public API, dependency, manifest, dirty/quarantined path, or Lean theorem may change. Stop on frozen-hash mismatch, a contract/code disagreement, a concrete counterexample outside the bounded edit, or inability to keep the oracle independent.

The Luna/high implementer has at most 600 seconds and the exact source plus source handoff leases below. One source/proof mapper has at most 300 seconds and only its handoff path. Both finish and freeze before the fresh reviewer starts. Fresh `compiler_referee`, at most 240 seconds, inspects the frozen Rust source, oracle independence, coverage and caller handoff; no compilation is available. Total sprint envelope: 1,320 seconds, at most two concurrent producers, no Astra, no heavy processes.

## Parent application and remaining gates

If independently reviewed, the Rust algebraic-source regression risk is reduced for the enumerated finite cases and the caller composition is documented against the existing Lean law. Source/native identity, actual allocation behavior, allocation-failure paths, whole-language effect hygiene H, the original A/B obligations, `SourceProblem.InferenceSoundness`, principality, termination and production remain OPEN. The next discriminating step remains authenticated source/native correspondence or a concrete caller counterexample.

Luna alone owns integration, record updates, explicit staging, commit and non-forced push after inspecting the full outbound range. A reviewed source-only checkpoint may state prominently that it was not compiled or executed.
