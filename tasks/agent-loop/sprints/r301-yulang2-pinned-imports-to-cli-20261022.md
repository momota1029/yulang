# Sprint R301 — unchanged Yulang2 samples through pinned imports and CLI

Status: CHECKPOINTED_UNREVIEWED, solo primary; no independent review or theorem closure is claimed.
Branch / baseline: `research/simple-sub-intrusion` / `6857f1eb7` (`Test imported identity at distinct concrete types`).
Authority: user's continuing R149 implementation-and-proof goal; Authoritative `notes/design/2026-10-20-r149-types-console.md`; unified design §§4.1–4.5, 6, 9–10; proof companion §§3.1–3.6, 4.5, 7.1–7.5; top-level Simple-sub principles. The user prohibits subagents. Work is solo; no dispatcher or child is started.
Parent gate: the exact unchanged 142-byte Types and 92-byte Console templates, their pinned 40-file Yulang2 standard-library closure, public type observations, whole-module execution and exact ordered writes. R149 and all source/native, principality, general theorem, review and production gates remain OPEN.

## Outcome

Connect the pinned source imports to the ordinary playground CLI path so both exact R149 templates can be inferred and run in source order. Resolve imports by parse-owned use leaves and exact `SourceExportId` provider declarations; lower the required original provider HIR artifacts; use one candidate collection/session and its ordinary FreshUse maps; preserve source-selected role/method behavior; run the module schedule and handle only the authentic `std::io::out::write` operation. Do not rewrite samples, extract prefixes, inject `main`, recognize `say`/`println`/`show` by spelling, or bypass source providers.

## Fixed observables and falsifiers

- Types source SHA-256 `8cbfb97a8df8e5dc4916313769c39a84626ae124f91f8a9672f1ad8b866f98e6`: public types for polymorphic `id`, `answer: int`, `name: str`, `pair: (int, str)` and one captured payload `(42, Yulang)\n`.
- Console source SHA-256 `ada6174d8795ddb10a8c533c812b771d9dddced816762e0e246022467499a076`: ordered payloads `hello from Yulang\n`, then `3\n`.
- Library closure: the exact 40 pinned sources in the R149 manifest, retaining each original relative path and blob identity.
- Each template must run through the ordinary CLI test entrypoint. Candidate graph success alone, or a sample with `pair.say` removed, is diagnostic evidence only.
- Falsifiers: changed source bytes; spelling-based method/host selection; provider HIR or source identity omitted; imported use bypassing FreshUse; ambiguous or stale owners accepted; missing Type/Console output or wrong order; partial output after failed inference; `pair.say` failing before the authentic tuple Display implementation is selected.

## Before evidence

R300 added `CandidateInference::solve_modules` and exact imported binding-to-provider routing. Its ordinary candidate test now applies one imported `id` to `42` and `"Yulang"` in the same session and observes separate FreshUse rows plus `IntPositive`/`StrPositive` bounds. This does not load the pinned closure in the playground or execute either R149 sample. On the current CLI, the exact Types input fails at collection (`Collection(ComponentIdentityExhausted)`); the diagnostic variant without its final `pair.say` expression succeeds and exposes an ordered `(int, str)` tuple graph. Source inspection identifies `LocalSourceForm::FieldTail` as an explicit unsupported branch.

## Implementation boundary

- Add exact source-import construction over the pinned 40-module index set, including named, aliased and glob use leaves, ambiguity and local shadowing.
- Build the required provider HIR set with original module/file identities and feed it with the consumer to the existing single-session candidate path.
- Connect the actual `Display` role and selected tuple implementation to `pair.say` only after relevant types are known; retain the selected provider evidence.
- Add a whole-module CLI run mode over the retained mixed source schedule and an identity-checked host implementation for the exact `out::write` declaration. Publish Types/output only after accepted inference and successful execution.
- Add ordinary CLI integration tests over the unchanged sample bytes, plus focused import/selection falsifiers. Keep proof claims conditional on the exact implemented path.
- This sprint's CLI outcome does not close Web parity, broader Yulang2 examples, general source/native soundness, principality or production. Those remain in the unchanged parent goal.

## Exact leases

`crates/yu-hir/src/module.rs`, `crates/yu-hir/src/module/source_exports.rs`, `crates/yu-hir/src/shadow.rs`, `crates/yu-solver/src/lib.rs`, `crates/yu-solver/src/candidate_source.rs`, `crates/yu-solver/src/candidate_effect.rs`, `crates/yu-solver/src/candidate_scheme.rs`, `crates/yu-solver/src/shadow_apply.rs`, `tools/inference-playground/src/pinned_stdlib.rs`, `tools/inference-playground/src/lib.rs`, `tools/inference-playground/src/runtime/program.rs`, `tools/inference-playground/src/runtime/machine.rs`, `tools/inference-playground/src/runtime/mod.rs`, `tools/inference-playground/tests/cli_yulang2_samples.rs`, this contract, `notes/theory/2026-10-22-r301-yulang2-pinned-imports-to-cli.md`, and Luna-owned `tasks/agent-loop/current.json`. No wildcard or directory lease.

One primary process; one Cargo/build/test process at a time; no background work. Cap 1800 seconds for this sprint with no carryover. The known solver suite failures from pre-R300 history are tracked as unresolved; do not attribute or hide them. A new failure in the R301-focused owner path must be isolated before continuing.

## Checkpoint

The parse-owned import API and pinned candidate-world scaffold are committed in `e9ef6bacb`. The focused HIR alias/glob test and `cargo check -p yu-playground` pass. Exact unchanged Types execution is blocked before candidate collection because authentic pinned Yulang2 method bodies produce parser recovery; `std::int` imports the recovered public `std::text::str::str` declaration, and export resolution refuses that owner. No recovery was bypassed.

## Proof and stop boundary

Reuse the proof companion's finite source/use correspondence, exact FreshUse maps, common-context preservation and runtime operation obligations only where their premises match these constructors. Tests establish executable correspondence for these samples, not the theorem. Keep Types/Console acceptance, public types, effect residuals, role/member selection, whole-module order, host payloads, failure atomicity and output capture tied to the same HIR/source identities. If a bridge requires a new language decision, retain the exact source counterexample and continue on independent authorized work; do not guess a semantic fallback.
