# Sprint R300 — artifact-preserving multi-HIR imported use

Status: RUNNING, solo primary; no independent review or theorem closure is claimed.
Branch / baseline: `research/simple-sub-intrusion` / `16dca3eb93f7ddcd48a7b222e14abaa496ec0048`.
Authority: user's active R149 implementation-and-proof goal; Authoritative R149; top-level Simple-sub principles; unified design §§4.1–4.5, 6, 9 stages 2/4/6; proof companion §§3.1–3.6 and 7.1–7.5. The user explicitly requires no subagents. No dispatcher or child process is started.
Parent gate: R149 Types/Console with unchanged source bytes, public types, ordered host output, and runtime behavior. R149, source/native soundness, principality, and production remain OPEN.

## Outcome

Add a candidate-only multi-HIR collection path for one consumer and its exact provider HIR artifacts. Preserve every `HirOccurrenceId` and `DefinitionRootId` in its original artifact; share one collection token, component arena, SCC plan, and `InferenceSession`. Resolve imported binding identities only from authenticated `SourceExportId` plus exact provider declaration source key/range. Represent imported uses as ordinary `DefinitionUse`s so the existing same-session graph/FreshUse route owns them.

Success evidence reached so far: provider and consumer independently lowered into distinct HIR artifacts enter one batch/session; both original artifacts are accepted while a foreign HIR is rejected; the same imported identity is applied to `42` and `"Yulang"` in one session, producing `IntPositive` and `StrPositive` graph bounds through distinct FreshUse-local rows. This fixture has no nonlocal provider anchor, so imported-anchor sharing is still untested. The single-HIR shared-anchor construction remains covered separately. Imported binding identity comes from the exact SourceExportId provider declaration, with no spelling fallback.

## Implementation boundary

- Extend candidate collection and solved ownership queries to retain multiple HIR artifacts without flattening artifacts or re-minting IDs.
- Add exact import-to-provider binding resolution using the already authenticated source export owner route.
- Permit candidate preflight only for imported IDs resolved by that exact map; unresolved where/role obligations remain rejected and retained obligations are not dropped.
- Add focused regression coverage and run the relevant solver/playground tests within one Cargo process at a time.
- Keep this candidate-only. Do not publish closed schemes through a new independent solver, claim R149 completion, narrow accepted source behavior, or turn role inventory into selection.

## Exact leases

`crates/yu-solver/src/lib.rs`, `crates/yu-solver/src/shadow_apply.rs`, `crates/yu-solver/src/candidate_source.rs`, `crates/yu-solver/src/candidate_scheme.rs`, `crates/yu-solver/src/candidate_context.rs`, `crates/yu-solver/src/candidate_effect.rs`, `crates/yu-solver/src/shadow_apply/local_source_observation.rs`, this contract, `notes/theory/2026-10-22-r300-multi-hir-imported-use.md`, and Luna-owned `tasks/agent-loop/current.json`.

Legacy UNKNOWN identities and their quarantined board lease remain untouched. One primary process; one Cargo/build/test process at a time. Sprint cap 1800 seconds, no carryover, no background work.

## Proof and falsifiers

The design proof obligation is artifact preservation plus ordinary `DefinitionUse`/FreshUse reuse, not a claim that passing tests proves general scheme preservation. Keep the source-to-native and R149 parent gates OPEN. Falsify the construction if IDs are flattened, any owner query authenticates against the consumer HIR only, provider bounds are absent from the shared session, imported use bypasses FreshUse, a local identity leaks across uses, a present nonlocal anchor is freshened instead of shared, or any unverified owner is accepted. The current imported-use fixture does not exercise a nonlocal anchor.

## Stop boundary

Stop this slice if candidate collection cannot retain owner HIR selection without losing source identity or introducing a disconnected second solve. Record the exact owner query or import constructor still lacking an authenticated bridge. Commit and push only a coherent checkpoint from the inspected baseline; leave the worktree clean.
