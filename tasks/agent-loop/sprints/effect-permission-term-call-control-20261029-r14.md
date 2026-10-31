# Sprint EFFECT-PERMISSION-TERM-CALL-CONTROL/20261029-r14

Status: admitted by Luna under the unchanged ongoing Simple-sub inference/executor goal, following R13 `CLOSED_COMPLETE_CONDITIONAL` and sprint-end selector consultation.

Baseline: R13 connected model accepted conditionally, artifact SHA-256 `6427eed5f0c3b84f80a3a37c31797fc782960c725fb77f6bef46cebcc993b023`; R13 review SHA-256 `fb1f43e3c486237b9f93d6955f4bf4cf96b5b3827a40c42044838e099734c394`. Rust owner hashes remain `lib.rs` `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` and `candidate_effect.rs` `1f64d4fec8f2abceb11a48a51f5b615aa2cf605c9586ba742f15f9024a6a2717`; `term.rs` is pinned by this sprint's input manifest.

Authority: unchanged original Simple-sub inference/executor research goal. R13 remains conditional. This packet does not establish Rust execution correspondence, primitive authenticity, reservations, native publication or production.

## Fixed outcome

Replace R13's arbitrary `TermCall.handling` freedom for the named `with_term_events` helper with a source-directed control-flow construction. From explicit constructor result, ordered capacity-event snapshots, `incoming_route_accounting_active`, and per-event sampler outcomes, derive:

1. constructor operation;
2. unconditional ordered capacity-event drain;
3. no sample operations when accounting is false, or physical-change plus one sampler segment per event when accounting is true;
4. immediate error on the first failed sample, otherwise the mapped constructor result.

Construct the existing `TermCall` for successful returns without assuming a handling list or endpoint equality. Prove agreement with this source transcription, allocator/path preservation, and application at the R13 term-call cuts. Preserve early returns and error precedence. The successful-call theorem must require a successful constructor result and successful sampler outcomes explicitly.

The constructor's real `BranchTermArena` result/event generation, sampler success and resource availability, primitive/library behavior, and the Rust-to-model relation remain external. This is a control-flow model, not a claim that Rust execution has already instantiated its inputs.

## Source and proof packets

Source lane is complete and frozen at `tasks/agent-loop/inbox/effect-permission-term-call-control-r14-source.md` (read-only primary Luna; 200s). It records `lib.rs::with_term_events`, event draining, the accounting branch, sampler call/error order, route activation, capacity event generation, relevant callers and the first unresolved boundary.

Proof owner: registered `lean_prover`, 600s. Write only `notes/theory/lean/YulangClosure/FormalPermissionTermCallControl.lean` and `tasks/agent-loop/inbox/effect-permission-term-call-control-r14-proof.md`. Reuse R12/R13 declarations unchanged; do not modify accepted modules.

Independent reviewer: fresh nonauthor `compiler_referee`, 250s, after the frozen proof/source handoffs and complete primary audit; exact output `tasks/agent-loop/inbox/effect-permission-term-call-control-r14-review.md`.

Primary Luna: 150s for source pins/manifest, up to two audits, review, adjudication and state closeout. Total sprint cap 1,200s. Zero Astra and zero descendants.

## Audit and resources

Use pinned Lean 4.35.0, a fresh isolated project copy and explicit inventory/hashes. At most two separately frozen primary audits, each ≤90s and combined ≤120s. Require complete printed types and transitive axiom reports for every inherited R12/R13 root and every R14 root. Preserve each raw stdout/stderr/status/resource receipt. One primary-owned build/cache only, `-j1`, `-M1024`. No tests, Cargo, instrumentation, package updates, compiler edits, or Git operations.

## Stop conditions and open gates

Stop on an omitted event/branch, wrong early-return or error precedence, protected field access missing from the transcript, assumed handling/endpoint equality, unsupported successful constructor/sampler claim, dependency/lease conflict, exhausted audit/budget, user STOP or session end. If source extraction cannot justify the successful-call construction, return that exact boundary; do not add an arbitrary operation transcript.

Reservations and actual execution-to-state/path linkage, primitive/alias authenticity, native identity/publication, original parent, effect hygiene, consumer residual, soundness, principality, progress, termination and production remain OPEN.
