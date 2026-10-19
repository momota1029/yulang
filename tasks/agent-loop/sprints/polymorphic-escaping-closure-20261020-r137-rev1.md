# Sprint polymorphic-escaping-closure-20261020-r137 — locally generalized closure escape

Status: CANDIDATE pending prospective spec and compiler/source review; no implementation/proof lease until both pass
Branch / baseline: `research/simple-sub-intrusion` / `93385cb6ab1e83a769e84af4997d39b9f57c9684`
Contract revision: 1

## Original outcome and success evidence

Parent goal: implement Yulang inference/evaluation with proof-backed source correspondence while broadening unchanged Yulang2 sample behavior where the current compiler can support it. R137 composes local generalization, lexical capture, closure escape, and independent clients through current CLI/WASM entrypoints. It does not close any general inference/evaluator A/B or production gate.

Frozen candidate source (`web/playground/examples/polymorphic-escaping-closure.yu`):

```yu
my identity x = 0
my make seed = { my identity x = x; \unused -> identity }
my chooser = make ()
our int_result = chooser () 7
our bool_result = chooser () true
our string_result = chooser () "ok"
my main = int_result
```

The inner `identity` is locally generalized, then referenced by a returned closure; a deliberately different outer `identity` shadows it. Each `our` result consumes the same returned closure at a separate type. Expected selected outputs are `int_result = 7\n`, `bool_result = true\n`, and `string_result = \"ok\"\n`; these are predictions until authorized execution. `main` returns `7\n` for the browser's default selected definition.

Success: prove the finite source-constructor and evaluator path conditionally on ordinary source preparation; independently review the frozen derivation and exact source/runtime correspondence; pass one isolated CLI integration test selecting all three results; pass one browser/WASM build and smoke check selecting `main` plus the three named results. A client constraining another, capture resolving to the outer shadow, missing local generalization, inference/runtime disagreement, or unavailable source admission falsifies the candidate. Stop on the first failure.

## Authority and dependencies

Use current ordinary syntax and established local generalization, lambda capture, closure application, and source root selection. No new syntax/API/semantic/runtime/solver policy is proposed. Do not modify parser, HIR, solver, runtime, WASM implementation, existing expectations, diagnostics, or R135's pending braced-if proposal. If a source or runtime edit becomes necessary, stop and return for Luna adjudication under a new contract revision.

Relevant existing evidence, limits:

- `cli_returned_closure::returned_closure_preserves_original_capture_through_cli` already checks a returned closure retains an integer capture.
- `candidate_context_tests` already examines authentic local identity capture and FreshUse incidence, but does not establish this returned polymorphic closure's consumer path.
- R134 verifies three selected Yulang2 identity definitions and root visibility; it does not establish local scheme escape through a returned closure.
- Owner inspection targets: `candidate_source.rs` local/Lambda source production; `candidate_scheme.rs` local generalization/fresh-use routing; `shadow_apply.rs` candidate collection/solve; runtime `program.rs` closure construction and `machine.rs` capture/apply; `yu-playground::execute`; WASM `run`.

Pinned direct-source hashes:

```text
crates/yu-solver/src/candidate_source.rs cbc39315f4243b0bae1db74976cf94282bc94cd28b9eb463699c085f421065f7
crates/yu-solver/src/candidate_scheme.rs 2e64dc8781189b4da21c30f4d1b3208aaef48ca247cae55fb7e77e68b5857850
crates/yu-solver/src/candidate_effect.rs 6112343b4014c67dcb7d814a46412b3af3e1d12183924e891df4817a59f58da0
crates/yu-solver/src/shadow_apply.rs 838d862dd34fe2b2bd70c5d92c5ce9af0aa98f10f8b6a8eddf313ae798686543
tools/inference-playground/src/runtime/machine.rs 4fb918732047f61184bc8f89b829bde68a8d1e6649a24d02640ec14500ae0acd
tools/inference-playground/src/runtime/program.rs 28748da0458da92b9d1190b250bbb84bdecc6643718eacbca95a04f5d6c9aa0d
tools/inference-playground/src/lib.rs a0769f77feac552304f0516b0742637f51660c0bb8bf9391d18ae0f9de5e2473
apps/yulang-wasm/src/lib.rs 2fc9feb353b3130c4efc888270cec14cba8b2bbcc2fca03d3780c676e0468f8a
tools/inference-playground/tests/cli_returned_closure.rs fc58331f2a444dd5cb85b3e3bdd8f7cd4bd6bbb11b1ff95bf2794f6e66c5278c
tools/inference-playground/tests/cli_demo_identity.rs 09fecc7c8b8a152ec49d939517d3dcd4951fad48a2909c1faee15bf95cc7a773
notes/theory/2026-10-20-r134-root-visibility-carrier.md 0b71be14476a1975b9d8816d452da74b666ae34e449c04f344398004ad5e6e4b
web/playground/src/main.ts 2df8c6e12911cb3b152be3d3d65bdb25bd51ad666e4ce003c76209593ce669e7
web/playground/index.html 487e3c2a7e39d9cf343325e249c942ef593edcae7e4b5e4ff8c363c61d97343b
web/playground/smoke-test.mjs 899b7f942f11d7cad48253d27ab502cd91106ffd6f02bdb2ca6b3d87fef9a9f8
web/playground/package.json ff870bfa1ba5cbb139a5a0b1d34673684eed9984f821548703ad648d0c9d1caf
web/playground/vite.config.ts 4f5df146b7d97875ab25521346845634a9fed911345355d3e6f2d77cbff58d69
```

## Two lanes after candidate approval

Proof lane: derive the local identity binding's scheme at its authentic owner; show the lambda body's `identity` reference resolves to that local binding rather than the outer shadow; trace the returned closure's captured environment and each independent client instantiation; relate retained source constructors to candidate collection, fresh-use consumption, runtime closure creation/application, and selected output. Distinguish source admission and observed execution from conditional derivation. Do not claim general let-polymorphism, soundness, principality, or all-environment lexical correctness. Outputs: `notes/theory/2026-10-20-r137-polymorphic-escaping-closure.md` and `tasks/agent-loop/inbox/20261020-r137-proof.md`.

Implementation lane (Luna/high): one canonical Web source fixture, one CLI test that selects all three result definitions, Web selector registration, and smoke assertions for `main`, `bool_result`, and `string_result` (the `main` result is `int_result`). No runtime or solver edits. Output `tools/inference-playground/tests/cli_polymorphic_escaping_closure.rs` and `tasks/agent-loop/inbox/20261020-r137-implementation.md`.

## Exact candidate review leases and subsequent code leases

Before review, only Luna edits this contract/current state. Fresh prospective review: `spec_auditor` checks authority, scope, fixture/test contracts and expected-output protection; `compiler_referee` checks source resolution, type-ownership premises, path feasibility, and pins. Their exact receipts are `tasks/agent-loop/inbox/20261020-r137-prespec-review.md` and `tasks/agent-loop/inbox/20261020-r137-precompiler-review.md`. Reviewers do not run tests/builds/compiler or edit source.

If both are CLEAN, proof exact leases are the theory note and proof inbox above. Implementation exact leases are the canonical fixture, CLI test, `web/playground/src/main.ts`, `web/playground/index.html`, `web/playground/smoke-test.mjs`, and implementation inbox above. Proof and primary implementation proceed in parallel; workers do not overlap. Fresh final compiler/source and regression reviews inspect frozen artifacts and dependencies before verification. Only Luna integrates Git.

## Resources, verification, and stop conditions

Cap 2,100 active seconds: inventory and prospective reviews 240; proof 660; primary implementation 420; final reviews 300; serial CLI/Web verification 360; closeout/integration 120. Zero Astra, one heavyweight process at a time. Run one isolated CLI test, then `npm run check` once. No extra tests/retries after a failure without a new contract. These checks are authorized by the standing user goal to make examples run.

Stop on any pin mismatch, scope/authority expansion, required runtime/solver changes, incorrect result or cross-client interference, unaccounted writer/descendant, or exhausted cap. On failure preserve the exact evidence and return to Luna; do not weaken the sample. Keep all original theorem and production gates OPEN. Only Luna changes current state, grants leases, adjudicates, stages explicit paths, commits and pushes non-forced.
