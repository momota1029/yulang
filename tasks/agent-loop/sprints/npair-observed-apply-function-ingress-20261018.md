# Sprint `npair-observed-apply-function-ingress-20261018`

Status: READY for Luna dispatch, issued 2026-10-18. Revision 1.
Branch/baseline: `research/simple-sub-intrusion` / `5c45c1807fc6f4fa495a2f0b85c4bdba1672820d`.
Parent: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`; original theorem,
domain, quantifiers, receive route, C1/C2 and F1/FK1 are unchanged.
Prior closeout: `notes/progress/2026-10-18-npair-actual-argument-ingress-closeout.md`.

## Fixed outcome

Observe the actual added binding `my received = receive f0` from parsed source
through HIR LocalSource and candidate collection, including whether an outer
Apply is present and its exact operands. Then derive the native Apply-demand
constructor and full Function-child dispatch from the actual source owners.
Connect the same actual returned `R1`, its Written `s1` field and receive's
Permission negative port `D` through the real comparison and both ordered
Replay inputs, or identify the first edge that direct evidence fails to
establish. Do not assume `UnsupportedExpression` means that LocalSource or
collector evidence is absent; do not choose HIR lowering as the root cause
without tracing the actual producer.

Keep Operation root Self `s0` separate from returned Written `s1`. No synthetic
transition, assumed native record, invented Replay premise, field movement,
domain restriction or expected-output change is allowed. A source refusal or
unestablished edge does not refute or close the original parent.

## Lanes and exact writes

1. **Constructive proof, Sol/prover/high, cap600s.** Read the pinned
   `candidate_source.rs`, `candidate_call.rs`, `candidate_scheme.rs`,
   `candidate_effect.rs`, `candidate_context.rs`, `candidate_extrusion.rs`,
   `shadow_apply.rs` and `lib.rs`. Derive the actual Apply native demand and
   complete Function children from their source constructors/dispatch. Apply
   only established edges to the original witness/H0, L2 `eta`, P3/P6; retain
   every missing premise and the original quantified alternatives. Write only:
   `notes/theory/2026-10-18-npair-observed-apply-function-ingress.md` and
   `tasks/agent-loop/inbox/20261018-npair-observed-apply-function-ingress.md`.

2. **Implementation/source path, Luna/implementer/high, cap720s.** Read the
   pinned `research_source_registration.rs`, `candidate_source.rs`,
   `yu-hir/src/module.rs`, and `yu-hir/src/module/local_source.rs`. Extend only
   the research example to explicitly report the `received` module binding,
   its HIR node, LocalSource result, collected Apply and actual callee,
   argument, result and effects. Add the one reversible source line to the
   pinned fixture, run the exact command below once, then restore fixture
   bytes. No production compiler code, tests, expected output, manifests,
   public API or semantics may change. If the example cannot directly expose
   the binding, stop at that actual owner boundary and report it; do not infer
   absence from selective output. Write only:
   `notes/progress/2026-10-18-npair-observed-apply-source-evidence.md`,
   `tasks/agent-loop/inbox/20261018-npair-observed-apply-source-evidence.md`,
   the research example and the one-line fixture (fixture restored exactly
   after the run).

   Exact source input and run:

   ```yu
   my received = receive f0
   ```

   ```sh
   timeout 120s cargo run --offline \
     --manifest-path crates/yu-solver/Cargo.toml \
     --example research_source_registration \
     --features shadow-apply-candidate
   ```

## Pinned inputs and access

| Path | SHA-256 | Access |
|---|---|---|
| `crates/yu-solver/src/candidate_source.rs` | `4ea9d89e4a31e7be4ce170517e50eea31dd9e054c360cedba9ccc9cb7ced69ce` | read-only, shared evidence |
| `crates/yu-solver/src/candidate_call.rs` | `2bcbab3d27e259fc4b22824980bd625014d4a19f4fa257cd74c69683c1be0359` | read-only |
| `crates/yu-solver/src/candidate_scheme.rs` | `abe1eb6d6176c035d237c3f51f7ccfe99dea5224df20de285465c510c6c2a494` | read-only |
| `crates/yu-solver/src/candidate_effect.rs` | `9ea9498692bdff12c2a7ebd8546ca2b443a095c0700f3e87ad6c956cc690e212` | read-only |
| `crates/yu-solver/src/candidate_context.rs` | `72da8a6e7b3f04ed3f7054b6151410c7d2b35f9f91b756ade1f6f008244c1ce6` | read-only |
| `crates/yu-solver/src/candidate_extrusion.rs` | `2c535e0906a9cf6221fa4746ae815dc45ce18cf37f19a8e811f996d8422b7f6b` | read-only |
| `crates/yu-solver/src/shadow_apply.rs` | `bb1e63c2ea33bf0b6e7408bd015d2498a9aed4dd45e250a85433169c9da334bf` | read-only |
| `crates/yu-solver/src/lib.rs` | `2c1fff385e5270ef7b7eb5fc4d9ed5f6edb6a4c01886887b183401212c5f398f` | read-only |
| `crates/yu-solver/examples/research_source_registration.rs` | `10ea5f2c6db7c9d093d86780dbeb217d7eca11332e99a4d1ec40f4753f544e7c` | implementation write |
| `crates/yu-hir/src/module.rs` | `60e91c9a51394b04af42b3ec7c284062b34fcd9faa4ea79c35b4ae58aaf460ed` | read-only |
| `crates/yu-hir/src/module/local_source.rs` | `ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5` | read-only |
| `tasks/agent-loop/fixtures/20261017-receive-choose.yu` | `969e20e0f38a2c341a96ff4fe07028bf567ca134e0fb24602fadf6e4c723d9c0` | one reversible line; restore exact bytes |
| `notes/progress/2026-10-18-npair-actual-argument-source-path-correction.md` | `071b87b2e08acf6845de2b8fd16199fe0c84590abda5fc2f4bb41aae7fa39586` | read-only adopted correction |
| `notes/theory/2026-10-18-npair-actual-argument-ingress.md` | `c5365821565f8043f1d63fe50a209ce24777cf506a26098852f01db33d0d2d09` | read-only reviewed proof obstruction |

The corrected implementation disposition supersedes the earlier claim that
the binding lacked LocalSource/collector coverage. The old submission remains
immutable; use the correction and this contract as authority for the next
observation.

## Review, resources and stop

Fresh independent proof/spec review: 180s. Fresh independent
implementation/compiler review: 120s, after the harness artifact is frozen.
Luna primary/integration: 120s; reserve60s. Total1800s, Astra0, descendants0.
Only the exact existing example command above may run as one heavy process;
no other tests/builds/probes. Any source-owner hash mismatch, need to modify
production compiler/HIR, missing writer cessation, or resource cap is a stop
with its exact first unresolved edge. Existing original semantic alternatives,
W/Z, source/native correspondence, Call, N-Transport, soundness, principality,
termination, F1/FK1 and parent closure remain separate.

Before pushing, Luna verifies the review findings and source/fixture diff,
updates the compact state, stages explicit paths and pushes non-forced.
