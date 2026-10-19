# R118 implementation handoff — rev2

Sprint / contract: `nested-handler-outside-selection-20261019-r118`, rev2,
SHA-256 `7b588d4e5990b142381f2993e4fa49376d5ebdd0efd2311bb3418f42f3879d63`.
Assignment: R118 implementation, handoff revision 1.
Parent: ordered-handler/outside-selection hygiene front under the unchanged
source/native and evaluator obligations. This is implementation evidence only;
it does not close a parent proof or approve production/adoption.

## Frozen result

The two test-only `Graph` fixtures in `crates/yu-solver/src/shadow_apply.rs`
now fill `capture_forest` from the owning state via
`state.intrusion.forest_snapshot().unwrap()`. The first uses its own default
`GraphState`; the merged-representative fixture uses the exact `state` borrowed
from `candidate.solved.data.candidate_graph`. No empty/default forest was
substituted for the merged candidate.

Added `tools/inference-playground/tests/cli_nested_handler_selection.rs`, a
public stdin invocation of `yu-playground --run main --steps 10000 -` with the
contract's exact 235-byte source and no final LF. It asserts successful exit,
exact stdout `11\n`, and empty stderr. The fixture repair and CLI observation
are separate file-level, commit-ready slices. No runtime or inference behavior,
existing test, expectation, diagnostic, source domain, or semantic rule changed.

## Source and parent correspondence

The test invokes the public binary path in `tools/inference-playground/src/main.rs`;
that path reads stdin and calls `yu_playground::execute`. `execute` in
`tools/inference-playground/src/lib.rs` calls `prepare`, which lowers one HIR,
solves from `hir.clone()`, and returns that same HIR for
`RuntimeProgram::from_hir`. The test is a finite public observation of that
path if and when the authorized CLI command passes. It does not itself expose
operation IDs, selected arm identity, installed `CatchReturn` frames, or prove
the inner-to-outer propagation trace. Those remain with the proof/source owner.

The authentic snapshot constructor is test-only
`candidate_intrusion::State::forest_snapshot`; production graph capture in
`candidate_scheme.rs` takes it from the active candidate graph's intrusion
state. R117 records the exact two missing-field test-compilation failures;
R109's failed source-range assertion and its fixture remain untouched.

## Artifacts and dependency pins

```text
crates/yu-solver/src/shadow_apply.rs
  838d862dd34fe2b2bd70c5d92c5ce9af0aa98f10f8b6a8eddf313ae798686543
tools/inference-playground/tests/cli_nested_handler_selection.rs
  cc56cb82c363c13b34d09bb28b6b12372451334e2d24e2412106ea1611fc91b6

crates/yu-solver/src/candidate_scheme.rs
  2e64dc8781189b4da21c30f4d1b3208aaef48ca247cae55fb7e77e68b5857850
crates/yu-solver/src/candidate_intrusion.rs
  8a1f531be9fb5e5f160bf4f75c6eb98bbc35ce0a30acaf06424c531840504ba4
tools/inference-playground/src/runtime/machine.rs
  fa8dab7f7146f528ad354f336cdfe6e41a728505f9c3dd80c6df64e843dc5b46
tools/inference-playground/src/runtime/program.rs
  c2363ad42104b895519bb29a8eb9aeda545bd0176cebbd78750d3a2df90849ca
tools/inference-playground/src/lib.rs
  bdf996d0264e252e345c05bc77b2adcf625120281244171f0054f1d87a8d1e1b
tools/inference-playground/src/main.rs
  75b38435f4634ee35b3e14a54fb4d021b78bda834b4fd53965302a73309e0100
```

## Checks, limits, and TODO

The R118 verification commands were not run. The solver test-target compile
command and the exact CLI test command remain NOT_RUN until the frozen outputs
receive the required fresh CLEAN compiler/source, spec, and regression reviews
and Luna admits verification under the shared 240-second envelope. No pass is
claimed. The CLI expected result is a contract prediction, not observed output.

No proof premise was discharged. The finite trace still requires the exact
source operation identity join, selected inner arm and consumed installation,
the new `tick` request's outside context, selection by the retained outer
handler, and final result correspondence. The general order/source theorem,
R117-JOIN-1, R100-P2, R85 adoption, all six effect parents, method/role parents,
the evaluator, and Simple-sub A/B remain open.

TODO `R118-IMPL-TRACE-JOIN-1` — proof/source owner `/root/r118_proof_lane`:
using the pinned same-HIR caller and runtime owners, connect source `io::other`
and `io::tick` operation IDs to their runtime declarations; identify both
handler arm owners and `CatchReturn` installation/consumption; show the inner
arm request uses the remaining outer stack and that the outer arm yields the
same final integer. Falsifiers are any identity mismatch, failure to consume
the inner frame before arm execution, missing outer selection, or a public
result/stream different from the exact CLI contract. This TODO requests evidence
only and grants no additional write lease.

Checks performed: source/history/test inspection and output hashing only; no
build, test, CLI, runtime probe, or Git command. No scratch/generated paths.
All three leased outputs are frozen; writer STOPPED, no descendants, no pending
write. Requested model/effort: Luna/high. Effective observed model/effort:
UNKNOWN. No independent review performed by the author.
