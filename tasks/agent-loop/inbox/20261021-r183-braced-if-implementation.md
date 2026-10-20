# R183 provisional Option B implementation packet — Luna result

Sprint R183 revision 3 SHA-256
`6380fedea2dad3e302fd8ed2ce99a010c61eff493b7010c17476020afa028dd8`.
Assignment `R183-OPTION-B-CONTRACT-PREPARATION`, Luna primary. This result
records contract preparation only; it does not grant code, test or execution
authority.

## Authority and user intent

The user directed provisional adoption and continuation after the R147
exact-option gate was surfaced. Luna records **R147 rev2 Option B** as the
provisional working interpretation because the user's full goal prioritizes
broad unchanged Yulang2 sample support. The user did not explicitly say “Option
B”; this is a contextual interpretation, not a direct quote. The choice remains
provisional and is not represented as permanent language authority. No further
question asks the user to repeat the same direction.

R147's five-artifact proposal bundle received a CLEAN final compiler/source
review, as recorded by `notes/progress/2026-10-20-r147-closeout.md` SHA-256
`853541e3f883a5f235fb366b752515220f9277cbe6b789f0e59b3d4e35f4e6a5` and
verified in R183 rev3 prospective review. Its historical pending-decision
status predates the user's provisional instruction.

## End-to-end behavior target

The immutable `web/playground/examples/yulang2-ordinary-islands.yu` fixture
(SHA-256 `f10e7e57cdfc165436a89326c9f069f19aa0afd24cea80b2b570463fcc553487`)
contains three identity observations and recursive countdown syntax. The
eventual Web path must execute the unchanged source and produce
`countdown_result -> 8`, preserving the identity observations and current smoke
expectations.

Option B's provisional source partition is: ordinary non-record expression
lists become an occurrence-preserving, left-to-right sequence; empty braces,
inline fields and at most one operand-bearing spread retain explicit
record-shaped meaning; malformed lists, duplicate spreads and non-record
mixed-spread bodies receive explicit diagnostics. No source item is silently
discarded. Parser recovery, branch scope/order, source ownership, effects,
conditional typing and operational continuation remain part of the contract.

## Initial direct-owner matrix

R147 rev2 pins the following direct owners, whose hash list must be transferred
and revalidated at the next contract baseline:

| Layer | Existing R147 owner | Initial evidence needed |
|---|---|---|
| Parser and recovery | `crates/yu-syntax/src/expression/if_expr.rs` | Dedicated braced arm CST, sibling shape partition, recovery/close ownership |
| HIR source | `crates/yu-hir/src/module/local_source.rs` | Arm-list representation, source occurrence identity/order/scope |
| Inference | `crates/yu-solver/src/candidate_source.rs` | Branch/result constraints, effects and record/list routing |
| Runtime | `tools/inference-playground/src/runtime/program.rs`, `runtime/machine.rs` | Ordered representation and continuation-safe evaluation |
| CLI/API | `tools/inference-playground/src/main.rs`, `src/lib.rs` | Select unchanged sample/result and expose actual execution |
| WASM/Web | `apps/yulang-wasm/src/lib.rs`, `web/playground/src/main.ts`, `web/playground/smoke-test.mjs` | Browser route selects unchanged fixture and asserts result |

This matrix is incomplete for code authorization. R147 rev2 requires a
dedicated sequence HIR and matching inference/runtime consumers; it does not
pin their exact definition files. The direct-owner list also does not establish
the complete focused test set or all error/effect continuation consumers.

## Next exact work

Prepare a bounded read-only source-owner mapping contract covering the CST/type
definitions, HIR sequence representation, inference constraint/record consumer,
runtime continuation/effect consumer, and focused test owners. Freeze each
source file to a direct hash at the R184 baseline, preserving current uncommitted
source work and avoiding Yulang2 oracle checkout contents. Use that result to
write the complete Option B implementation contract with exact atomic code
leases, unchanged sample/output assertions, focused/regression test commands,
independent review and a 2100s implementation/600s verification/300s review
allocation in the additional 3000s code phase proposed by the R183 dispatcher.
Do not collapse this code phase into the R183 source-to-Capture proof.

No additional source files were read under R183; no tests/builds/probes or
compiler/evaluator/CLI/WASM/browser/Yulang2 processes ran. The only source pins
in this packet come from R147's already reviewed contract. No code-ready slice
is claimed until the missing owner map is frozen. R70/R71, inference/evaluator
A/B, source/native and production gates remain OPEN.
