# Source-authentication admission run receipt

Sprint `source-authentication-admission-20261017`, contract revision 4 SHA-256 `316feaaac1ba4ee17d00ec088445937d74651a48e7081b180cc07eb3deefb4f2`. The one authorized primary Cargo execution used the frozen rev3 implementation artifact SHA-256 `10ea5f2c6db7c9d093d86780dbeb217d7eca11332e99a4d1ec40f4753f544e7c`, fixture SHA-256 `969e20e0f38a2c341a96ff4fe07028bf567ca134e0fb24602fadf6e4c723d9c0`, pre-edit snapshot SHA-256 `60592afdafd8b545ef0f4410a693bcc5815ce929d2ae64c8b527ec28bdf0643c`, proof artifact SHA-256 `fde662725830095f4ea28e902449c34bc89ebbc237cdc30fee5ee214fc135601`, and proof handoff SHA-256 `2c408c62f0d7937bf416d1a21b968a001ac55974974212b1141ac77b27e6af6b`. All 17 direct pins were rechecked immediately before the run.

Command:

```text
timeout 120s env CARGO_TARGET_DIR=/tmp/yulang-research-source-authentication-20261017 cargo run --offline --manifest-path crates/yu-solver/Cargo.toml --example research_source_registration --features shadow-apply-candidate
```

Exit code: `2`, completed in about two seconds under the 120-second cap. This was one run, not a test. No more execution is authorized in this sprint.

Observed output and path:

- `source.bytes=357`, `SourceRevision(0)`, `parse.structural_recoveries=[]`.
- HIR lowering completed at `SourceRevision(0)` and reported exact errors: `HirErrorId(0)` UnsupportedItem, DirectRootItem(0), range `80..130`; `HirErrorId(1)` UnsupportedExpression, value `f0`, range `147..162`; `HirErrorId(2)` UnsupportedExpression, value `receive`, range `328..356`.
- `f0` and `receive` definitions had source-root identities; `f0` definition key was parse-owned. All four declaration keys printed parse-owned. Family/member and member/name/signature key equalities were false as expected for distinct syntax positions. The choose use was parse-owned and resolved to the same declaration `Arc` as the HIR choose member. `f0` LocalSource had one operation use; receive LocalSource inventory contained eight expressions, including its formal annotation and block applications.
- Normal `CandidateInference::solve` was entered and returned `CandidateError::Unsupported` (`STOPPED at candidate-solve: Unsupported`). The API/identity harness checks before this boundary completed. Candidate graph export was not reached.

The run confirms that the prior example-level nonempty-HIR-errors gate had hidden the normal candidate admission result. It does **not** reveal which individual owner/preflight branch produced the generic `Unsupported` error. The pinned proof/source packet statically predicts receiver formal preflight failure at the negative concrete `[ctrl]` row before receive placeholder retention; that is a source prediction, not an execution trace. Exact branded SourceNodeKey payloads were not printed (`Debug` elided them); parse ownership/equality predicates were observed. Declaration placeholder contents were not printed directly. Do not claim that all diagnostics are placeholders or that solve passed.

No test, fixture edit, compiler source change, semantic/API change, or source-domain change occurred. Historical source identity, mathematical phase-root `R_e`, complete choose semantics, F1/FK1/First-Result, principality, F5 and production remain OPEN. The previous sprint receipt correction r2 remains pending independent delta review; this new run does not silently close it.
