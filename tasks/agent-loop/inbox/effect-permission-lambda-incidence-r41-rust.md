# R41 Rust handoff — Lambda argument-effect incidence

Sprint-ID / contract revision and SHA-256: `EFFECT-PERMISSION-LAMBDA-INCIDENCE/20261031-R41`, admitted contract SHA-256 `20b446aa3ad63eeccbda603e4b054ccd76e87e492c8f64d7a5cab6aacd112ed8`.

Assignment-ID / handoff revision: `R41-RUST-INCIDENCE`, revision 1.

Parent gate / original theorem and scope locator: unchanged annotation permission, open inflow and actual subtraction obligation in `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1, 1.1–1.2. This implementation packet establishes only the registration-to-Function argument-effect incidence through capture and retained FreshUse maps. It does not establish provider arrival, Catch selection/residual, subtraction, source-wide hygiene, whole-language safety, or production permission.

Baseline / direct dependency hashes: Git baseline `41a446c9e37d1cb9a4f88f7d8832f831d76cfd40`. Pinned pre-write hashes: `lib.rs` `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07`; `candidate_context.rs` `57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e`; admitted dirty `candidate_scheme.rs` `31ae5b9466a0f7bbd501c81e4401049ad9782636ba57ed89e8232e9149e8b707`. Read-only pinned inputs rechecked unchanged: `candidate_source.rs` `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a`; `candidate_call.rs` `fdc39e01fa3665b4dc14e167973de63b275eb0280b831e340b6cdcee5ed0fc3f`; R39 Lean model `ComputationPermissionEntryR39.lean` `748cd52ff7962962940a3767ffa6a0b2d8def16d80e65e682282d1fa2b79560e`; R40 report `effect-permission-module-use-r40-read2.md` `29ef9e594a9175299410db966f15e5689781568b6ca998055668aec152f58627`; R40 independent review `effect-permission-module-use-20261031-r40-read2-review.md` `86ccde5b1b3ff0f18efa64aa6e819caeb05a51b39f34b0f2e94a9a9596f28a97`.

Role / actual worker ID / current session / launch or resume receipt: implementer / `/root/r41_rust` / `R41` / no direct runtime receipt available to this worker.

Requested model and effort / observed model and effort: `gpt-6-luna` / high / UNKNOWN / UNKNOWN. No model or effort telemetry was exposed in this worker context.

Exact leased paths / authors and descendants: `/root/r41_rust` owns only `crates/yu-solver/src/lib.rs` (`admit_lambda_fact` and local declarations), `crates/yu-solver/src/candidate_context.rs` (passive provenance), `crates/yu-solver/src/candidate_scheme.rs` (capture, graph/FreshUse mapping and accounting), and this handoff. No descendants.

Outcome class: bounded implementation and provisional passive source-evidence instrumentation.

Parent application: each computation-formal Lambda now retains the exact `FormalRegistrationInput` vector index, Lambda occurrence, exact positive Function term, and argument-effect row after `positive_function_term` constructs the Lambda Function. This record is independent of slot-3's forced-entry constraint; computation formals can omit that edge and still retain their constructor incidence. During graph capture, the exact positive Function endpoint selects the graph Function node, then structural child index 1 selects its argument-effect `Node::Row`; the row is checked against the recorded entry's current representative. The graph keeps the source registration label, Lambda occurrence, Function node index, child index, and child graph-row index. Each FreshUse follows that exact row index through its existing ordered `rows` map and retains the registration label, Function/child coordinates, graph-row index, and mapped row beside the existing reconstructed `terms` vector. Multiple registrations remain separate records even if their mapped row images coincide.

Source constructors -> generated constraints -> propagation -> consumer/native path: `candidate_source` creates a `FormalRegistrationInput` while visiting a source Lambda and places the same registration index in its `LambdaRecipe`. `admit_lambda_fact` selects the registered computation entry, constructs the positive Function with that entry as its argument-effect child, and retains passive incidence metadata. The existing candidate graph capture traverses structural endpoints and now carries the exact label to Function child 1. Existing FreshUse row reconstruction maps that child row to its use image; existing node reconstruction and bound restoration continue through their current path. The new metadata does not authorize or change a permission consumer, add a propagation edge, perform subtraction, or alter natural inference. Rust source evidence is present; its source-to-Lean correspondence remains a separate proof/review question.

Artifact locators and frozen byte hashes:

- `crates/yu-solver/src/lib.rs` SHA-256 `b1dac8bd244e282ff42a2d580e237393153f9b912c6ac0adf110367def5c79ce` — select only computation registrations, then retain their constructed Function/entry incidence from `admit_lambda_fact`.
- `crates/yu-solver/src/candidate_context.rs` SHA-256 `030fcb4b6571c0db8a670d12d8a67fe8fcf465484502fe5b11b6d057e8026c38` — passive origin type/vector, checked reserve, checkpoint truncation, checked state bytes and enumerated bytes.
- `crates/yu-solver/src/candidate_scheme.rs` SHA-256 `73f13e56057efa11d5c9b8f1eff66687b83920257e2c41ba1dcce2ecb3ce3785` — graph incidence, exact endpoint/child capture, FreshUse row-image record, retained route-map transfer and checked byte accounting. This full-file hash includes the admitted pre-existing dirty bytes; this handoff does not claim an independently isolated diff or certify those unrelated bytes.
- `tasks/agent-loop/inbox/effect-permission-lambda-incidence-r41-rust.md` — this frozen handoff; its byte hash is returned separately at intake.

Checks, coverage, omitted cases and resource budget: performed a bounded static source walk over the leased owners and exact read-only constructors, checked that each retained allocation has a fallible reserve and checked capacity accounting, and rehashed the pinned read-only dependencies above. No tests, compiler/build, Cargo, Lake, environment, cache, worktree, scratch file, or Git operation was run or created, as required by this assignment. Existing source tests inspected but not run: `f5d_identity_lambda_admits_exact_effect_and_function_facts`, R226 and R227. They provide prior construction/route context and do not prove this new registration-to-child record. No runtime behavior check was performed. Elapsed seconds and CPU/memory use were not instrumented; assignment cap is 1,400 seconds, no extension or transfer was requested.

Prior evidence reused/rejected: R40 READ2's reviewed finding is reused: captured Function children and exact module FreshUse routing existed, while the source registration-to-Function-child association was unestablished. Its `{signal | e}` / `{write | e}` shared-tail example remains a conditional falsifier for any equality-only consumer; it is not treated as an observed Rust defect. R39's owner-local source identity and separate entry permission construction are reused only as source provenance context. R39 Lean theorems are not treated as proof that this Rust record implements the finite model. Existing R226/R227 tests were not treated as evidence for the new metadata and were not modified or run. No `Simple-sub` bypass was restored.

Mutual TODO: `R41-RUST-INCIDENCE-TO-PROOF-1`; unchanged parent is the annotation permission/inflow/subtraction obligation; first missing evidence is a reviewed source-to-Lean correspondence for the exact `FormalRegistrationInput` index, Lambda occurrence, constructed positive Function child 1, captured graph child, and FreshUse row image. Proof owner is `/root/r41_proof`; required inputs are this frozen source delta, the R41 Lean constructor/capture/FreshUse model, and the unchanged candidate source/call dependencies; proposed output is an explicit theorem/source correspondence or the exact failed source premise. Falsifier: two distinct registration labels with a shared row image become one record, or a retained record's Function child/graph-row/use-row coordinates do not commute with the actual constructors. This request does not grant a write lease on proof files or any consumer.

Provisional boundary / cleanup owner: the records are passive source-evidence instrumentation only. Cutover and permission consumption remain OPEN. Luna owns cleanup or later consumer integration after independent review; preserve the records while the proof/source correspondence is unresolved. The conditional shared-tail witness falsifies any proposal that treats the mapped row as registration identity.

Worker state / writes stopped receipt / unresolved descendant leases: all leased writes stopped after this handoff was frozen; no descendants or generated outputs. No disposable scratch paths exist. Runtime cessation was not independently observed; Luna owns live-state synchronization and the frozen-file intake.

Commit-ready milestone or explicit pending review: implementation result is frozen pending fresh independent review. This author does not self-certify the candidate delta, prove native correspondence, or close any theorem or production gate. Preserve the original open premises and all existing diagnostics/source domains/expectations.

Next related in-envelope step: after `/root/r41_proof` freezes its separately leased result, Luna assigns the contract's fresh independent review across the exact source/proof snapshots. If review accepts this Rust delta, a later approved step must join the retained registration-specific child image to source-qualified arriving contribution before any permission consumer is considered.

## Revision 2 — primary correction after independent review

The independent R41 revision-1 review found two blocking issues in the frozen
Rust source: capture stored the child ordinal `1` where later code interpreted
the value as a graph-node index, and the unparenthesized `match` initializer was
not valid `let-else` syntax. The review otherwise independently accepted the
bounded Lean audit, conditional witness, and dirty-base isolation.

The primary corrected the exact leased owner `candidate_scheme.rs`. Capture and
FreshUse now retain separate `argument_effect_child_index` and
`argument_effect_child_node` fields. Capture stores the actual node obtained
from `children[1]`; FreshUse checks the index selects that node, reads the row
through that node, and carries both coordinates forward. The match initializer
is parenthesized. No other source file or semantic consumer changed.

Corrected `candidate_scheme.rs` SHA-256:
`3cd9dd2d0f55412636dc88bc658d7cfbc23aad6304b90f2ba95247f8d58e1d22`.
Independent revision-2 review passed for this exact source hash. The bounded
static review confirmed separate child-index/node-index handling, the
non-node-1 row/FreshUse image, valid match-initializer syntax, and exact
reconstruction of the pinned dirty baseline. The complete review receipt is
`tasks/agent-loop/inbox/effect-permission-lambda-incidence-r41-review.md`.
