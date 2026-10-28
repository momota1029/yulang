# SOURCE-RECEIPT-ORIGIN/r11

Status: ADMITTED BY LUNA. New packet after `NATIVE-WITNESS-VALIDATION/r10` CLOSED_INCOMPLETE; it does not retry R10. Baseline `7b3ad7074`. Input manifest `tasks/agent-loop/sprints/source-receipt-origin-20261028-r11-inputs.json`, SHA-256 `a3b10055f0fb497bd341bdbd6ff7dc80d9ec40d15f564c6339d34e95539790b4`, 90 authenticated entries, 90 unique paths, zero mismatches at admission. Parent outcome is R10 `tasks/agent-loop/history/native-witness-validation-20261028-r10-outcome.md` (SHA-256 `e151f1a31c4a9396fa9b52a265b0515cc00d073ea628a966d0b46b029de0cc84`).

## Fixed outcome and original scope

Trace the first `ReceiptMismatch` produced by the exact unchanged Rust fixture `replay_constructor_lineage_observes_rejected_cross_route_authentication` from the failure-producing source owner through its consumer guard. Identify the relevant receipt fields/invariant and responsible source owner, or report the exact unresolved branch if the trace cannot distinguish them. Compare the observed event with the corresponding original source occurrence, bound, antecedent, use, mapped/admitted relation, flow/demand, restoration/emission path. A `ReceiptMismatch` by itself is not a source-qualified counterexample and closes no theorem.

Preserve the original `YulangClosure.SourceProblem.InferenceSoundness`, all quantifiers and its source domain, one shared source witness, immutable-birth Value qualification, and effect-hygiene policy. Parent, native/source correspondence, effect hygiene and production remain OPEN. R10's accepted conditional Lean artifact is reusable but proves no new source/native fact.

## Frozen inputs and workspace

The 90-entry manifest inherits R10's 89-entry input cone and maps its R9 workspace paths into `isolated/source-receipt-origin-r11/`; R10 check logs, proof/review and outcome are additionally pinned. The R11 workspace is a byte copy of R9 without the generated `build-target/` and Lean `.lake/` caches at preparation. The three writable Rust files start at the inherited R9 hashes. The exact focused test, its assertions, feature flags, error kind and ordinary control flow are frozen. No R9 or production source path is writable.

## Lanes, exact writes and aggregate bounds

Fresh aggregate envelope **3,000 seconds**, no renewal; Luna implementation 900s, registered `lean_prover` Sol/high source/proof lane 900s, independent review 600s, Luna primary checks/integration 600s; Astra 0. Implementation and proof may proceed in parallel from the immutable admitted inputs. Reviewer runs source-first after both outputs freeze. No Cargo/Lean check before initial independent review accepts the exact frozen candidates.

- Implementation writes only `isolated/source-receipt-origin-r11/crates/yu-solver/src/candidate_scheme.rs`, `candidate_context.rs`, `candidate_extrusion.rs`, and `tasks/agent-loop/inbox/source-receipt-origin-r11-rust.md`. Add only test-gated, invocation-correlated origin/stage observations for the exact failing fixture. Instrument the actual `ReceiptMismatch` producer/consumer path enough to distinguish the first error-producing owner; record minimal provenance needed to join it to the fixture invocation. Keep closures lazy when recording is disabled. Do not change semantic branches, error values, expected output, assertions, fixture inputs, solver results, or production builds. Do not repair the semantic cause in R11. If finding the exact producer requires broad behavior changes, stop and return the exact missing owner/capability to Luna.
- Proof/source writes only `tasks/agent-loop/inbox/source-receipt-origin-r11-proof.md` and, if a source-derived conditional theorem can be stated without invented or unproved premises, `isolated/source-receipt-origin-r11/notes/theory/lean/YulangClosure/NativeReceiptOriginR11.lean`. Work from immutable R9 inputs, not the concurrently edited R11 Rust files. State whether the observed receipt consumer condition is implied by an existing source rule, needs a missing source/native bridge, or remains underdetermined. Any Lean theorem must state every premise and preserve the source domain. No new axiom, `sorry`, `admit`, assumption of the failure, or parent-claim weakening.
- Reviewer is fresh `compiler_referee`, Sol/medium, maximum 600s, read-only. Authenticate all pins before source-body reads; inspect source and proof artifacts before checking; verify the exact test/expected output and that instrumentation preserves the production path and error semantics. After checks, authenticate and inspect every frozen log and complete theorem type/axiom output. The reviewer writes no file; Luna persists the review receipt at `tasks/agent-loop/inbox/source-receipt-origin-r11-review.md`.
- Luna owns `tasks/agent-loop/current.json`, all logs, outcome `tasks/agent-loop/history/source-receipt-origin-20261028-r11-outcome.md`, review persistence, integration and Git.

## Conditional checks after initial review

Cargo: at most **two** exact attempts, combined wall at most **180s**, one CPU affinity 0, maximum **2 GiB sampled process-group RSS**. Use the same fixed fixture and feature; no test filter or expected-output change:

```text
CARGO_TARGET_DIR=isolated/native-witness-frame-repair-r9/build-target cargo test --manifest-path isolated/source-receipt-origin-r11/crates/yu-solver/Cargo.toml --locked --features shadow-apply-candidate replay_constructor_lineage_observes_rejected_cross_route_authentication
```

The first completed test trace is the observation target. A second attempt may be used only for an instrumentation-local diagnostic correction, after freeze, rehash and fresh reviewer delta acceptance; no solver fix or fixture change is permitted. Stop on any boundary or changed expected behavior.

Lean is conditional on the proof lane producing a genuine source-derived theorem: at most one check, 60s, one CPU, `-j1 -M1024`, pinned R9 Lean/Lake project and R11 absolute artifact path. No Lean run when no theorem artifact is produced. Any theorem type/audit failure remains visible; no repair or retry in this packet.

Retain exact argv, complete stdout/stderr, versions, exit and resource receipts in these exact paths:

```text
isolated/source-receipt-origin-r11/logs/cargo-1.argv
isolated/source-receipt-origin-r11/logs/cargo-1.stdout
isolated/source-receipt-origin-r11/logs/cargo-1.stderr
isolated/source-receipt-origin-r11/logs/cargo-1.resources.json
isolated/source-receipt-origin-r11/logs/cargo-2.argv
isolated/source-receipt-origin-r11/logs/cargo-2.stdout
isolated/source-receipt-origin-r11/logs/cargo-2.stderr
isolated/source-receipt-origin-r11/logs/cargo-2.resources.json
isolated/source-receipt-origin-r11/logs/lean-1.argv
isolated/source-receipt-origin-r11/logs/lean-1.stdout
isolated/source-receipt-origin-r11/logs/lean-1.stderr
isolated/source-receipt-origin-r11/logs/lean-1.resources.json
```

Absent second-attempt or Lean files must be marked NOT_RUN in the outcome, never synthesized. Only these exact Rust/proof/handoff/log paths are leased. R9 caches remain primary-owned and may be reused; cache contents are not evidence.

## Stop conditions and interpretation

Stop on pin mismatch, fixture/assertion/expected-output drift, event from a different invocation, instrumentation that changes the error kind/control flow or hides the failure, any attempt to weaken a receipt guard, a required source law being assumed, incomplete trace, theorem axiom/`sorryAx`, missing full types/audits, or resource boundary. Preserve all failures. No finding promotes a finite trace into a parent counterexample without the actual source judgment and source/native correspondence. Outcome must give exact first error owner/site if established, trace IDs and stage relation, producer-to-consumer invariant, responsible existing source owner, unresolved premises, all hashes, resources, review verdict and gates.
