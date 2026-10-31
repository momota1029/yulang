# R62 Rust handoff — Internal root pre-ancestry evidence

Sprint: `EFFECT-PERMISSION-INTERNAL-ROOT-POLICY/20261031-R62`, contract revision 2, SHA-256 `22dadec356ec91d6d575f771aadb5f9f82104b528dd7992500775b48fe8662da` (additive Lean-cone pin correction; Rust scope/source pins unchanged). Only `candidate_context.rs` had begun before this hash-only revision; `candidate_receiver.rs` was not edited.

Assignment: `/root/r62_rust`, handoff revision 1. Parent gate: original Simple-sub A/B claims and Yulang inference/executor soundness, effects, principality, and termination remain OPEN. This handoff is implementation/source evidence only and does not close a parent or authorize production.

Baseline: `437716cc057368932fc233809960ae0f378f9e60`. Relevant source pins before writing matched the admitted contract: `lib.rs` `25498cc1be404b12d060cbd47f77e78c23ad27b2b99113e15823bc8b6fa92ca4`; `candidate_context.rs` `cf73489b771067c2cd01d738a29e74f8a180c8fece782b5829871f02db36d106`; `candidate_receiver.rs` `3b60a58a1dba75b908607d91a76f49403314d3667a07987e29fc30fc4a7907e5`; read-only dirty dependencies `candidate_effect.rs` `75267bd1a195121ca79addb62b2a446a4b1b26afcc11e8c70aa1fa732c9e2909` and `candidate_scheme.rs` `bf8f5c80ce2761dc2a1235d2e02e348a91bc9e8965653db26b9abd4c8d6ca631`.

Role/runtime: requested `gpt-6-luna`, high. Observed model and effort remain UNKNOWN; no runtime telemetry was available to this worker. Current session: `EFFECT-PERMISSION-INTERNAL-ROOT-POLICY-R62`; worker ID: `/root/r62_rust`. No descendants.

## Outcome

Added a private `InternalUseRootEvidence` type and `RelationContext::checked_internal_use_root` reader in `candidate_context.rs`. The reader reuses the existing borrowed origin and source-drain records. It selects exactly one origin with the requested occurrence and relation pair, then checks the same completed source-drain receipt fields and returns its root relation as a typed pre-ancestry certificate. It adds no retained history, allocation, cache, owner record, or general inference path.

`checked_emission_for_internal_use` retains the exact preceding emission/readback/admission, physical Internal slot, unique-emission, and relation-pair guards. It then invokes the typed root reader and immediately makes the existing ancestry call against the returned relation. Thus the sequence and error variants remain: `MissingEmission`, `MissingAdmission`, `BoundMismatch`, `WrongEntrySlot`, `AmbiguousPhysicalSlot`, `MissingRelation`, `ForeignRelationPair`, the existing root-selection/drain errors (`AmbiguousUseRoot` / `MissingUseRoot`), then ancestry errors. The moved root scan preserves its iteration order and predicates.

`candidate_receiver.rs` is unchanged. The first physical edge still calls `current_internal_emission` before the existing outer emission ID, admission ID, physical slot, and bound identity comparison; later edges still call ancestry at their existing branch. The same entry-row/fact/use inventories are used. Rust source path: Internal use and formal-permission incidence in `Experiment::internal_formal_permission_incidence` -> current physical lower-row/lower-atom read and retained emission/admission/relation in `current_internal_emission` / `checked_physical_lower_edge` -> typed unique use-root plus completed source-drain evidence -> ancestry -> existing path and consumer. This does not demonstrate the Lean inventory/Native correspondence or successful outer Run.

## Files and checks

Exact leased paths written:

- `crates/yu-solver/src/candidate_context.rs` — SHA-256 `962af7c44b2e57ba50b7738e82785bd68b517e881ba08ea41c544c9314d60021`.
- `tasks/agent-loop/inbox/effect-permission-internal-root-policy-r62-rust.md` — SHA-256 reported with frozen handoff; a self-hash is intentionally not embedded.

Leased but unchanged: `crates/yu-solver/src/candidate_receiver.rs`, SHA-256 `3b60a58a1dba75b908607d91a76f49403314d3667a07987e29fc30fc4a7907e5`.

Checks performed: verified all admitted source/model hashes before editing and rechecked them immediately before the edit; manually inspected the extracted helper, surrounding validation order, unchanged first-entry/later-entry branch, and outer identity check. No build, tests, Cargo, formatter, Git command, scratch output, or generated file was used; those actions are excluded by the frozen assignment. This is not compile/test evidence or an independent review.

Prior evidence reused: R61 bounded ancestry source review (BOUNDED PASS, report body `ce97b0ccaca0c1c0b36944d14f0d545d2212dcdb22c559c83dac46ac2d8c83fc`) and the exact R45/R47 owner definitions cited by the contract. No Simple-sub bypass was used. No earlier evidence was rejected within this slice.

Remaining correspondence: Rust owner records are not yet proved equal to the R45/R47 primitive inventories and R60/R61 Lean `Native` on identical inputs. Actual source-to-Native construction, successful outer Run, pointer-to-Nat, arbitrary repeated-call resource/failure behavior, Context/R50, R51/publication, runtime, original A/B, soundness, principality, termination, and production remain OPEN. The proof lane owns its admitted Lean construction and should supply exact theorem/source-owner TODOs if Rust evidence cannot discharge correspondence. The fresh reviewer must attack owner selection, missing/duplicate roots, foreign use, stale/wrong slot, wrong drain/cause/pair, invalid ancestry, and first-entry-before-later-identity ordering.

Checks/budget: elapsed time was not independently metered; assignment cap is 1,500 seconds and aggregate sprint cap remains 6,000 seconds. No resource estimate is claimed. Next related in-envelope step: freeze this result and hand it to Luna for the already admitted joint review after both author lanes stop. No lease expansion requested.

Worker state: WAITING -> STOPPED for this assignment; WRITES STOPPED. No scratch or disposable generated paths were created. No commit-ready or review-complete claim.
