# Sprint EFFECT-PERMISSION-INTERNAL-ROOT-POLICY/20261031-R62 — construct the Internal-root policy reader

Status: ADMITTED_BOUNDED_RESEARCH. Primary: Luna (`/root`). Branch `yulang3`; baseline `437716cc057368932fc233809960ae0f378f9e60` (= `origin/yulang3`). Contract revision 2 (additive dependency pin correction; all outcome/lease/scope clauses unchanged). No new environment, worktree, cache, target, scratch, build or test process.

Authority: unchanged Yulang compiler/source semantics and the standing `research/simple-sub-intrusion` goal. This packet cannot alter source domain, accepted behavior, production authority, or original Simple-sub A/B claims. Prior milestone: R61 outcome `tasks/agent-loop/history/effect-permission-bounded-ancestry-20261031-r61-outcome.md` (SHA `c3376525f002a810b4d1158bf312a8b0681b847e3434bdaf3c3ee1f7d5c476ea`), independent BOUNDED PASS report body `ce97b0ccaca0c1c0b36944d14f0d545d2212dcdb22c559c83dac46ac2d8c83fc`.

## Original goal and this packet's result

The original ongoing goal remains soundness, effects, principality and termination of Yulang inference/execution. The original parent claims/quantifiers and source domain are unchanged and remain OPEN. R60/R61 construct successful candidate-search readers but retain the first-entry Internal callback as an explicit `Physical -> Except Failure (InternalReceipt)` parameter.

This packet targets that remaining policy input. Factor the actual Rust first-entry checks into a typed pre-ancestry root certificate and a distinct ordered ancestry check, then construct the R60/R61 Internal-root reader from the same owning Internal-use / formal-permission / source-drain / physical-emission inventories. Apply the resulting policy to the same Native/Inputs used by R60/R61, without an independent Internal callback premise.

Success evidence:

1. The Rust stages reuse the same owned records, enforce the same exact use, owner, formal registration, root-component, fact endpoints, current physical slot, unique emission/admission/relation, and unique completed source-drain root checks, then invoke ancestry in the existing order. Error variants, check order and observable inference behavior remain unchanged. No retained history/identity, allocation scheme, or general inference path is added.
2. The Lean reader is computed from primitive indexed inventories / the exact R45/R47 guard definitions, returns `InternalReceipt` only after every pre-ancestry guard succeeds, and leaves the existing ancestry visitor as a separate final stage. Prove the source-root/current-slot projection equations and apply it to the R61/R60 constructed consumer on identical inputs with no independent `internal` callback parameter.
3. Fresh independent review attacks owner selection, missing/duplicate roots, foreign use, stale/wrong slot, wrong drain/cause, invalid ancestry, and preservation of the existing first-entry-before-later-identity-check ordering. Complete theorem types and transitive axiom audits accompany the proof.

A missing owner identity, counterexample, or source-behavior difference stops that affected claim. A theorem over assumed `LocalLaws`, callback fields, proposition wrappers or constructor-authored receipts alone does not meet success.

## Governing source and frozen inputs

Rust source owner: `Experiment::internal_formal_permission_incidence` in `crates/yu-solver/src/lib.rs`, `Experiment::current_internal_emission` in `crates/yu-solver/src/candidate_receiver.rs`, and `RelationContext::checked_emission_for_internal_use` in `crates/yu-solver/src/candidate_context.rs`. The first-entry call site is `find_lower_path` in `candidate_receiver.rs`; it calls the root reader at the first physical edge and calls ancestry on later edges. Preserve this sequence and the outer later physical-identity comparison.

Frozen source / model pins at admission:

- `crates/yu-solver/src/lib.rs`: `25498cc1be404b12d060cbd47f77e78c23ad27b2b99113e15823bc8b6fa92ca4` (read-only).
- `crates/yu-solver/src/candidate_context.rs`: `cf73489b771067c2cd01d738a29e74f8a180c8fece782b5829871f02db36d106`.
- `crates/yu-solver/src/candidate_receiver.rs`: `3b60a58a1dba75b908607d91a76f49403314d3667a07987e29fc30fc4a7907e5`.
- Read-only current-worktree dependencies, not write leases: `candidate_effect.rs` `75267bd1a195121ca79addb62b2a446a4b1b26afcc11e8c70aa1fa732c9e2909`; `candidate_scheme.rs` `bf8f5c80ce2761dc2a1235d2e02e348a91bc9e8965653db26b9abd4c8d6ca631`.
- R45 `InternalPermissionIncidenceR45.lean`: `9ff4fd544375a3d4a46100647cba93ddde6f34bebd767ba402f3bd3d35a84b1f`.
- Complete additional imported cone: R39 `ComputationPermissionEntryR39.lean` `748cd52ff7962962940a3767ffa6a0b2d8def16d80e65e682282d1fa2b79560e`; R48 `ProviderEntryArrivalR48.lean` `b85dfad5c0e80f7fbc2480e7f38421cc6c50107144d9abb160e688208b192575`; R49 `AuthenticatedResidualConsumerR49.lean` `4fc4380f3ad1827ecf155f982e5186b32d6d66d91909039fb118063d8f1e2df2`; R55 `SourceInternalContextR55.lean` `7aaecdd3d358d769123f00acb4b19b4d7d61ccfef98fee4eb53179da4a105123`; R57 `ProviderNativeContextR57.lean` `804b3431c2e585370b8adc28f59b36c26a36e1524f42278a860823c9bd7eaa63`.
- R47 `CurrentEmissionOwnershipR47.lean`: `d64c54f7c977e110305a76e6437fc87c8ff14201a4d69eb0bbcb5ee0e1cd8b9c`.
- R58 `ReachedSlotSearchR58.lean`: `431d3b4cb031fd86ad4a0537c1c8a42adecb8433f3ef775b3371eb37611b3079`.
- R59 `ReachedSlotCompletenessR59.lean`: `d0d1a33e416a13ed29e5ba018f5adf1e0a71b6b5886d2d04f74956522836bfab`.
- R60 `NativeLocalDecodeR60.lean`: `3eccc41902a8a8768a55cac020efd4936517da3feb2d91a7ec158994a133ca20`.
- R61 `BoundedAncestryR61.lean`: `9e1c783016bc14487dd0a4ebc2839dfab0dc3daf911ee88fa02f3624e2ad60a4`.

Prior source/model definitions are premises only at their exact admitted scope; no Rust-to-Run, pointer-to-Nat or arbitrary allocator/failure equivalence is inferred. Authors rehash all inputs before writes; dependency drift returns to Luna.

## Exact lanes and leases

**Rust implementation, `/root/r62_rust`, Luna/high, 1,500 seconds:** write only `crates/yu-solver/src/candidate_context.rs`, `crates/yu-solver/src/candidate_receiver.rs`, and `tasks/agent-loop/inbox/effect-permission-internal-root-policy-r62-rust.md`. Factor the existing owner-root guards from the ancestry call into a private pre-ancestry evidence type/reader and keep the ancestry call at its original point. Reuse existing owned records and preserve errors/order. No tests/build/Cargo/formatter, no edits to other source, tests, semantics or shared state.

**Constructive proof, `/root/r62_proof`, prover Sol/high, 2,100 seconds:** write only `notes/theory/lean/YulangClosure/InternalRootPolicyR62.lean` and `tasks/agent-loop/inbox/effect-permission-internal-root-policy-r62-proof.md`. Build the reader out of primitive inventories and guard definitions; audit all new roots with pinned Lean 4.35.0, print exact types and complete axioms, and apply the callback-free policy to the R61/R60 consumer. No root imports, toolchain edits, cache/scratch files, Lake project changes or assumed source-instance theorem.

**Fresh reviewer, `/root/r62_review`, compiler_referee Sol/low, 1,200 seconds:** after both authors stop and inputs/artifacts freeze, read only the frozen contract, dependencies, Rust/proof artifacts and write only `tasks/agent-loop/inbox/effect-permission-internal-root-policy-r62-review.md`. No author may review their own contribution. Verify type separation, guard/failure order, same-owner selection, exact first-entry order, Lean completeness/types/axioms, and explicit boundaries.

**Primary Luna, 1,200 seconds including 500 closeout:** owns authority, intake, review/adjudication, state, exact-path staging, commit and push. Primary may write contract/admission/outcome/current state only. No Astra assignment. Aggregate sprint budget 6,000 seconds. No more than these three assignments; no descendants. Existing checkout/read-only Lean stdin only. Build/test commands are outside this packet and not authorized.

## Falsifiers, exclusions and stop conditions

Falsifiers: valid permission with missing root; foreign use; duplicate root; stale or wrong physical slot; wrong source drain, cause or pair; invalid/non-ancestral relation; swapped source owner; Catch bypass; and any changed first-entry / later identity-read error order. Preserve the two distinct R58 phases. A resource abstraction cannot be presented as exact allocator behavior.

OPEN after this packet unless independently closed: actual Rust source records to the same Lean inventories/Native and successful outer Run; pointer-to-Nat; Internal root extraction from arbitrary full source programs; arbitrary repeated-call allocator/resource/failure simulation; complete Context/R50 and R51/publication; Rust runtime; original A/B, soundness, principality, termination, complete hygiene and production.

Stop on semantic drift, a missing owner record requiring a new producer/lease, dependency hash change, reviewer finding outside current authority, or budget. Do not widen source domain or weaken any premise. Keep pending32, all UNKNOWN worker observations and all12 quarantined leases. Record exact active/STOPPED receipts; no fictional RUNNING state. Commit only after independent BOUNDED PASS, exact outbound-range review and coherent outcome/state synchronization; never stage unrelated dirty files or force-push.

## Revision 2 — transitive Lean pin correction

The original admission named R39/R45/R48/R49/R55/R57–R61 but did not individually hash-pin R39, R48, R49, R55 or R57. Revision 2 adds the five exact current-source SHA-256 values above. The primary recursively enumerated the local Lean import closure before this correction; all 11 existing YulangClosure modules in the R62/R61/R60/R59/R58/R57/R55/R49/R48/R47/R45/R39 chain are now individually pinned. No proof statement, theorem premise, source scope, write lease, resource budget or semantic authority changes. R62 proof had not written; Rust lane confirmed only `candidate_context.rs` had begun and its inputs remained unchanged. Both lanes must acknowledge the revision before continuing with any dependency-sensitive write.
