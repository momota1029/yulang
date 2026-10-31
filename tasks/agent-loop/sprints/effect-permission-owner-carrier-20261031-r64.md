# Sprint EFFECT-PERMISSION-OWNER-CARRIER/20261031-R64 — construct the authentic Lean Owner and Call

Status: ADMITTED_BOUNDED_RESEARCH. Primary: Luna (`/root`). Branch `yulang3`; baseline `9c7dd3d74b56bccce776abb18d597d62f9161ba3` (= `origin/yulang3`). Revision 1.

Authority: unchanged Yulang semantics and standing `research/simple-sub-intrusion` goal. No semantic change, source-domain narrowing, original-parent alteration, or production authority. R63 is CLOSED BOUNDED PASS for research only. Its theorem applies to a supplied typed Lean `Owner` and `Call`; the actual Rust-carrier interpretation remains OPEN.

## Fixed outcome

Construct R63's `Owner` and `Call` from the actual private Rust `InventoryPackage` in `candidate_receiver.rs`, retaining complete owner identity, every source/native competitor, semantic facts with all associated provenance occurrences, and every TermView consumed by R55/R62. Derive TermViews from owning terms and their required children. Derive use/Catch/provider coordinates from the package's actual source-call/schema records. Prove complete-field and consumed-lookup coverage, then apply R63 to those same constructed values.

The carrier is an explicit structural reification of the existing package, not an independently supplied `Owner`, expected package, or unconstrained mirror. Preserve legitimate empty inventories when the actual owner is empty. No nonempty-list assumption may stand in for completeness.

## Success evidence and falsifiers

1. Rust reads the exact owner tables and provenance/term owners, retains every source occurrence for each admitted semantic fact, and constructs fields by checked owner-local indices and identities. Construction remains private, fallible, in-memory, and observation-only; no serialization, pointer-to-integer cast, inference/forwarding/routing/subtraction change, or source producer edit.
2. Lean constructs one R63 `Owner` and `Call` from the typed carrier fields. Prove exact complete-field equations, every R55/R62 consumed TermView lookup equation, all competitor coverage, provenance multiplicity, owner/call coordinates, and apply R63 with those same values. Do not assume a faithfulness predicate equivalent to the bridge.
3. Fresh independent review attacks omitted live receipts/facts/TermViews, lost provenance occurrences, omitted competitors, mixed owner IDs, wrong source-call/schema coordinates, legitimate empty fields, and theorem/type/axiom completeness.

Falsifiers include dropping any extant receipt/fact/provenance occurrence/consumed TermView or competitor, changing a source coordinate, or mixing owners while still claiming an authentic package. If a required native owner cannot expose a needed complete field read-only, stop and return that exact source owner; do not expand leases.

## Frozen inputs

- Baseline HEAD: `9c7dd3d74b56bccce776abb18d597d62f9161ba3`.
- Rust `candidate_receiver.rs`: `3119ed33909f85ddbee5864b8f0e910ee65c69fdf3d056d600b95deab0cbf84a` (write lease).
- Rust `lib.rs`: `25498cc1be404b12d060cbd47f77e78c23ad27b2b99113e15823bc8b6fa92ca4` (read only).
- Rust `candidate_context.rs`: `962af7c44b2e57ba50b7738e82785bd68b517e881ba08ea41c544c9314d60021` (read only).
- Rust `term.rs`: `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1` (read only).
- R63 `RustInventoryRequestR63.lean`: `74381ebd183fa7d26f626fe166f848e1312377fca855cd08beb92d9256edfacc`.
- R62 `InternalRootPolicyR62.lean`: `e76e41a853673e75555cc5e603f1f84c456332794980613c554a2d69af8d976e`.
- R63 review: `caefe50b329bb1ae28cd456d0f5adb229ee19e946e1b3206d3d0aa184ab91f4c`; outcome: `96dc181ebb53a4ebcdd1dfefe4f08728fa20d3d6d2b41e11c76eb6f4de61ee90`.

Rehash direct inputs before writing. Read-only Rust owners and Lean dependencies may not be edited. No writes to `candidate_context.rs`, `lib.rs`, `term.rs`, `candidate_effect.rs`, `candidate_scheme.rs`, or source constructors.

## Exact lanes, leases, resources

**Rust implementation — `/root/r64_rust`, Luna/high, 1,800 seconds.** Write only `crates/yu-solver/src/candidate_receiver.rs` and `tasks/agent-loop/inbox/effect-permission-owner-carrier-r64-rust.md`. Extend the existing private InventoryPackage construction with complete fact provenance and TermView ownership/lookups. No builds, tests, Cargo, formatter, or extra source-owner edits.

**Constructive Lean — `/root/r64_proof`, `lean_prover` Sol/high, 1,800 seconds.** Write only `notes/theory/lean/YulangClosure/BrandedInventoryOwnerR64.lean` and `tasks/agent-loop/inbox/effect-permission-owner-carrier-r64-proof.md`. Use pinned Lean 4.35.0 stdin-only audit, `-j1 -M1024`; preserve full theorem types and transitive axiom reports. No Lake project, cache, scratch, target, or build writes.

**Fresh reviewer — `/root/r64_review`, compiler_referee Sol/low, 1,200 seconds.** Start only after both author lanes freeze and STOP. Write only `tasks/agent-loop/inbox/effect-permission-owner-carrier-r64-review.md`. No checker/build/test reruns, Git, scratch/cache/target/environment, descendants, or author contact outside the report's bounded review.

**Primary Luna — 1,200 seconds including 500 closeout.** Owns exact state, intake, review/adjudication, durable records, explicit-path staging, commit and push. No Astra, no descendants. Aggregate cap 6,000 seconds. Existing checkout only; create no worktree/environment/cache/target/scratch/build directory. Keep pending count 32 and all UNKNOWN/quarantined leases intact.

## Parent application and OPEN limits

A successful bounded result must connect the actual Rust InventoryPackage to one complete typed Owner/Call and instantiate R63 without changing its quantifiers. Actual compiler execution, outer successful `Run`, arbitrary allocator/resource/failure correspondence, original A/B, whole-program soundness/effects/principality/termination, full hygiene and production remain OPEN. The empty mathematical Owner witness is not a reason to reject legitimate native empty inventories; prove authenticity and completeness at the carrier constructor.

Stop for missing read-only native provenance/TermView owners, dependency drift, any observable behavior change, unrepresentable identity, budget exhaustion, or a reviewer finding requiring a new owner/write lease. Only Luna integrates a reviewed coherent checkpoint.
