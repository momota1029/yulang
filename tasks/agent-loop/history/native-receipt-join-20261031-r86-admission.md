# R86 primary admission — native receipt join

Sprint: `NATIVE-RECEIPT-JOIN/20261031-R86`  
Contract SHA-256: `fbba407ea6a59e2a0856a369e8e8ea815766c3e241460fe3ea84fa493343453b`  
Input manifest SHA-256: `e94dfb586a42052073620809ec17936c9c78e3025e017a1ffedea89c2df8debc`  
Baseline: `a44adf1f2fda99f896debf11b5f58c207728b030`.

## Dispatch decision

At the R85 boundary, `next_action_selector` recommended a bounded R86 two-receipt join, grounded in the actual source mismatch: `Origin` retains the pending receipt, terminal completion appends a completed clone, and both the checked-root and saved-receiver paths inspect the Origin-attached receipt. The source worker must first inventory the finite seven-file module closure, including `pub(super)` writers and rollback; the proof worker must model both records without changing R84/R57 semantics. The direct relation-join route is admitted. No source code change is admitted because both consumers must be understood together and the safe owner-local repair has not been established.

Altitude remains the original R66 `Root` application within original Simple-sub A/B. The bounded outcome is the exact two-record relation and its application or a formal no-go at the unchanged R84 `Primitive` interface. The concrete method is an indexed relational join with a forward simulation over the two physical receipts, preserving all Origin competitors. Its falsifiers and review seam are specified in the contract.

Beyond this packet, any Rust consumer/producer edit or change to accepted root semantics requires a separate versioned admission after the full source inventory and independent design review. Original A/B, source extraction and production authority remain unchanged.

## Exact leases and lanes

- Proof author (`lean_prover`): `notes/theory/lean/YulangClosure/NativeReceiptJoinR86.lean`; handoff `tasks/agent-loop/inbox/effect-permission-native-receipt-join-r86-proof.md`.
- Source researcher, read-only Rust: `tasks/agent-loop/inbox/effect-permission-native-receipt-join-r86-source.md`.
- Fresh independent review: `tasks/agent-loop/inbox/effect-permission-native-receipt-join-r86-review.md` (primary owns writes).
- Primary owns the contract, manifest, admission, `current.json`, review receipt, exact-input authorization and Git.

The complete pin list and line ranges are in the input manifest. The seven Rust paths are the complete current `rg -l` hit set for `source_drain_receipt`, `source_drain_completions`, `checked_internal_use_root`, and `owned_projection_source_drain` under `crates/yu-solver/src`. Each full file is authorized read-only; no path outside that list may be added without a versioned amendment. Lean reads are limited to the pinned R57/R84/R85 and original-claim sources.

## Authority, model and resources

The original ongoing user goal authorizes this bounded proof/source continuation. Requested routing: proof `lean_prover`, Sol/high; source `researcher`, Sol/high; independent result review `compiler_referee`, Sol/medium. Observed model values remain UNKNOWN until runtime evidence. Astra budget: 0. Luna remains sole dispatcher, lease owner, reviewer assigner, adjudicator, state writer, integrator and Git actor.

Budget: 3,600 seconds total (proof 1,400; source 1,000; review 700; primary 500). Lean: no more than two separately authorized in-memory stdin calls, 120 seconds each, `-j1 -M1024`, one Lean thread, no scratch/cache/target. The exact input must include accepted R85/R84 query receipts and all new R86 types/axioms. First call requires frozen inputs and independent review; one diagnostic-directed repair needs Amendment 01, fresh review and a new pushed authorization. No third call.

No Rust/compiler mutation, builds, tests, Cargo/Lake, formatter, `.olean`, target/cache/scratch, installation, environment or worktree. All work stays in the existing checkout. Unknown workers and quarantined paths remain untouched. Stop on hash drift, an unaccounted writer, semantic change, unsupported premise, falsifier, resource limit or exhausted call cap.

## Expected review and next trigger

The reviewer checks exact field preservation through receipt join, indexed uniqueness/rejection, all competing Origins, the relation of the projected evidence to unchanged R84 and R57 definitions, complete theorem types/axioms, and the exact flattened input/result. An unaccounted write, duplicate acceptance, altered non-bit field, rollback separation, lost competitor or selector mismatch defeats the relevant claim.

Next dispatcher consultation is due only at a material counterexample, frozen source/proof integration seam, required consumer-policy change, out-of-closure writer or budget exhaustion. No review panel or additional planning round is authorized.
