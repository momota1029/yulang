# Sprint EFFECT-PERMISSION-LOCAL-DECODING/20261031-R60

Status: ADMITTED, bounded research and private helper implementation only. No production or whole-language closure.
Branch: yulang3; baseline: `05729971678af86f7e0cc5d426d838e6c52dde02` (R59 closeout pushed).
Original goal: Yulang inference/executor soundness, effects, principality, termination.
Authority: rules/goal-driven-sprints.md §§1–4; unchanged Simple-sub source domain and A/B claims.

## Outcome

Construct the concrete borrowed R58 `Readers.rows`, `Readers.views` and `Readers.physical` from the same owner-derived native records used by R57. Prove, without assuming a blanket reader-soundness predicate, that these constructed readers satisfy:

```lean
LocalDecode (constructedReaders native) (constructedInputs native search)
```

Use this to instantiate R59's successful-search candidate theorem on those same inputs and apply it to the existing R49/R57 hygiene consumer without an extra decoder assumption.

The physical field must derive `StepReads` and exact endpoint preservation from actual current-slot, admission, emission and relation checks. The Support field must derive the view/member/family/closed-tail equations from the same retained view inventory. Reader construction and its proofs must preserve the actual validation and error order.

Falsifiers: foreign state, swapped physical lane/index, stale readback, duplicate slot emission, wrong relation pair, reordered Support member, canonical-row substitution, malformed Support tail and crossed owner/view identity. A falsifier must remain unavailable; do not silently accept it through a canonical row or a different owner.

Keep ancestry policy separate from physical reads. Do not move ancestry validation earlier or change failure priority to make the reader proof easier. Stop on any required producer/source policy change or a counterexample to the proposed sealed borrowed reader.

## Pinned inputs

- R59 reviewed closeout commit: `05729971678af86f7e0cc5d426d838e6c52dde02`.
- R59 outcome: `tasks/agent-loop/history/effect-permission-search-completeness-20261031-r59-outcome.md`, SHA-256 `a60e7aade5fef31efde21cdb4a94ad05435e185e6164b47c0d69dcf32c0eeb58`.
- R59 independent review: `tasks/agent-loop/inbox/effect-permission-search-completeness-r59-review.md`, SHA-256 `59658c916da9d5cf6f766568045b1de7f1dc3348fec0076118ab81d3c9a694b3`.
- R59 model: `notes/theory/lean/YulangClosure/ReachedSlotCompletenessR59.lean`, SHA-256 `d0d1a33e416a13ed29e5ba018f5adf1e0a71b6b5886d2d04f74956522836bfab`.
- R58 model: `notes/theory/lean/YulangClosure/ReachedSlotSearchR58.lean`, SHA-256 `431d3b4cb031fd86ad4a0537c1c8a42adecb8433f3ef775b3371eb37611b3079`.
- R57 model: `ProviderNativeContextR57.lean`, SHA-256 `804b3431c2e585370b8adc28f59b36c26a36e1524f42278a860823c9bd7eaa63`.
- R55 model: `SourceInternalContextR55.lean`, SHA-256 `7aaecdd3d358d769123f00acb4b19b4d7d61ccfef98fee4eb53179da4a105123`.
- Receiver baseline: `crates/yu-solver/src/candidate_receiver.rs`, SHA-256 `8d491e52ed9922e982c93a694e8c065bb065ca5f50bff76c255a5303eba1e016`.
- Read-only context: `crates/yu-solver/src/candidate_context.rs`, SHA-256 `8fa738f5050b642a9a52a55ffb2744cadeb95a0a0decefcc336663430deb4f89`.
- Source: `crates/yu-solver/src/candidate_source.rs`, SHA-256 `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a`.
- Also preserve the exact R49 consumer and R39/R45/R47/R48 source/model dependency hashes in the R59 proof handoff; abort on any mismatch.

## Lanes, exact leases and resources

- Rust implementation: `/root/r52_rust`, Luna/high. Write only `crates/yu-solver/src/candidate_receiver.rs` and `tasks/agent-loop/inbox/effect-permission-local-decoding-r60-rust.md`. Implement a sealed borrowed reader view from `ProviderNativeContextProjection`, using the actual retained views/rows and existing checked physical helper. No new identity/history, no producer changes, and no changes to search/forwarding behavior. Read-only `candidate_context.rs` physical and ancestry implementations. No tests/build/Cargo/formatter/typecheck.
- Lean proof: `/root/r52_proof`, constructive. Write only `notes/theory/lean/YulangClosure/NativeLocalDecodeR60.lean` and `tasks/agent-loop/inbox/effect-permission-local-decoding-r60-proof.md`. Construct all three readers; prove each field of `LocalDecode` from the concrete owner projections; apply R59's result to the same constructed inputs without an extra decoder assumption. Keep actual Rust-to-Run simulation and inner ancestry/resource correspondence OPEN. Use pinned Lean 4.35.0 stdin audit only in `notes/theory/lean`, one CPU, `-j1 -M1024`, <=120s each; preserve full types/axiom reports, hashes and resource receipts.
- Independent review: `/root/r37_inventory_review`, read-only, fresh non-author. Write only `tasks/agent-loop/inbox/effect-permission-local-decoding-r60-review.md` or return report for primary placement if the role is read-only. Review field-by-field Rust construction, exact owner/index/order correspondence, all theorem types/axioms, falsifiers and hashes after both lanes freeze.
- Primary: `/root`; owns current state, lease changes, admission, adjudication and Git.

Fresh budget: 4800 seconds total: Rust 1200, Lean 1800, review 900, primary 900 (includes up to 500 closeout); Astra 0. Existing checkout and pinned Lean stdin only. No builds/tests/typecheck, cache, scratch, target, persistent process, environment or worktree.

Before dispatch, synchronize the live roster; all R59 authors/reviewer must be STOPPED and no other writer may own the receiver. Preserve all 32 pending questions, every UNKNOWN observation and all 12 quarantined paths. Keep current.json <=16 KiB. Each author freezes exact bytes and reports WRITES STOPPED before review. Stop on a missing owning read, required producer change, counterexample, budget, user STOP or session end.

## Boundaries

R60 removes the explicit `LocalDecode` premise only for the exact constructed owner/input projections and existing R49/R57 application. It does not prove arbitrary borrowed-owner extraction, general source-run simulation, full inner ancestry traversal/resource equivalence, complete Context/R50 interpretation, Rust runtime, original A/B, inference soundness, principality, termination, complete hygiene or production authority. No conditional model result is parent-theorem closure.
