# Sprint EFFECT-PERMISSION-REACHED-SLOT-SEARCH/20261031-R58

Status: ADMITTED, bounded research only. No production or whole-language closure.
Branch: yulang3; baseline: 4b1a0380888619adee0f06a37ad49243a2e86a95
Original goal: Yulang inference/executor soundness, effects, principality, termination.
Authority: rules/goal-driven-sprints.md §§1–4; unchanged Simple-sub source domain and A/B claims.
R57 input: tasks/agent-loop/history/effect-permission-provider-native-context-20261031-r57-outcome.md (b33e106b1f6ca031b548a1516e8e06b278e100deb5dd9685ac91f2608232d0cc); independent R57 review hash ea4e5bb4f60b4b4b9d314bb44d1092777e0e49a123ca9b458a79f8225bd9949e.

## Outcome

Discharge or precisely isolate the remaining operational-search premise in the R57/R50 effect-hygiene Context: model Rust `certified_lower_paths` as its actual bounded LIFO worklist, including physical and Support-member steps, checked owner reads, branch-local `seen`, exact work accounting, and error-to-unavailable behavior. Prove successful results refine exactly the checked candidate paths and connect only successful paths to R57/R50 readers.

Source baseline: `candidate_receiver.rs` SHA 8d491e52ed9922e982c93a694e8c065bb065ca5f50bff76c255a5303eba1e016; read-only `candidate_context.rs` SHA 8fa738f5050b642a9a52a55ffb2744cadeb95a0a0decefcc336663430deb4f89; `candidate_source.rs` SHA 96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a; R57 model SHA 804b3431c2e585370b8adc28f59b36c26a36e1524f42278a860823c9bd7eaa63.

Preserve the two call policies: Catch invokes search with `entry=None`; permission entry invokes with `entry=Some(self)`, authenticates its first physical edge through the actual internal-emission reader, then checks same-use ancestry on subsequent physical edges. Every physical edge uses checked current slot/owner readers. LIFO order, support-tail rejection, branch-local cycle avoidance, ambiguity rejection, `try_reserve` failure, overflow and `SCOPED_WORK_LIMIT=65536` exhaustion remain observable. Do not claim unconditional equivalence with all-slot R57 traversal: malformed unreachable slots can make conservative enumeration fail where this worklist never reads them.

## Success and falsifiers

Success: a source-indexed small-step Lean relation matches the relevant Rust transitions and error boundaries; theorem roots establish accepted result soundness/completeness relative to checked reached candidates, and valid-input connection to R57/R50. Explicitly state every abstract premise that Rust projection does not yet establish. Keep separate `(root,target,mode)` queries; prove any cross-mode reuse only under a stated agreement premise, otherwise expose representation mismatch.

Falsifiers: unreachable malformed slot; malformed reached alternative; second successful path; cyclic dependencies; late ancestry failure; stale/foreign/reversed physical owner; support tail; off-by-one work limit/overflow/allocation failure; same `(root,target)` queried in Catch and entry modes. No success theorem may erase a reached failure, include an unchecked path, or silently merge modes.

## Lanes, exact leases and resources

- Rust: `/root/r52_rust`, Luna/high, write `crates/yu-solver/src/candidate_receiver.rs` and `tasks/agent-loop/inbox/effect-permission-search-correspondence-r58-rust.md`; read-only context/source/model dependencies. Make only a necessary private factoring change; a source-grounded correspondence map is acceptable if factoring adds no value. No tests/build/Cargo/formatter/typecheck.
- Lean: `/root/r52_proof`, constructive proof, write `notes/theory/lean/YulangClosure/ReachedSlotSearchR58.lean` and `tasks/agent-loop/inbox/effect-permission-search-correspondence-r58-proof.md`. Use only pinned Lean 4.35.0 stdin audit in existing `notes/theory/lean`, one CPU, `-j1 -M1024`, <=120s per audit. Preserve full theorem types, command/input/stdout/stderr hashes, resource receipts and complete transitive axiom audits. Disclose standard axioms; no project axiom/sorry/native evaluation.
- Review: fresh `/root/r37_inventory_review`, read-only; `tasks/agent-loop/inbox/effect-permission-search-correspondence-r58-review.md`. Check source transitions, theorem types/axioms, mode split, failure and falsifier coverage, exact hashes. No authorship.
- Primary: `/root`; owns contract/state/Git, adjudication and bounded application to R57/R50.

Exact implementation/proof/review handoff leases above; immutable reads: `candidate_context.rs`, `candidate_source.rs`, `ProviderNativeContextR57.lean`, R57/R50 receipts and direct dependency cone. No other source path, scratch, cache, target, environment, worktree or persistent process. Reuse current checkout and existing Lean toolchain only. No Astra.

Budget 6000s total: Rust 1200; Lean 2400; review 1200; primary 1200 (includes up to 500s closeout); Astra 0. Each lane freezes exact bytes and a writes-stopped receipt before review. Stop on a source/model counterexample, missing owner read, required producer change, budget, user STOP or session end; keep unknown leases quarantined.

## Boundaries and integration

Required prior work: R47 physical-owner/ancestry, R48 provider arrival, R49 authenticated consumers, R50 exact Context, R55 source-internal Context, R57 provider-native Context. Apply every proved result to that existing Context and name the exact remaining premise.

R58 does not prove Rust compilation/runtime, projection completeness, R51 primitives, publication, original A/B, inference soundness, principality, termination, full hygiene or production. No semantic changes. Review must be independent of both authors and of moving bytes. Primary stages only explicit reviewed paths, checks outbound range, updates compact state/outcome and pushes coherent checkpoint. Current state must remain <=16KiB and preserve all 32 pending items, UNKNOWN workers and quarantines.
