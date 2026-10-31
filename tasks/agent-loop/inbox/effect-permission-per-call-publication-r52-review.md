# R52 independent review — bounded PASS

Reviewer: `/root/r37_inventory_review`. Both authors were confirmed STOPPED/WRITES STOPPED before review.

**No BLOCKING, major, or minor correctness finding remains open in the bounded per-call capture and conditional Lean bridge.** This establishes source-level identity and cut containment, not concrete execution or complete Rust-to-R51 extraction.

## Rust capture

`candidate_receiver.rs:429–439` selects a unique record by `(publication identity, original plan index)` before endpoint comparison. The checked atomic identity allocation cannot wrap; exhaustion disables observation.

At lines 1008–1037, each Forward captures origin/completion/emission lower cuts and physical-slot state immediately before calling `constrain_live_effect` with the unchanged endpoint, upper, fact ID and cause. After a successful return, it captures upper cuts and accepts evidence only from that call's windows. Plan indices retain suppressed positions; filtering Forward decisions does not renumber calls.

`candidate_context.rs:2982–3036` validates half-open origin and completion intervals and requires exactly one matching origin and exact completion copy within those intervals. Older, later, missing, duplicate, malformed or out-of-range evidence is unavailable. New emissions are selected only from `[emission_cut, emission_end)` and retain exact slot, readback, admission, relation pair and source-drain ancestry checks.

AlreadyPresent requires the actual pre-call slot, unchanged prior count and no new matching emission. Zero prior emissions remains valid. Observer preparation, identity allocation and evidence-selection failures disable observation through `Option`/observer flags without changing successful Forward order or arguments. Existing plan allocation and actual forwarding errors retain their prior behavior, preserving R51 B1.

## Repeated calls and source envelope

The Lean `[7,8,7]` witness distinguishes equal task/occurrence/cause records through separate keys and windows. Rust's concrete experiment canonicalizes and deduplicates terminal endpoints before planning, so this witness is abstract evidence, not a demonstrated native execution. A hypothetical duplicate endpoint outside that source envelope may make observation unavailable due to preplanned mode/slot; no reachable blocker exists in the admitted deduplicated source domain, and per-call windows prevent borrowing neighboring evidence.

## Lean bridge and audit

All 25 theorem statements, bodies, final printed types and complete axiom reports were inspected. `project` constructs R51 call, receipt, completion and per-call snapshot tables from the same installed captured record. `captured_instantiates_r51` derives that record's `CallReads`, `DrainReads` and `ModeReads` from explicit local source premises. `captured_forward_native` applies the result using the same probe and additional native reads.

The proofs establish key uniqueness, index non-aliasing, half-open boundaries and ordered origin/completion/emission separation. Concrete witnesses cover swapped indices/publications, earlier receipts, later evidence, boundary errors, missing completion and observer loss. Axiom census for `YulangClosure.PerCallResidualPublicationR52`:

- No axioms: `key_unique`, `identity_unique`, `distinct_keys_no_alias`, `window_disjoint`, `earlier_rejected`, `later_rejected`, `lower_cut_inclusive`, `upper_cut_exclusive`, `emission_separation`, `call_identity_fixes_index`, `concrete_repeated_calls_distinct`.
- `[propext]`: `origin_separation`, `completion_separation`.
- `[propext, Quot.sound]`: `captured_instantiates_r51`, `captured_forward_native`, `captured_missing_completion_unavailable`, `later_emission_source_rejected`, `unavailable_observer_successful_forward`, `concrete_same_record_bridge`, `concrete_source_premises`, `concrete_parent_application`, `concrete_repeated_publication`, `concrete_key_and_cut_attacks`, `concrete_completion_gap_keeps_call`, `concrete_observer_loss_preserves_return`.

No final `Classical.choice`, `sorryAx`, project axiom or unchecked native-evaluation dependency appears.

All six audits' encoded stdin/stdout/stderr byte archives were decoded in memory and matched every recorded byte count and SHA-256. Audits 1–4 remain failed construction history; Audit 6 alone authenticates the final 25-root artifact. Audit 6 used pinned Lean 4.35.0, one CPU, `-j1 -M1024`, exit 0, 7.090808 seconds, peak RSS 910092 KiB. The reviewer did not rerun Lean.

Audit 6 hashes:

- stdin `0f3bd20ec6ced56a9be3b1049bcb236af56cd8f2abab25c3cdd1b302b9c4a9f0`
- stdout `c9d27c0743415978dcf44ea2f27e3dee980f82915628f6949c0b66a051da6679`
- empty stderr `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`

## Remaining limits and frozen hashes

Source premises remain for faithful identity encoding, complete owner inventories, cut monotonicity, lifetime/canonicalization interpretation, final native reads and whole-publication frame/fact/plan correspondence. R52 does not establish R51's complete `observe` predicate or final prefix/suffix frame. Concrete Rust compilation/runtime, full extraction, original A/B, soundness, principality, termination, complete hygiene and production remain OPEN.

| Artifact | SHA-256 |
|---|---|
| R52 revision-2 contract | `3cd430e0d8ff9f566c631e0d4db34bd1c00131efdfcb98dde226e3578e455e06` |
| `candidate_receiver.rs` | `2707cbe4c41a4f91816ef85fe18ac58cc3f5dfe22a648cdcd598215843cb5d4d` |
| `candidate_context.rs` | `c9deb23ebb2b7762f6404c6529231f3581e9959082ee301e03eb1c0895d111eb` |
| Rust handoff | `2183c859ec7b1ce8b75aaf0b93efe4af1c9fdc8012b162833079af03ba8d7cf3` |
| R52 Lean | `d0ffaad36139148c3898d70c9da2e03d1b0e17cbb8b71841f751a8720570e73e` |
| Proof handoff | `da53deb52aed9447c61ef46fb27288cc53e569167221ade7bae5a77d6e58ea6a` |

Read-only `lib.rs`, R51/R50 models and R51 review/outcome match contract pins. The revision-1 contract references are historical provenance; revision 2 governs this review.

**Reviewer STOPPED.** No writes, builds, tests, checker/compiler reruns, Cargo/Lake, scratch/cache/target/environment/worktree creation, descendants or persistent processes. No quarantined path was accessed or released.
