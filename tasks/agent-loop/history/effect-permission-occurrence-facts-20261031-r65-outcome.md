# R65 outcome — occurrence-qualified effect facts

Sprint `EFFECT-PERMISSION-OCCURRENCE-FACTS/20261031-R65`, contract revision 1, SHA-256 `57f6f8f978aa86922e01998a7a29ead015cd2e67eb0939188982f9294d0bbf08`. Baseline branch `yulang3`, commit `a89bccbfb7b6123dff3522cc8cb000728f206fae`, verified at `origin/yulang3` on admission.

## Outcome

The fixed bounded research outcome is complete and independently reviewed. The Rust owner-local reader selects by `(HirOccurrenceId, slot)`, rejects ambiguity at that key, preserves every provenance occurrence, and validates the selected FactId and endpoints against the owner tables. The R64 iterator-collector and Term-vs-row-ordinal corrections were retained. This source contribution remains uncompiled and non-production.

The Lean module defines versioned occurrence-qualified Internal and R47 reader bundles. It proves same-key uniqueness/rejection, dangling and foreign-store rejection, foreign-key extension preservation, and successful reads for distinct source keys that share one FactId. It derives accepted slot-0 and slot-2 facts, retains the same raw permission entry/use/fact in Internal and root extraction, and preserves the existing collected Catch slot-51 reader. It leaves R55/R57 unchanged and does not claim equivalence to their original global-FactId readers.

No finite Lean witness is represented as a native runtime counterexample. Actual native multiplicity is unknown. Rust-to-Lean owner/pointer/index authenticity, source-to-Native correspondence, R62/R63 exact-bundle integration, outer successful Run, original A/B, full effect hygiene, whole-program soundness/effects/principality/termination, and production remain OPEN.

## Frozen artifacts and review

- `crates/yu-solver/src/candidate_receiver.rs`: final SHA-256 `a729f7ae68b421073b36e26d687ef7ef69e79f5d5674a7e1884b4058c37431e3`. R65 started at `ff03bb9cfa1222a61f7c9594f437049e470b7a2fb6d69af00ef74c8625b4a63e`; the reviewer authenticated that removing the R65 contribution reproduces this baseline. The final one-line lifetime repair was independently re-reviewed.
- `notes/theory/lean/YulangClosure/OccurrenceQualifiedFactReadersR65.lean`: `3253e00f9b523446363507ae39567bab0a4ca69a2fc84cc128f8952c43bb700b`.
- Rust handoff: `tasks/agent-loop/inbox/effect-permission-occurrence-facts-r65-rust.md`, `30e81d63e691ac81e684c71a7a04ed5b1967a562125d4e79190a216d0b9d3310`.
- Proof handoff: `tasks/agent-loop/inbox/effect-permission-occurrence-facts-r65-proof.md`, `c93b9e3a9978f6c4b5c802f5e94456b2c18328a8d58f4835bf60a7884ab0ce6e`.
- Review with re-review supplement: `tasks/agent-loop/inbox/effect-permission-occurrence-facts-r65-review.md`, `c8e78799c9910544f158de26a797fcb604ea35b64c14800bcd6945911c06c259`.

The first independent review found blocking R65-R1: the returned `occurrence` borrowed the independent lookup argument rather than the inventory row. Luna changed exactly that initializer to `occurrence: row.occurrence`. The same independent reviewer confirmed the one-line delta and PASSed the repair. No other major or minor finding was established in the fixed scope. Rust feature compilation remains unverified because R65 prohibited builds/tests.

## Lean evidence

Pinned Lean 4.35.0 `-j1 -M1024 --stdin`, final attempt 9, exit 0. Retained stdin SHA-256 `3584b948acd4549b3d4be5579b1ebd31bb20953c8ede77880462c3d23210c41f`; the independent reviewer authenticated the module body, 333 definition spans, 15 inherited/supplementary theorem spans, all 25 theorem types and transitive axiom reports against the retained input. Axioms are only `propext`, `Classical.choice`, and `Quot.sound`; only `foreign_key_extension_preserved` reports `Classical.choice`. Nine attempts used 69.654 checker seconds; final reported RSS 932,772 KiB. Failed attempts remain in the proof handoff. This is retained producer evidence reviewed independently, not a second kernel run or a default project build.

## Checks, resources, and Git

- `python3 tools/agent_sprint.py check`: PASS after state synchronization; static consistency only.
- `git diff --check` on the Rust source: PASS.
- No Rust build, test, Cargo, formatter or project check ran. No scratch, cache, target, worktree, environment or build directory was created.
- Requested envelope: Rust 1,000s; proof 2,600s; review 1,200s (240 intake/960 final); Luna 1,200s including 500 closeout; Astra 0. Effective worker telemetry and elapsed active budgets were unavailable and remain UNKNOWN.
- Git disposition is recorded in the R65 closeout state/progress record after the primary checkpoints the reviewed exact path set.

The result advances a source-qualified reader seam under unchanged semantics. It does not close the original effect-hygiene parent or authorize production.
