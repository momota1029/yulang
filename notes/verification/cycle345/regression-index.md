# C345 checked regression index

The new operations are proof-only observers. They do not add acceptance checks or replace the actual mixed solver transition.

- **C311 peer, not a local/birth request**: `CurrentPeer345.before_no_row` and `after_row` compare the actual pre/post-merge trace snapshots, and `CurrentUnstored345.actual` couples the peer receipt with the actual current-model equation even though the current effect is missing from the journal. Peer target `z` remains the direct sibling's original name.
- **C310 duplicate, not a set**: `CurrentDuplicate345.exact_before`, `exact_after`, and `no_dedup` exhibit the actual two distinct site/ordinal tuples with one identical output descriptor after merging. Any deduplicating scan would violate exactness.
- **C238 nonpoint, not a whole-state success**: `NonPointBodies345.actual` proves the existing point-only whole-state projection returns `none` in this actual installation, while its physical site 0 / ordinal 0 associated output equation still holds in every valid post-model. This is a real reachable prefix, not proof that the whole solver has halted.
- **C316 actual old-kernel stop and missing raw producer**: `CurrentBarrier345.held_outputs_without_packet` checks the fixed recorded target 4, while `CurrentCandidate345.actual_cut` has a real current frame, unique candidate, ready output body and earlier-choice compatibility but no Installable package. No claim that this is a selected witness of the latest declarative judgement.
- **C319 isolated repair as a control**: `HybridPhysical345.both_ready` and `replay_one_model` witness both actual isolated commits separated by native nominal reobservation with current requested names and one final assignment. This does not prove that the original raw scheduler uses these isolated commits.

The five standalone Lean source audits have the same `Cycle345*.lean` names under `lean/Audit` and import no other audit module.
