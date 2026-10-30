# R36 stage ledger — source-owned callback use

Sprint: `EFFECT-PERMISSION-SOURCE-USE/20261031-R36`
Contract SHA-256: `c471c7dd5d8ef2515022f4665f1ef2151577141a3f0942ea107489ecd86c5ac0`
Input manifest SHA-256: `cf03b01ba1cb057972303540dd7deb881e0cfff2f8dbafd93e4912035bee37e4`
Admission SHA-256: `c28d9b493d7a6e00bfd9d4f99ac46990e1bf246a70bd3ace9225021afa36e92d`.

| Stage | State | Evidence / boundary |
| --- | --- | --- |
| Contract and dependencies | ADMITTED; committed and pushed | Commit `177960fc8` (`docs: admit R36 callback source-use sprint`), parent `1388bdc476e5dc0c0bb96532715c7280aa95b10e`, pushed to `origin/yulang3`. R36 contract and 15-file manifest pinned at baseline. |
| Rust construction | FROZEN; repaired and delta-reviewed | `program.rs` SHA-256 `b3fc1daacdba9fa9618b9b741e4f85d8e9ea0dcd5e859540204d09200d23a65d`; Rust handoff r2 SHA-256 `df72f3c643b1267f4d9ff40e737890d45fe4059f4c9e5b75a7c246bb5d480ec5`. Static field-path blocker repaired by Luna; independent reviewer verified exact one-field delta. No build/tests. |
| Lean construction and audit | FROZEN; independently audited | `SourceCallbackUseR36.lean` SHA-256 `9e15cb4982248cf90d7a11ef0c66ee7ee95ec0abe99c217d8187c31c488731de`; proof handoff r1 SHA-256 `0d1a5d7e4c31ff6722269c6d894f301950c87b34c641b395e11c8360aebd8558`. Lean 4.35.0 stdin audit exit 0; all 13 theorem types and full axiom sets recorded (7 `propext`; 6 `propext, Quot.sound`); no holes/project axioms. |
| Independent review | STOPPED; final bounded technical PASS | Review handoff SHA-256 `2b2f8bb23727c82fc572046e36d2aba64b63ac2020cbb491151b871ee3779afe`. B1 closed by delta review. The unauthorized broad-`rg` quarantined-read incident is separately adjudicated and remains recorded; no quarantine/path lease released. |
| Luna integration and Git | SOURCE CHECKPOINT COMMITTED; receipt update and outbound-range push | Commit `38abc73b9` contains only the five reviewed source/proof/handoff paths. This ledger/current/outcome update is the next exact-path receipt commit; inspect the whole outbound range before push. |

No builds/tests or new environments were used. Preserve symbolic rows, annotation polarity, all pending questions, unknown workers and quarantined paths. Runtime execution, Grant/Catch, Rust-Lean simulation, original A/B and whole-language claims remain OPEN.
