# R30 intake incident and exact-input recovery — revision 1

Recorded: 2026-10-30 00:41:23 UTC. Sprint: `EFFECT-PERMISSION-NATIVE-CALLBACK-GRANT/20261030-R30`. This receipt records missing local artifacts and their exact-byte recovery. It does not release any historical lease, establish that an unknown writer stopped, or attribute the disappearance to a process or person.

## Observed workspace state

After R30 admission commit `c6358458b646ebf5472988a106f488c72dd9178d` had been pushed, the primary's first Gate 0 check found the entire local `isolated/` directory absent. The exact R29 and R27 overlay source paths listed in the R30 manifest were absent, and the new R30 destination had not yet been created. Git reported 2,894 deleted tracked paths below `isolated/call-effect-owner-realization-r19`; many other root changes were already present. The coordinator did not restore, clean, reset, stash, stage, or commit those unrelated paths.

The live collaboration roster showed `/root` as the only running coordinator. No R30 worker was launched; the three R30 assignments remained `WAITING`. A process check found no Cargo, rustc, Lean, or Lake process. Unknown/quarantined workers and leases, the historical R29/R27 leases, pending items, and unrelated dirty files were left unchanged.

## Pinned input recovery

All four R30 overlay hashes were recovered exactly without writing to any historical source path:

| R30 overlay | Recovered bytes | SHA-256 |
| --- | --- | --- |
| `tools/inference-playground/src/runtime/machine.rs` | Reachable Git commit `a1d53b374fbbbc8ce376bb2bf3116c35fa22d4e0`, path `isolated/ep-native-callback-grant-r29/project/tools/inference-playground/src/runtime/machine.rs` | `b74c8345e6e07155f482440bb9299b5fc12763accb666ca8f543156dd4a87425` |
| `tools/inference-playground/src/runtime/receiving.rs` | Same commit, corresponding R29 path | `55b468cda3c3cf8180647a6429da28fc70badf7a371bf1b327539c8556b9b0f2` |
| `notes/theory/lean/YulangClosure/CallbackHygieneCorrespondence.lean` | R28 R2 rejected archive member `R2/context/notes/theory/lean/YulangClosure/CallbackHygieneCorrespondence.lean` | `0621f43739c12ce1e7919a50de129414a4748d8359bf46740babd69f4854011e` |
| `notes/theory/lean/YulangClosure/NativeCallbackGrantBridge.lean` | R28 R2 rejected archive member `R2/context/notes/theory/lean/YulangClosure/NativeCallbackGrantBridge.lean` plus the four preserved string-only edits from the completed R29 proof-author session record | `e49a320fbb148712b59e27a57cde57072e2192cdcdd84c936b10175f3a6ce6e0` |

The bridge recovery was evaluated in memory from the archived R28 seed (10,832 bytes, SHA-256 `7089b047821ed82e715b4230c47e36f5fec231bf431ec6d26501137f8a358c18`). The four original completed command records are in local session record `rollout-2026-10-30T08-19-25-01a189f6-0ac9-7f12-b8ac-458b6a33436d.jsonl`, entries 103, 128, 138, and 155; each records exit code 0. The primary parsed and replayed only their string replacement/index/slice assignments using a restricted in-memory AST evaluator; the shell/Python commands were not re-executed. The resulting 28,490 bytes matched the pinned R29 bridge SHA exactly. The R29 proof handoff alone did not contain the full source.

Because the recovered bytes match the pinned hashes, the R29 R3 Rust source review and prior compile inputs retain applicability to those unchanged R29 bytes. They do not review or compile R30's future edits. The recovered R29 Lean bridge remains an unchecked candidate; exact-byte recovery adds no proof or audit result.

## Gate 0 result

The primary created only the newly leased destination `isolated/ep-native-callback-grant-r30/project` from baseline commit `dd3d5ee22b8622f22e8db87382edaec0a466e7fd`. Its Git tree is `554c82b13d9186e197a460128330c4bb0dcd53ab`. A streaming comparison against `git archive` verified all 10,411 baseline entries with zero mismatches. The baseline verification digest matched the manifest value `1aa7ba512c55fd91d10eec15036f7b4b1d73110e2c8d9a5492165f0163a61ef0`; the four overlays were then written only under the new R30 destination and re-hashed against all four manifest pins.

Copy receipt: `isolated/ep-native-callback-grant-r30/project-copy-r1.json`. Gate 0 is verified, with no worker execution claimed. No compiler, runtime test, Lean, or Lake command ran. The R30 contract, source scope, original resources, and production authority were not changed; no budget or lease was transferred from R29.
