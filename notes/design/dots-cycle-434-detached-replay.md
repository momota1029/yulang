# C434: detached replay manifest for the literal R pending rule

Pinned technical lookup: `5d58ae2e16fc3b5a462d2376e40d8f382e84ade6`; Lean tree `6b1fa7520125ad7a50797c9d0cf4c6083a3f66a6`.
Production dependency base: exact C433 Lean tree `7592bf70541dbaa56052b85c02938184e9192a82`. Compiler: Lean 4.35.0 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` (Release).

Start from a separately verified build of that base production dependency closure. Read all these files from the pinned technical commit, use `git hash-object` to verify each byte-for-byte, and use a fresh production-only `LEAN_PATH`. Do not put any Audit olean or Audit source in the import path. Compile the eight listed C434 production modules in the listed dependency order with `lean --trust=0 -DwarningAsError=true -o …`. Run each Audit by itself with `lean --trust=0 -DwarningAsError=true input.lean`, with a distinct empty working directory containing only that input. The barrel is verified as the exact earlier barrel plus eight appended import lines, not a whole-repo build.

| Path | Git blob |
|---|---|
| `lean/Yulang/GeneralDeclarativeI65I74PendingAssociatedSource434.lean` | `5cb47c895106cdd316b035e53d26877b354e2527` |
| `lean/Yulang/GeneralDeclarativeI65I74PendingAssociatedRead434.lean` | `d0676bc1eb8fb9fd91f174469fd7b2d74b6b9595` |
| `lean/Yulang/GeneralDeclarativeI65I74PendingAssociatedEntry434.lean` | `56c210d9f4fc7afe8400764aacaa1b58ea79d800` |
| `lean/Yulang/GeneralDeclarativeI65I74PendingAssociatedNoCompletion434.lean` | `5eb4a5420b7009e92551026402c75324acf51a24` |
| `lean/Yulang/GeneralDeclarativeI65I74PendingAssociatedSeparation434.lean` | `a87ce5ea83abb0fc071ff3881e26aa1f3b9c85b6` |
| `lean/Yulang/GeneralDeclarativeI65I74PendingAssociatedParentEquality434.lean` | `f401ec6010ca3df44979fe8656bc7676b5901c88` |
| `lean/Yulang/GeneralDeclarativeI65I74PendingAssociatedRawGraph434.lean` | `1ea7299ea6797be3711443f84e4179569bb70079` |
| `lean/Yulang/GeneralDeclarativeI65I74PendingAssociatedAuthoredReopen434.lean` | `d66b2174e27cf6b0e663d646025ee63ae53b9330` |
| `lean/Audit/Cycle434I74PendingAssociatedSpec.lean` | `dbe2893676452b1410fd009f31a33dd7011d9aca` |
| `lean/Audit/Cycle434I74PendingAssociatedLegacy.lean` | `8152a052420fd7dc12c6a050a0ae919afd42caec` |
| `lean/Audit/Cycle434I74PendingAssociatedParentEquality.lean` | `dbee357b4359706cd206d4fc76d5dc16e9165469` |
| `lean/Audit/Cycle434I74PendingAssociatedRawGraph.lean` | `89cf178da495d4f04f6ae9b9b1fb5bcc6efbc00f` |
| `lean/Audit/Cycle434I74PendingAssociatedAuthoredReopen.lean` | `08ba7a8f0dabbef700a8494d16e434bfa335e703` |
| `lean/Yulang.lean` | `688130fd82771bcf618306ea89d486e33866811d` |

Result: 8/8 production, 5/5 standalone Audit, 34 reports with only `propext`, `Classical.choice`, `Quot.sound` or none. Audit import prefixes outside `Yulang.*`: 0. Freeze verified by blob identifier only. No whole repository/Rust or solver run.

Supplemental local checks on those same compiled bytes: (1) relocating the parent to `[92,3]`, the child to `[92,3,0]`, and its raw path to slots `15→3→12` still accepts exactly the original pending request and rejects the stale occurrence, missing source atlas case, and authored-head control; (2) the corresponding state with actual independent authored A has a fitting interpretation, `Ready`, and no old pending witness; (3) changing the child output address or claiming a reported write for the retained ordinary equality is refused. These extra probes are not separate public Lean modules and do not add new accepted paths.

Scope: the requested literal §6.3 R case. The absence of a full C17 implementation for distinct downstream W or Container/Wrap/P scenarios is not an additional rejection rule, and no candidate or execution-order semantics were added outside this literal scope.
