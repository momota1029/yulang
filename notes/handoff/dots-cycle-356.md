# Yulang cycle 356 — mixed compiler evidence and exact outputs

Started 2026-11-22T23:27:56.416Z UTC. Work on private `work/dots-main`; integration spec/owner order at `73d449534e5fdecca98140b4d6c1e4a72e77c38f` (`notes/plan/dots-standing-orders.md`, `notes/plan/dots-inbox.md`, I‑63; `spec/06-roles.md`, `spec/10-inference-core.md`). Prior C355 `08ff9c24ffbddfa8b52b4f43628644f53f68fa55`. No integration write.

## Result

型付き・通常の両方の子を同じコンパイラ出力順に照合し、実例の辞書 `92[93[95],94]` を検証した。通常の2枝の出力先は70と60。物理的な中心名10は共通だが、型付き読みと通常の読みは、それぞれ別の根拠から導いている。

- The current selected root at physical `[4]` emits the typed sibling at `[4,0]`, and then the ordinary sibling at `[4,1]`. The typed sibling actually emits the ordinary grandchild at `[4,0,0]`. The absolute compiler diagnostic paths and dictionary are derived from actual compiler rows and the ordered emitted requests. They are checked against the offered finite tree, not plugged in as a semantic equivalence.
- Typed authority and the ordinary payload are independently checked. Root release at the authored write ordinal 1 names center 10; the typed valuation separately verifies the nominal result `(tag=13, Box=0)` at the stored place/version. The ordinary payload read at center 10 has its own source rows 7 and 8 and a genuine union witness; in an inhabited ordinary model it denotes the tag‑7 payload. A literal clause, binder and actual demand path are checked; a numerical name match cannot authorize the ordinary read.
- The recursive supplied mixed wire is checked against the actual child list at each typed node. Ordinary subtrees use the independent C352/C337 scoped evidence checker and its model facts, not typed fallback. Whole-role filtering cannot hide any ordinary competing declaration at an authorized role: it leaves the role environment and current source state untouched and removes entire disjoint typed roles only. The ordinary-subtree closure check excludes typed reentry.
- The preorder emitted ledger reports authorship stamp/version when typed, original compiler argument, exact ordinal/target pairs, and full typed or ordinary write rows per visited node. At this fixture the root targets are 5,10,6; the typed child has no writes; the ordinary branches actually bind fixed targets 70 and 60 with emitted variant rows. Soundness validates their ordinary rows in the very same ordinary model plus a separately compatible typed valuation. For any admitted finite forest, the compiler's absolute diagnostic addresses are injective, so a single path cannot name two competing ledger entries, even across carrier boundaries; this makes no claim that different paths must use different physical names. False reports tested include wrong release/version, missing ordinary provenance, reordered children, rebased or truncated path, wrong clause, and wrong fixed target.

## New owner direction I-64 and limits

I‑63 **S1: one partially covered group** (actual compiled emissions, protected slot, finite recursive structural coverage, sourced authored reads and narrow supported nominal route; this does not cover arbitrary source/type/role combinations). **S2: one partially covered group** (scoped two-carrier forest soundness, compiler execution, same-model ordinary equations and exact output/dictionary receipts; cross-back from an ordinary subtree to a typed node and arbitrary within-role competition across modes still outside this checker). **C: one group deferred by I‑63**, not a proof of completeness or supported-language rejection; no raw certificate extraction, no old Local/C334 equivalence, no solver termination, no implementation-wide Lean or Rust claim. The finite checker's structural recursion concerns the supplied wire only and says nothing about solver termination.

今周の終盤に I-64 を確認した。次は旧 C334 への橋ではなく、宣言側を分散つきに一般化し、辞書の健全性を示し直す。この周の証明は新しい宣言側の共変の場合に接続する候補であり、接続そのものは未証明。

Final live reread found **I-64** at integration `6e2b1228b3daefe2bc1b6859fd92af9662a666d6` (inbox blob `710202fad8db50f70be6ab1b0f03f3909111a556`; standing orders and both reviewed spec files unchanged). No new Lean changes followed this reread. I-64 supersedes the earlier C356 follow-up; the next task is to generalize the declarative state/classification itself from primitive/invariant to a declaration-kind-and-variance table, re-prove its dictionary soundness, and then connect S2 to *that* classification. The earlier C356 checked artifacts are valid isolated inputs and prove none of the I-64 obligations. Do not bridge to old C334 Coverage. The [I-64 handoff](../design/dots-cycle-356-i64-declarative-variance.md) isolates the local proof cut, reusable independent variance rules and ordered induction.

## Verification

- Exact final science pin `00ba488a2137f30bc418c249eeaa893dca3d6d46`, verified after detached source-byte checkout. Warning-strict scoped Lean 4.35.0 checked 24 new source modules and 6 stand-alone audit files directly under `--trust=0`. 81 individually reported declarations (3 axiom-free) and 116579 transitive declarations; no axioms beyond propext, Classical.choice and Quot.sound.
- Combined scoped Lake succeeded (3938 dependency jobs); exact frozen-skip diff gate passed; old barrel byte prefix and precisely 24 additive same-change imports verified. No whole Lean/barrel or Rust claim.
- Original frozen objects match by metadata, with neither file materialized: `97dd1cfaded3e3abc3fd8caa98a64843d6f7a3d9`, `9fd6842bcc00c5bc5c00a196d9ccb328c6b0c94a`. Evidence commit `a13d5304387b5125dc539a17ed4ca66ef519bf20`; logs and exact source-blob manifest: [verification](../verification/cycle356/). Only successful scoped logs are counted; the final detached logs are the evidence for the exact tree.

Pre-handoff paths verified: 52; final handoff adds one report and updates the existing heartbeat.

Completion marked 2026-11-23T00:18:00.952Z at 50.08 minutes from recorded actual start, within this slot's absolute cutoff.
