# Cycle139: I-25 初期状態・到達可能性の V5 接続

開始 2026-11-12T10:27:19Z。ユーザーの55分上限: 11:22:19Z。
fresh integration `3e2be99336e14b61006ca38cde256c6eac1cb330`、standing orders/inbox を再読し I-25 を実行。
最終公開前にも同じ integration head を確認。前138はcompleted・報告あり、前writerなし。
本サイクルは最新の55分「以内」を優先し、文書の長時間実行要求のためだけの待機はしない。

## 今回の成果

1. `B4TargetV5` は Initial を足し、公開5項の入力だけを初期状態へ制限。
   その他の量化子、診断tree、Evidence、order同値は V3 のまま。
   とくに OrderIndependent に二つ目の Initial 前提を追加していない。
   `B4TargetV5Compatibility` は V3⇒V5 と、Initialが全域の場合の V5⇔V3 を形式的に検査。
   全域Initialは具体的境界へ与えた仮定ではない。
2. `B4SkeletonV5` の状態橋を Reachable に限定し `b4_of_bridges` を証明。
   EvidenceNode は root または実Generated子だけ、whereAccessible は rootだけで足りることを
   相互再帰の辞書健全性証明で確認。公開 Statement はこの骨格整理で変更していない。
   順序独立の単一Initial前提を守るため `initialReorders` を14番目の局所義務とし、具体的に証明。
3. 具体的 Initial は実 InitialSource と空journal。実feedback全更新による Reachable と
   SourceFormed の同値を証明。初期化・再順序化を示し、Astraの既存5 lawsを無変更で移植。
   `Remaining` は正確に残8フィールドを持ち、6証明済みフィールドと型検査済みで合成する。
   **条件付き b4_of_remaining は一般executorやB4の完成ではない。**
4. 任意registry/contextの初期空journalでは、実SurvivorからJointを構成。
   実Stable・selectedなら全modelの現在Instance/Evidenceを導く。初期に安定selectedなら子列は空。
   非terminal選択は初期安定ではない。これはzero-step部分だけの証明。
5. 任意registry・非初期journalでも、restricted FinishedTrace、記録済みfocus、同じoccurrenceからなる
   alias class、実model、実selectedから Joint を導出。Jointを前提にしていない。
   同じ一つのmodelで各alias BranchAtを満たす。任意view/carrier変更refreshや別occurrenceへの
   alias transport、Stableからの記録網羅性はこの結果に含めない。
6. **記録網羅性への一般還元は偽。** 正当なInitialSourceからの実Reachable・Stable・selected30[]・
   model存在にもかかわらず、packets=[]の例を構成。既存 JournalTree.Covered は偽で、
   Stable/SourceFormed/selected/inhabitedからの全域Coverage橋を形式的に否定した。
   Committed は意味的成立であり、記録がなくてもinstallationが不要になる。
   この例では全journal modelでterminal Evidenceが正しい。**V5 EvidenceNodeの反例ではない。**
7. 実Reachable+model存在でも ContextComplete が偽になる既存実installation例を接続。
   これはStableではなく、やはりV5反例ではない。rawモデルを無条件にjournalモデルへ昇格できない。
8. 実feedback traceがmodel存在を失うなら、最初の喪失は全旧modelを排除する出力等式を持つmerge
   に限ると証明。enqueue/refresh/equate/実enabled installは喪失させない。
   merge証明書は実SameInputs・noveltyも保持するが、破壊的mergeの到達可能な実例は作っていない。
   InitialSource自体にmodel存在は含まれない。一般model存在保存は主張しない。
9. 前138のraw stale journalはV5 Reachableでないと確認。一方、実installation+view-changing refreshの
   2段階正例を V5 Reachable・実Stable・selected・Classifyへ接続した。任意refreshの一般定理ではない。

分類: proof-interfaceの忠実な修復、条件付き合成、局所健全性、具体的正例、補助還元の反例。
一般完全性・原理性・全言語決定可能性・source parser adequacy・一般停止性は未証明。

## I-25 の受け入れ条件

- (1) V5公開target、(2) reachable骨格と合成、(3) Initial/SourceFormed・既存5 laws移植は完了。
- (3) 一般evidenceNode閉鎖は未達。実際の初期・正例・限定記録クラスまで。
- Arbitrary refresh後のhistorical-to-current applicability、別occurrenceのalias同時モデルが残る。
- 記録必須の方針だけではzero-step semantic completionを落とすため、次は意味的Committedの場合を併合する。
- I-24遵守: 巨大Audit/README凍結、新しい小監査2ファイルとmodule guide。Astraの定義、specは無変更。

## SourceBoundary 13項目

一般の定義ありは全言語網羅性や主定理の証明済みを意味しない。

| 項目 | 状態・制限 |
|---|---|
| Checked | 一般の定義あり、既存checked registry |
| Models | 一般の定義あり、実journal/source models |
| RootPending | 一般の定義あり、保守的source観察 |
| RootK2 | 一般の定義あり、実feedback/cycle |
| CandidateK2 | 一般の定義あり、実feedback/cycle |
| InspectionPending | 一般の定義あり、未対応inspectionはpending |
| Survivor | 一般の定義あり、source compilation完全性は未証明 |
| Reorders | 一般の定義あり、既存visible/where関係 |
| DictionaryEquivalent | 一般の定義あり、payload同値 |
| Step | 一般の定義あり、実feedback更新無変更 |
| Stable | 一般の定義あり、実no-step安定性 |
| Generated | 一般の定義あり、実生成closure |
| Evidence | 一般の独立定義あり。V5一般node橋はOPEN |

追加 Initial は実InitialSourceと空journal、Reachableは実Stepsで定義済み。

## V5 未証明8/14

| フィールド | 状態 |
|---|---|
| progress | OPEN、一般descent未証明 |
| execution | OPEN、一般executorなし |
| halted | OPEN |
| closure | 具体feedback boundaryで証明済み |
| stepModels | 同boundaryで証明済み |
| frontierLocal | 実非計算的frontierで証明済み |
| localIdentity | 同frontierで証明済み |
| whereAccessible | OPEN、rootの実child Accが必要 |
| treeExecution | OPEN |
| canonicalLocalOrder | OPEN |
| dictionaryRefl | payload同値で証明済み |
| evidenceNode | OPEN、raw V4の反証をV5へ転用しない |
| generatedChildren | OPEN、model不存在も含む一般版 |
| initialReorders | 今回実InitialSourceで証明済み |

## 検証と限界

- focused build: exit0、678 jobs。対象は今回の8入口と依存closure、全repository buildではない。
- `lake env lean --trust=0 Audit/Cycle139.lean`: exit0、30宣言。
- `lake env lean --trust=0 Audit/Cycle139Followup.lean`: exit0、31宣言。
- 61監査宣言は標準propext/Classical.choice/Quot.soundのみ（依存不要の定理は空）。sorry/new axiom/native_decideなし。
- `tools/verify-lean.sh . origin/integration/m1-final --no-build`: exit0、差分ゲートPASS。
  全build・全巨大Auditは未実行。現在の短時間運用に従い、既存全ライブラリの再監査と混同しない。
- 独立read-only review: V5量化子、root/generated narrowing、記録Joint、unrecorded例、model-loss切分けPASS。
- x-oracleは公開済み報告を読んだのみ。新規Yulang2実行・全適合試験は今回していない。
- 初回に未完成buildより先の監査でolean不足、dirty時の差分ゲート拒否があった。
  build完了・commit後の上記再実行は全て成功。

### 最終差分ゲート出力全文

```text
verify-lean: . @ 5f7b44d15 (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: lean/Audit.lean only appended (plus top import lines)
ok: lean/Audit/Cycle136.lean only appended (plus top import lines)
ok: lean/Audit/Cycle137.lean only appended (plus top import lines)
ok: lean/Audit/Cycle137Finished.lean only appended (plus top import lines)
ok: lean/Audit/Cycle137Followup.lean only appended (plus top import lines)
ok: lean/Audit/Cycle138.lean only appended (plus top import lines)
ok: lean/Audit/Cycle138Formation.lean only appended (plus top import lines)
ok: lean/Audit/Cycle138Joint.lean only appended (plus top import lines)
ok: lean/Audit/Cycle138Refresh.lean only appended (plus top import lines)
ok: lean/Audit/Cycle138Terminal.lean only appended (plus top import lines)
ok: lean/Audit/Cycle138Tree.lean only appended (plus top import lines)
ok: lean/Audit/Recovery131135.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
exit_code: 0
```

## 公開

work/dots-mainのみ。中間checkpoint 7ec4f0c4 → 1f44b06e → 0d69cfa0。
最終source `814a1c018598b61919c7e8173f9ba9b5eeae870e`、tree `817e2e53e1aca60f39cc58622c7f3f08e784cc50`。
integrationとの差分全20ファイルをこのcommitから再取得し内容一致。
凍結Audit SHA `1cd235e664d51efda50bd37f6751854aea94b10f`、
README SHA `0b255a4d97ae144984a60e1e7de03c9389b104e8` は上流と一致。
GitHub appのtree/commit/refを使い、refはexpected_sha一致のfast-forwardのみ。
本サイクルでblob承認依頼は発生していない。

## 次

1. fresh integration/inboxを読み、I-25の続きか最新指示に従う。
2. 一般EvidenceNodeでは実Current Instanceのsemantic completionと記録caseを分ける。
   Stable⇒Coveredは反証済みなので同じ還元を再試行しない。
3. 任意refreshとalias同時BranchAtが本当の残件。ModelLossはmergeの保全義務を特定するが
   存在しない一般保存定理で穴埋めしない。Conditional Remainingを完成と報告しない。
