# Cycle240 — I45 後継と、新しい停止性反例

開始2026-11-17T12:32:58Z。研究上限13:17:58、最終上限13:27:58 UTC。
12:53:54に新境界そのものの反証を確認して対象研究を停止。その後は監査・記録・公開照合のみ。
短縮は成功扱いの早期終了ではなく、偽命題発見時の停止条件による。

## 入力・判断

239 completed/公開7816c2f0確認、作業競合なし。integration2a271030のstanding-orders/inboxを再読して取り込み。
I45は239反証を承認し、一点descriptorをReobserveで付け替えない選択肢2を採用した。
旧targetは停止のまま、新判断の後継だけを実装。版正準化案は採っていない。
注意: このintegrationの差分はinboxのみで、記述されたspec6.5更新はtreeに未反映。
明示inbox決定の範囲で進め、specは変更していない。

## 検証済み成果

64新モジュール、生成宣言を含む885定義の推移公理監査PASS。

1. PointRevision/Kernel/Boundary/SourceBoundary240: 旧234の版割当て・mixed cacheを保ち、
   Reobserveだけに既point descriptor完全保持条件を追加。
2. Erasure/Transport/Record/RecordSteps240: 新→旧stepの消去、旧Stable→新Stable、
   sourceとrowSourceを含む既point記録の全actual path不変性。逆向きStable含意は使わない。
3. 旧239の任意nの付け替えrevisionが新guardを満たさないことを証明。
4. 230/Optional・206・218の実新source経路、Stable・選択・中身のあるEvidenceAtを保持。
   Compoundの実到達性、モデル非空とno_common障害も保持。
5. 別の5slot sourceでは、根のintervalを `(lower_n,4)` として非pointのまま残せる。
   原初期境界の形成/GroundRoots/モデル、全nのFresh・SafeKnown・Installable・mixed cache・
   raw-back・未commitを閉じ、actual Install→Refresh→Reobserve の全n反復を構成。
6. `GeneralDictionaryLooseIterationNontermination240.initial_no_acc`、
   `no_saturation`、`no_statement` により、新PointSourceBoundary240の全域停止性目標を反証。
   最終6宣言は独立に再監査し、旧kernel混入・循環・結論の仮定化がないことを確認。

既pointの記録不変性は正しい。しかし、非pointの根が新しい同値sourceを参照し続け、
毎回別のloose Fooをpoint化できるため、有限個の版しか出ないとはいえない。
この結果は「全実行の発散」や「Stable終点不存在」の主張ではない。

## 検証範囲とログ

- 64追加ファイルを依存順に個別 `lake env lean --trust=0 -DwarningAsError=true`:
  `notes/verification/cycle240/direct-build.txt`（全文、最終exit=0）。
- `Audit/Cycle240First.lean`: 147 constants /16 modules、exit0。
- `Audit/Cycle240All.lean`: 885 constants /64 modules、exit0。
- `Audit/Cycle240Independent.lean`: 最終6 declarations、exit0。
- 許可公理は propext / Classical.choice / Quot.sound のみ。
  sorry・追加axiom・native_decide・implemented_byは追加ソースにない。
- source-manifest.json に64ファイルのSHA256。
- 全体lake build / verify-lean.shは監督側専有の凍結指示に従い未実施。
  凍結 `lean/Audit.lean`, `lean/README.md` と既存proofは変更なし。
  この個別監査を全体CI成功とは扱わない。

## 公開と次回

中間公開6003eee05で16モジュールと第一監査を保存。最終公開は全追加ファイル・
質問・監査ログと最新integrationのinboxを含む。公開後treeを取得しローカルと比較する。
公開SHAと比較結果は末尾のpublication記録参照。

[質問ノート](../questions/2026-11-17-cycle240-point-preserving-nontermination.md)
に監督判断が必要な意味条件を記録した。次の明示判断なしに偽の停止性目標や
修正案を再開しない。版正準化を勝手に採らない。

## Publication verification

全成果公開 `0fa032527f4f1822230adf325c78047925732d7b`。
公開tree `35c93bc6acb4a4b69cedca7e3c674afcdaeb5790` をGitHubから取得し、
ローカル `abe654978f6ac70211bdbd1312a09501b75a2688` と `git diff --exit-code` で全tree一致（exit0）。
64ソース・監査ログ・I45 inboxを含む。GitHub statusは空配列であり、CI成功とは主張しない。
最終記録時刻12:57:53 UTC、経過24.9分。研究停止後の公開と検証まで完了。
