# Cycle 275: 実230の mixed 終端、全継続の停止と辞書

- 開始: 2026-11-19 14:30:10 UTC（14:30 定時枠）。報告作成: 2026-11-19T15:20:15Z（50.08 分）。使用量枠: 不明。
- 開始時と公開前に integration/m1-final の immutable 版 3382f7eaab33017d4697fcbe082acc070bd1ae1b を確認。standing orders / inbox の blob は 7ae4d68d2ac7df80d1eadbd061dadd2296faf4c4 / 2f6b72446884d0e340537ac4b9aea1bb6c0e047d。最新 I-52・I-53、I-51、凍結を遵守。全作業 STOP なし。開始時 work/dots-main は正常完了 9841c3ca1d726309bec7cfed4d3c2866a068602f、ローカル tree 一致。同 repo の他 writer は見当たらなかった。
- 書き込み先は work/dots-main のみ、expected-head の non-force 更新。途中公開: 0cb64d39、8e085e0a、546683d9、5d8d8de2、683368ad、aa87f2f7、13595b51、a5f75d3f、9e33c896、a1ccc517、c00087a0、f4c8e9e0、6da433ca、45389077、c7cfd074、d67f0b99、cdd10d52（ほか独立した心拍）。

## 検証済みの成果

1. **前周で未確定だった3名は、どれも実際に登録できる。**
   GeneralRebaseWidthRefinement275 / GeneralRebaseWidthCertificate275 / GeneralRebaseWidthRealized275.realized は、任意の候補 ID ∈ [旧 upper, 新 lower, 新 upper] に対し、既存の生 source 5枠、row、nominal、普通式、鍵、seed を保つ6枠の snapshot と、全 recorded head をカバーする mixed trusted 節を構成し、実際の mixed 234 Step を与える。同じ full assignment に対する Models は双方向で等しい。従って旧232で stable だった据え付け済み実230は mixed234 では stable でない。以前の stable 判定をそのまま流用していない。
2. **三つの同時登録には8型枠が必要かつ十分。**
   GeneralRebaseAllWidthRealized275 は本物の mixed 1 Step で3幅名を登録し、同じ full models を保つ。元の5型IDを維持し3幅IDを明示化する任意の refresh 列は少なくとも8型枠が必要（GeneralRebaseWidthMinimum275.at_least_eight）。この構成で8枠ちょうどで、増えた型枠は既存 row 2 を再利用。GeneralRebaseAllWidthStable275.halted はその具体的到達先から実 kernel のどの Step も出ないことを証明し、GeneralRebaseAllWidthSelected275.regression は source 到達、実モデル、Stable、V8 selected、EvidenceAt を全て与える。GeneralRebaseMixedReplay275 は source から install・Reobserve・install・一括 refresh の4辺を実行可能な有限表にし、任意の受理辺・受理列の実 Step 対応、全位相の公開射影、rank 4→0、終端の実停止を証明。
3. **据え付け後に限れば、制御表ではなく実 mixed kernel 全体の Acc を証明。**
   GeneralRebaseRefreshClosure275.step_partition は任意の refresh 到達先で enqueue / equate / Reobserve / merge を除く。GeneralRebaseRetarget275 は任意の source/row ID 保存埋め込みで、同解釈・確認済み nominal report・葉 packet の条件の下、report、bindings、自己検査、投影、binder、入力と出力を運ぶ。GeneralRebaseRetargetEffects275 は明示/既定 body と class effect を運ぶ。GeneralRebaseRefreshFrame275 の単一枠性と GeneralRebaseRefreshAcc275.exact_hop により、新たな据え付け候補も既に committed な同一計画となり、実後続辺は refresh と必要十分。GeneralRebaseRefreshRank275.rank_drop / GeneralRebaseRefreshAcc275.actual_230_acc, actual_bound は、未登録の幅名の個数が毎辺減るので、**据え付け済み実230からの任意の実混合継続は最大3 Step** と証明。3辺を達成するとは主張しない。一括1辺は実証済み。GeneralRebaseRefreshSaturation275.remaining_budget は任意の有限 prefix を全体3辺以下の安定な正の V8 終端へ延長できる（存在証明であり任意 snapshot の実行器ではない）。
4. **どの据付後履歴でも、公開モデルと実辞書が同じ。**
   GeneralRebaseRefreshPrepared275 で現在の Prepared を再構築。GeneralRebaseRefreshEvidence275.all_actual_leaves は任意の実 post-install 到達先と任意の full assignment に対し、Models が元と同値で、同じ葉辞書が現 snapshot で立つことを示す。GeneralRebaseRefreshSafety275 は同じ具体的モデルに対する semantic edge と raw structure/nominal edge の strict rank で K2 を除き、GeneralRebaseRefreshSelected275.all_post_install は全実履歴の V8 Local=.selected と EvidenceAt を与える。GeneralRebaseRefreshPublic275.decode_exact は型0〜4と全 row から決定的に読み戻す274の decoder をそのまま使い、両方向の公開条件、実モデル、検査済みの ID と空子の payload、および固定 owner store を同一 assignment で照合する。GeneralRebaseRefreshLedger275.all_retained は source ID の集合が両方向に一致し、元の型・row枠ごとの ID が残り、保存済み plans/effects と元 source、seed、構成子、解釈が変わらないことを示す。生 snapshot 自体が一意、または可換な書き換えで同一になるとは主張しない。

## 検証・残り

- 29 新規 Lean モジュール、294 名前付き宣言、26 単独監査。全追加ファイルを Lean 4.35.0 の focused trust=0 / warningsAsError で確認。全単独監査を再実行、許容公理 propext / Classical.choice / Quot.sound のみ。重要 19 モジュールも focused 再実行。共有環境への負荷を避け別キャッシュ総再構築、lake 全体ビルド、CI、Yulang 実機は未実施。別に Lean eval で実行表の rank 4→3→2→1→0、早すぎる・二重の refresh 拒否を確認。
- git diff --check、tools/verify-lean.sh . a1cc0b224 --no-build、tools/verify-lean.sh . 6d6475be0 --no-build は exit 0。出力全文、全宣言名と個別ビルドは [verification](../verification/cycle275/)。凍結ファイル byte-for-byte、barrel 末尾 import 1回ずつ、Audit 同士の import 無し。前周から 170 ファイル（報告・完成心拍を含む）。
- 範囲外: 元 source から二度目の据え付けまでの全分岐の停止、任意 source/owner の Acc、生成子つき EvidenceNode の一般化。238に旧生 Evidence があるとも主張しない。設計の問いが必要な言語変更はなかった。
- 次候補: (1) 273/274/275とは別の実正例 GeneralNominalMixedNonleaf198 / GeneralNominalNonleafCurrent195（一子あり）を versioned/mixed に移す。子の ID・順序・出力・公開境界を先に照合。 (2) 230を続ける場合は第二据付より前の全実分岐、または一般の finite owner/basis 不変条件に進む。この post-install 問題を繰り返さない。詳細は [設計](../design/2026-11-19-cycle275-terminal-mixed-registration.md)。
