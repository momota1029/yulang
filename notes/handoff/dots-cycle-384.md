# Yulang cycle 384 — I-67: 出力の参照先を有限証明の添字にする

前周 `5569cbb378c75f1675bf1a0d1437bb0a4fee45da` の完了を確認して開始。取り込まれた C383 を含む `integration/m1-final` `e30ada6e616a87e15daabf1dbee3461a378eb323` の常設指示・inbox・roles/inference を再読した。I-67 は同じ inbox blob `a87744968aacd0c51cf7f82e263009a914ed48c6`。固定 `dictionary_sound` / `check_sound`、既存の受理範囲、I-59 根 K2 優先は変更していない。

## 今回通した範囲

1. **有限 producer の一致。** `ExactDependencies384` の `ExactSupportForest384` は各参照を `(Request, Dictionary, 元の出力 ordinal, row)` で固定し、同じ状態・同じ辞書の選択 subproof とその位置の独立な論理出力証拠を一緒に保持する。`ExactSupportReads384` の正確な添字読取りは、同じ要求の別辞書や同じ target の別出力を代用しない。`ExactSourceEmission384` は既存の ordinary 関連等式、および明示 unary covariant tagged body について、別途得られた実宣言・捕捉・有限 producer と保持行からそのセルを作り、元の requested target を返す。`authoredValues` と native 端点は同一視しない。
2. **正の分類投影と循環。** `ExactPositiveProjection384` は、上の exact 支持ベクタを保持する正の局所規則インターフェース上で、有限証明と `Resolves/Summarizes` の選択投影を同じ辞書のまま両方向に示した。一般の `Classifies` はまだ供給していない。`KeyedCircularSupport384` は、全候補の必要な producer または literal where 子が同じ `(Request, Dictionary)` 閉族を必ず再訪するなら、族のどれにも有限証明がないと示す。別の辞書／規則に外からの根拠があればこの仮定は成立しない。停止性・実行順は扱わない。
3. **普通の観測経路。** `OpenOrdinaryRead384` は直接の source 行か元 ordinal を保持する出力参照を受け、有限セルの証拠で閉じる。名寄せ式の各辺だけでなく、`interval` / `tyLe` で進む辺にも、normal にあるという事実とは別の論理的根拠を求めた。与えられた根拠から同じ状態の実 ordinary 行と supported view へ射影できる。実 source normalizer が任意の形でその根拠を供給する定理は別。
4. **実位置の K2 と不一致の証拠。** `VisitedUnaryOrdinary384` / `RigidAtVisit384` / `SupportedVisitProjection384` は、単一引数の実可視候補・元 head の正規化・実下端から始め、同じタグで一つだけの child があり、親に K2 がない ordinary primitive/nominal/variant の枝で、bare capture ではない実位置までの検査を示す。各下降に支持付きの形を要求するが、根・途上・到達点 K2 は未完了出力を除かない元グラフで確認する。到達点で literal nominal 名／arity が実際に異なる場合の正の衝突を得る。読めなかっただけでは衝突にせず、K2 があればそちらが先。この証明は構文上の一つの観測についてで、完全な rival 判定・混合 native 訪問・観測の一意性ではない。
5. **参照リストは検査から得る。** `CollectExactReads384` / `CollectAliasNeeds384` / `CollectUnaryVisits384` は、独立に成立する正の普通観測・実 unary 訪問から、根→経路→その位置で必要になった観測の順で exact セルを集める。ローカルの配列位置を再番号付けしても各セル内部の元 ordinal と辞書は変えない。普通観測では、得たセルと開いた読取りから元の独立な読取りへも戻せる。この局所ベクタで全候補の観測を切り落として「残りは保留でない／一意」とは判定しない。
6. **辞書・where 本文の合成。** `ExactWhereLowering384` は、実局所規則から同じ exact 支持を使って `SourceNode` を返す橋があれば、証拠を落とさず既存 C365 の literal where forest へ下ろせると示す。支持のために読んだ producer を辞書の子や固定出力リストへ混ぜない。得られる固定行は同じ一組で、任意の同じ状態の適合モデルで意味を持つ。全形の局所橋と一般 typed receipt は未証明。

## 残り

- S01 未証明: 全可視候補の独立した正負診断を含む実 `Classifies`。
- S02 一部: 実上流の可視範囲・正規化・全種の観測、混合 native の論理的出力位置。
- S03 一部: 全候補・混合 native の実訪問の識別と K2 優先。可能 port や型付きの比較成功だけでは訪問を認めない。
- S04 一部: 一般の元選択 head。S05 一部: 一般の順序付き捕捉。
- S06 一部: 一般 ordinary の元本文書込み。S07 一部: 一般 typed 書込み・保持。
- S08 一部: 混合 node の合成。S09 一部: 同一モデルの一般局所意味。
- S10 未証明: 実選択から一般 source node。S11 一部: 一般 tree/forest の lowering。
- S12 一部: 一般 tree の健全性。S13 未証明: 一般意味から固定辞書証拠。

**残り 13 = 未証明 3 + 一部 10。** I-65 Step 1 未完、Step 2/3 未着手。S1/S2 未完、C 後回し。旧 `Local`、C334 への橋、停止性、fixture 追加なし。承認済み spec で受理が実行順に依存する場合は確認しておらず、意味の選択や質問ノート起票はしていない。

次に必要なのは、(i) `SourceBundle.declarations` が実際の呼出し側で全て可視な出現を表す証明、(ii) 同じ最終状態の実観測規則が枝の検査を正確に開く証明と、未読・不一致・保留を混同しない候補全体の判断、(iii) 一般 typed 出力の発生と native syntax を actual logical ordinal でつなぐ証明。scope 付きの正の枝から、任意の候補についての排他性・観測完全性は主張しない。 また generic な exact セルは producer の `Request` と `Dictionary` を揃えるが、局所規則と出力生成は別の関係として渡している。実規則で同じ辞書を持つ異なる宣言／捕捉の導出を排除できない場合は、出力が有限証明の同じ局所導出（実宣言 ordinal・捕捉）から発生したことも添字または反転で結ぶ。全状態の辞書一意性を仮定して省かない。

## 検証と公開

- 開始は `2026-11-24T03:30:24.719Z`（`date -u`）。技術 pin `54847ecbda5a87d928ab508dcadcf7557e4e2e02`、同 Lean tree `02eb27512199cff7f004c46937b7feb849e47519`。[設計・次の接続](../design/dots-cycle-384-i67-exact-output-and-visits.md) は `035a998f34f16d8194f4defb0ed1921f32bc0ea0`。
- Lean 4.35.0 で新規 13 モジュールを `lean --trust=0 -DwarningAsError=true -o …` で個別に構築し、その `.olean` に対する独立 13 監査ファイルを `lake env lean --trust=0 -DwarningAsError=true <file>` で個別に実行。すべて exit 0。監査項目 57 は標準の `propext`、`Quot.sound`、`Classical.choice` の範囲（公理なしの項目もある）。ソース/import の既存閉包は `integration/m1-final` の 3,809 source blobs と一致。追加 Lean 26 ファイルの監査 import 規則・禁止トークン・改行も確認。
- 03:56 UTC 頃に実行環境が切断。native source の別案は確認を完了できず、公開しなかった。公開パスの exact bytes は検証済みローカル入力と GitHub から照合した。別実行環境での再コンパイル・全体 `lake build`・CI・Rust は実施していない。
- 公開は `work/dots-main` のみ expected-head / non-force。前周から累積 30 パス（新規 Lean 13、独立 Audit 13、barrel の末尾 import 13、設計 1、心拍 1、報告 1；barrel はパス数 1）。凍結二ファイルは Git blob ID のみ確認。使用量の枠は不明。
- 最終照合開始 `2026-11-24T04:20:27.970Z`（50 分経過）。
