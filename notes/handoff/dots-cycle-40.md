# Cycle40: computed structural carrier coverage

## 状態と部分目標
通知13:27:19Z、実着手13:31:49Z。最新 integration/m1-final@8681ed2fa の standing orders/inbox を再取得。前回 cycle39 completed と報告を確認、稼働ビルド・並行writerなし。上限なし。開始心拍は3a18d3246で公開し、再取得して一致確認。作業場はyulang一つ、空き49GB。

部分目標: 前回の有限carrierを外部前提にせず、入力構文から計算したcarrierが全ての支持規則導出を含み、正規化がその最小閉包となること。これは達成。既存の分解・推移規則に対する完全性であり、意味的部分型全体に対する完全性ではない。

## 追加定理
新規 `Yulang.CommonRoleStructuralCarrierCoverage` の17定理。以下、全自然数n、全 `Atom (Fin n)` のseed列、全対象atomを量化する。充足可能性は前提にしない。`Derives` はseed・既存の構造分解・推移合成だけを持つ独立帰納判断で、carrier/indexの側条件を持たない。

- `self_terms`: 全型term tは自身から計算するtermsに属する。補助。
- `descendants`: 全tとそのterms内のsについて、sの全termsとrowsはtのものに含まれる。補助。
- `expand_supported`: 全term/row pool、全自然数fuel、全l,rについて、端点の全子term/rowがpoolにあるなら、実分解が作る全atomも同じ条件を満たす。補助。
- `pool_descendants`: seedのtypePool内の任意tの全terms/rowsはseedのpool内。補助。
- `carrier_iff`: atomが計算carrierに属する iff その全支持term/rowがseedのpool内。補助。
- `seed_coverage`: 任意のseed atomは計算carrier内。補助。
- `split_coverage`: carrier内の任意atomを実分解した全atomもcarrier内。補助。
- `trans_coverage`: carrier内の任意2atomのcomposeが作る全atomもcarrier内。補助。
- `derives_coverage`: 任意atomが独立Derivesで導かれるなら計算carrierに属する。完全性補助。
- `indexed_sound`: 全seed、任意carrier uとそのindex iについて、旧indexed Derivedが成立すればatom u[i]の新Derivesが成立。健全性補助。
- `derives_seen`: Derivesで導かれた任意atomについて、seeds++carrierのそのatomを指す全indexは実seenに入る。完全性補助。
- `normalize_membership`: 正規化出力にatomが属する iff Derives seeds atom。支持規則に関する健全性・完全性。全意味的部分型を対象にしたものではない。
- `derives_cut`: 任意moreの全seedが元seedから導かれ、atomがmoreから導かれるなら、元seedから導かれる。補助。
- `normalize_idempotent`: 任意atomについて、再正規化後への所属 iff 一度の正規化後への所属。補助・閉包。リスト順序や重複回数の等式ではない。
- `normalize_congr`: 任意2seed列の全atom所属が一致すれば、正規化後の全atom所属も一致。順序・重複に依らない集合としての正準性。補助。
- `normalize_coverage`: 任意正規化出力atomはseedから計算したcarrier内。補助。
- `normalize_least`: 全atom述語Pについて、seedを含み実分解・composeに閉じているなら、全正規化出力はPを満たす。補助・最小性。

新しい意味論の決定なし、質問ノートなし。既存の定義・定理は変更せず、新モジュールとroot/Audit/READMEの追記。主型性は主張しない。

## 残る橋
一般B4の5橋は残る。今回で前回の「支持規則に対する計算carrierの十分性」は閉じた。一般意味的部分型完全性、全constructor対応、source/receiver生成、role feedbackの停止・最終分類、X13〜X16の外側入口は未達。正規化再実行のリスト構造的冪等性は未達。有限carrierの三乗規則生成の性能は未検証。
次の候補: (1) 支持規則閉包をmaterialization/自己出力診断の正準性へ接続、(2) source生成の意味保存、(3) role feedback停止。支持規則の閉包が閉じたことをB4完成とはしない。

## Yulang2との照合
取得済み notes/audit/x-oracle-types-details.md のX13〜X17と spec/04-types の構造規則を確認。既存のCommon意味論と分解規則を変えない。最新audit再取得と新実機照合は未実行。

## 検証
`cd lean && lake build --wfail Yulang.CommonRoleStructuralCarrierCoverage` と
`lake env lean --trust=0 /tmp/cycle40-audit.lean`。
323 jobs、全17定理の監査PASS。全体build・全Audit・verify-lean.shは指示に従い未実行。使用量枠不明。

~~~text
✔ [323/323] Built Yulang.CommonRoleStructuralCarrierCoverage (2.1s)
Build completed successfully (323 jobs).
BUILD_EXIT=0
'Yulang.CommonRoleStructuralCarrierCoverage.self_terms' depends on axioms: [propext]
'Yulang.CommonRoleStructuralCarrierCoverage.descendants' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralCarrierCoverage.expand_supported' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralCarrierCoverage.pool_descendants' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralCarrierCoverage.carrier_iff' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralCarrierCoverage.seed_coverage' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralCarrierCoverage.split_coverage' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralCarrierCoverage.trans_coverage' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralCarrierCoverage.derives_coverage' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralCarrierCoverage.indexed_sound' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralCarrierCoverage.derives_seen' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleStructuralCarrierCoverage.normalize_membership' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleStructuralCarrierCoverage.derives_cut' depends on axioms: [propext]
'Yulang.CommonRoleStructuralCarrierCoverage.normalize_idempotent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleStructuralCarrierCoverage.normalize_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleStructuralCarrierCoverage.normalize_coverage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleStructuralCarrierCoverage.normalize_least' depends on axioms: [propext, Classical.choice, Quot.sound]
AUDIT_EXIT=0
~~~

## 公開・時間
GitHubアプリの個別blobとSHA treeで全変更を一括公開し、非force・expected-headでwork/dots-mainのみを更新する。公開後は全treeを取得して比較する。完了確認は親への報告にも記載。対象8ファイル。中断・承認待ちなし。開始時刻は実時計、完了心拍も実時計を使用。

読取りレビューでも、carrierの外部前提がないことと規則完全性の限定を確認。行制約の一般推移は規則系に含まれない。

最終ref更新準備時刻 2026-11-09T13:42:23Z。公開API処理のため10分心拍の境界を約1分越えたが、完了時刻を実時計で更新して公開。
