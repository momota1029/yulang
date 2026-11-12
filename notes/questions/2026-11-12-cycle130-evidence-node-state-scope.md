# V3 evidenceNode の状態の範囲

状態: 監督役レビュー待ち。意味論の変更は提案していない。既存定理・spec・Astra定義は変更していない。

## 遅延案（推奨）

現行V3とrecursiveFieldsは残す。今回の反例とモデルごとのEvidenceを公開し、辞書健全性の補題を「最終状態、または必要な候補制約の記録が証明された状態」に限る形で新しく設計する。どの前提をどの段階へ置くかは監督役が確認する。未記録の関連型等式をEvidenceから落として解決したことにはしない。

## 例とLeanで確かめる点

```yulang
role Out 'a:
    type out
impl Out (list 'a):
    type out = int
// 名前なしの入力は list 'x、名前つきの出力 target は 'x を指す需要。
// 元の制約は 'x = str を許すが、この候補の関連型等式を記録すると許さない。
```

具体的なsource IDと役割はLean fixtureで明示する。checkedな唯一の終端候補について、SafeKnown、Unique、Classify selectedが成り立つ。元stateにはlist str / output strのモデルがある一方、branchにはlist int / output intのモデルがある。悪いモデルでもprivate head intervalとprojectionは満たされ、要求された関連型出力だけが失敗する。

`GeneralDictionaryRecursiveObstruction.no_evidenceNode_of_output_sound`は、どんなEvidence実装であっても、この葉の証拠が実宣言のoutput=intを含意するなら、現行の全stateのEvidenceNodeは成立しないと述べる。これはEvidenceを都合よく選んだ反例ではない。

承認済み草稿の第4項はModels(Σ*)の任意モデルでの辞書健全性であり、Σ*は飽和後の安定状態である。現行のB4TargetV3.EvidenceNodeはStableや到達可能性の前提なしに任意stateへ量化する。そのためStepを実装するだけではこの局所フィールドの型を満たせない。一般B4の最終状態での主張そのものを否定してはいない。

## 他の案（未採用）

1. source境界の状態carrierに、必要な候補制約が記録されたことを保持し、合法なモデルの範囲と分類の対応を別途証明する。carrier変更の影響が大きい。
2. SurvivorまたはModelsの定義を強めて未記録stateを排除する。現行の独立候補意味が変わりうるため、dotは実施しない。

参照: spec/06-roles.md §6.3、2026-11-08-b4-main-statement-draft.md 第4項、Astra Item3dのBranchModelsと元Modelsの区別、今回のdesignとLean反例。
