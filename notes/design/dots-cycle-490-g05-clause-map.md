# C490: G05Goal の三つの境界を照合

固定命題は `GeneralDeclarativeI65I74G05Goal487.lean` の `G05Goal`。今回の作業による命題自体、旧入口、旧候補意味の変更はない。

| 固定の節 | 根拠と今回の追加 | 範囲 |
| --- | --- | --- |
| 旧報告／旧証拠の Bool と crossed tags | C488 `g05_coordinate_dispatch_keeps_every_old_tag_and_rejects_crossed_tags488`。C490 の受理集合の同値は同じ実行入口の新報告タグについてのみ。 | 旧入口にタグを再追加しない。 |
| 任意の検証成功が元の根、独立な報告、適合する同じ State のモデルごとの証拠を保つ | C488 `verified_g05_report_has_exact_original_coordinates_and_evidence_for_all_fitting_models488`。C490 は続行側の実装が何であっても、実際の全 K2 を元順でのみ拒否し、各陽性に同じ有限 constructor return が付くことを示す。 | 正確な元 prefix 許可と根から言えること。局所 verdict の意味や各モデルでの根拠には、固定の `G05ExactLocalProtocol487` と model-evidence の仮定が別に残る。 |
| 任意の厳密な報告が受理される有限証拠を持つ | C488 `independently_exact_g05_reports_reify_without_an_observation_order_or_arity_assumption488`。C490 は各元候補に独立に許された選択列のすべてを続行に再生できると特徴づけ、既に受理した証拠では局所 token だけの移行でも元の根と候補 tape が一切変わらず、あらゆる提出報告に対する受理と遅延ルートも同じことを示す。 | 局所判定を選ぶ規則、証拠を常に供給する compiler、辞書の合成は別。実 K2 がなければ、必要な証拠が供給されない場合は `notReplayed` であって拒否ではない。 |

公開した C490 の定理はそれぞれ個別の節・追加性質。命題 `G05Goal` を結合した定理は今回は宣言しない。C492 の期限を延ばさない。I-98 が止めた `G04Entry` や実局所型付けからの prior 生成へは戻らない。
