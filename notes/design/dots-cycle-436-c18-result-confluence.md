# C436 / I-79: この singleton C18 の結果にだけ競合がない

前提は実際の新 `Leaf s q`（一つの visible unary variable-child head、元入力一つ、where なし、出力なし、authored lower なし、raw root 安全、同じ State の真の producer）。checker の成功やモデルの存在を仮定しない。成立する語の種類や source の受理を新しく決めない。以下は exact ソースを使った紙上の定理、Lean ではない。

- 旧 R17 の分類があるとする。`classification_has_exact_lane_rule426`（blob `8ebefffe…`）で旧 named trace か旧 projected leaf。後者は `OriginalProjectedLeaf426.onlyOutput`（`74112b1e…`）で元の q に出力一つを要求し、今回の空と矛盾。
- 旧 named `SourceTrace` が `.rootK2` なら、真の新 leaf の raw-safe に矛盾。`.other` なら、別紙 [R17 の旧診断を展開](dots-cycle-436-c18-inherited-priority.md) した各形に矛盾。`.selected event` なら、event の宣言が同じ visible singleton に入るので同じ row。 `completed_unary_gate_is_not_an_old_source_head406`（`GeneralDeclarativeI65I72CompletedNativeSourceIndex406.lean@8e33e060…`）はその row の旧 named `SourceHead` **そのもの**を除く。この最後の反証は、旧 selected trace の子が全部選ばれているとは仮定しない。旧 selected trace が pending / rejected に要約される枝も同時に除ける。従ってこの scoped leaf を持つ同じ (s,q) では旧 R17 の汎用結果はゼロ。
- 新 R18 が同じ q について二つの proof を持っても、候補リストの等式 `visible=[r₁]=[r₂]` から宣言 r₁=r₂。双方の tree は厳密に `.selected r₁.id []`。 `classification_exact`（`b05658f0…`）から同じ Result（辞書 `.node r₁.id []`）。元の `CompletedBody406.written` は `List.ofFn` で元の出力数ゼロ、`frameWhereKids400` は実 where の空から空。したがってこの場合に限り、新 entry の報告として再発行する producer write や追加の子はない。複数の適合する stored origin 探索や、隠れた証拠オブジェクトの一意性は主張しない。
- 定式化候補: `no_previous_classification_at_genuine_completed_leaf436` と `new_selected_result_is_unique_at_actual_leaf436`。これは既存 R17 の全入力 Bool の `rfl` 保存とは別の論証。C18 外で旧 checker が拒否する／誤るとは結論しない。raw K2 の場合には新 leaf 前提そのものが成立せず、従来の旧根をそのまま報告する。
