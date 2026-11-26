# C440 — 任意長の declared unary 接頭辞と実際の比較の複製

`compile_in_context_through_arbitrary_used_nominal_prefix440` は決め打ちの深さではない。比較する両端の構文が同じ有限な unary nominal 接頭辞を持ち、外側の宣言は invariant、中間部・内側のすべての宣言は value の used variance として同じ table から読めるとする。最内側に元の任意の二つの interval を置く。既存 `compileInContext` の実出力は `inheritedRows` の順序と重複を含む厳密な列になる。

中間の追加接頭辞数を k とすると、実際の raw emission は 4^(k+2) 行で、別の型の比較条件の集合は元の 4 条件（両区間それぞれと交差 2 つ）のまま。同じ任意の full assignment における `ContextDerives` の成立もその 4 条件と同値。Emitted row の重複削除や性能最適化は実装していない。table は distinct slot ごとの declared mode を与える前提で、unknown/unused に inferred mode を与えるわけではない。

これは比較の backend 定理であり、有限入力で選択判定まで通す `R20.check` の定義・深さや、元の literal source の表現範囲は変えない。standalone Audit 5 行、標準公理のみ、公式 Lean 4.35.0 strict focused。
