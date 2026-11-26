# C441 — 同じ元の row / value の取り違えがないこと

二つのデータ wire が同じ元 State/request に対し、この R21 分岐でともに成功したとき、本人が書いた可視候補と binder 順と辞書報告が同じ。同じ適合モデルでは、row の実スロット名どうし、value の実スロット名どうしが文字どおり一致する。それぞれを値の等価性で後付けしていない。元の `nativeSyntax` が同じ root slot の二つの authored reads を持つことを使い、`Sum.inr` の row と `Sum.inl` の value を別々に反転する。

任意の完全な型の carrier では、本物の二引数 `nominal [inr row,inl value]` と、どの legacy `.nominal ...` の all-value コンパイラ結果も同値にならない（同じ名・同じ arity でも）。これが legacy raw `Expr` を捏造せず元の typed origins を使う理由。raw graph 自体は引き続き K2 のため未フィルタのまま。

`WindowMeaning` は **宣言された original syntax と元の row/value の拘束** を語る。別の ordinary raw state の root 値に、この mixed literal 全体との同値を要求する旧 `HeadMeaning` を推定しない。この区別は実モデルを用いた独立 QA でも確認。今周は古い lane を変更したり native を legacy に平坦化したりしていない。追加 production と独立 Audit 5 件、公式 Lean 4.35.0 strict、標準公理のみ。
