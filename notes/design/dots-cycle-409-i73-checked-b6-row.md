# C409: R₀ の実書き込みの検査

最初の C 行は、R₀ が既に含む選択済み変数系の、元の B6 型木つき固定出力。Checker408 と R₀ と DictionaryEvidence は変更しない。元の選択（全可視候補、元 role 行、raw K2 優先）を別に照合した後で、同じ State の元の宣言から associated body を lookup し、元の出現・宣言順・出力順・Body で B6 を読む。元の capture 名を代入した木を報告と構造比較し、実 State の equations に同じ固定先と同じ RHS の表現があることを検査する。形が検査外なら false（言語の rejected とは別）。

先に局所 API: `replayOutput (p : Problem) (frame : AuthoredBodyFrame393 p.state.core p.root) (i : Fin …) (row : Nat) : Option (…)`。成功から元 `NamedMixedOutput401`・`fixedValueCode403` と元の固定行の一致を得る。元の frame は出力から逆算しない。すべてを top に接続できた場合にのみ、`check … = true → ClassifiedAs … ∧ ∀ m, Fits … m → ReportEvidence …` を報告する。
