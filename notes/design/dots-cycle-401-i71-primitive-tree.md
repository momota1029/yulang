# C401: I-71 の型つき RHS に元の primitive 節点を残す

I-71（integration `793febb8a7f2069c7315a1a37954209395461c03`, inbox `eb64179ca0cf4f86fe36697b824b58fac3ffec12`）済み。今回の具体的な不足は、同じ選択 frame に対して B6 が与えた RHS の中の primitive が C400 の symbolic input に入らず、mixed RHS を丸ごと保持できないこと。C357 `names (.primitive _) = none` を declared 型として無理に読むのではなく、実際の `Use` と `Mode.primitive` による scalar / pair / emptyRecord / exactEmpty を、同じ Pattern に索引づけた構造節点として持つ。pair の両子も generic typed tree（従って下の nominal やさらに別の primitive も可能）。nominal の引数には元の kind と文脈分散を保持する。評価は同一モデル、`primitiveValue` の既存意味のみ。B4 が型推論を実行したり、失敗した lookup から拒否を出したりしない。

目標は、同じ有限の型つき RHS input から論理 capture を名称のまま代入し、元の構文木／番号／固定先を変えない出力を作ること（まず混在節点を含む RHS の意味）。`AuthoredBodyFrame393` の実 slot・B6 input を使い、旧 C386 literal vector を求めない。これは一般 `Classifies` 自身から実選択 frame を得る残件とは別で、S13bbba を閉じた内訳には数えない。S13 の分割・言語の追加・fixture・retention・停止性は行わない。
