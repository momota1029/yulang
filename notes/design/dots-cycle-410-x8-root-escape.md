# C410: X8 の根と、調べない再帰 payload を分離する

I-74 の C02 だけを扱う。spec/06-roles.md K2/X8 `impl Len (list 'a)` の例では、引数の根は循環上になく、`'a` は list 引数の再帰値を捕捉するだけなので展開しない。C01 の全グラフ rank を使わない。

- raw graph: 名の alias は同じ色。根を 0、構造辺で根から出た領域を 1、無関係を 2 などとする。0/1 の所有者からの全構造辺は 1 へ行くと元の無濾過の equations 上で検査する。1 内を閉じ、根の alias に戻らない。色 1 の循環は認める。X8 の根は 0、payload は 1。失敗は C02 checker の false であり拒否判断ではない。
- actual declaration: 同じ入力の実 role・全可視 singleton・元の宣言・C357 の本来の value/invariant mode を確認。元 1 引数の点 nominal と、その 1 引数の元 payload 名から exact `DeepRead.nominal` を作る。head の子は literal variable のため構造的な訪問を生まない。空 where/出力に限る。
- 追加規則の和 `R2` と `DictionarySound R2` は既存の固定辞書を変更しない。実行版 witness は元 origin ordinal と有限色列だけで、モデル・判定証明を持たない。旧分岐はそのまま。 `check_sound` は同じ State・元出現・同じ exact report の全 fitting model。C03/X9 の where 子が再帰型を調べるケースは別行。
