# C440 — X14 に対応する比較の正確な出力

異なる元の区間 `(a,b)` と `(c,d)` を同じ Outer/Inner の式に置いて、既存の `compileInContext` をそのまま使う。外側は declared invariant、内側は declared invariant/covariant/contravariant の任意。出力は順序を保つ次の 4 家族（各 4 atom、重複削除しない）。

```
       first-inner ↔ first-inner : [(a,b),(a,b),(a,b),(a,b)]
       first-inner → last-inner  : [(a,b),(a,d),(c,b),(c,d)]
       last-inner  → first-inner : [(c,d),(c,b),(a,d),(a,b)]
       last-inner  ↔ last-inner  : [(c,d),(c,d),(c,d),(c,d)]
```

各ペアは元の `Atom.tyLe (.var x) (.var y)`。無名行を置換して一方向を捨てない。宣言テーブルを引く既存 compiler から生成リストを等式で導出。両端の旧 Full semantic carrier の割当がそれぞれ scalar Int と Float を表すなら、同じ model で `ContextDerives` は不可能（rank 0 における既存 probe で両者を区別）。旧 TyTerm が直接 Float を構文として持つことや、元の X14 literal source 全体のフロントエンドが動くことは意味しない。R20 の狭い正の辞書入口はそのまま。

`GeneralDeclarativeI65I74NestedInvariantCrossings440` と独立 Audit を公式 Lean4.35.0 strict で検証。5 axiom 行は標準のみ。
