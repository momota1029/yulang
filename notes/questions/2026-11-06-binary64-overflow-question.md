# float literal の有限範囲外（2026-11-06）

## Q11. 最大有限値を超える小数 literal をどこまで受理するか

状態: **回答済み(2026-11-06): A**。最近接・偶数丸めの結果が有限なら受理し、無限大へ溢れる literal は静的に拒否する。`spec/03-expressions.md` 3.1に反映。以下は質問の記録。

既存 Q2 の IEEE 754 binary64 と最近接・偶数丸めは変更しない。
`spec/03-expressions.md` 3.1 は「有限の範囲内なら」の丸めを確定したが、
範囲を越えた token を source で拒否するか、無限大の値として受理するかは指定していない。

例（構文・値の説明用。source parser/oracle での実行結果ではない）:

```yulang
my huge = 1.0e309
my negative_huge = -1.0e309
my near_max = 1.7976931348623158e308
```

`near_max` は厳密な値が binary64 の最大有限値より少し大きいが、
IEEE の最近接・偶数丸めでは最大有限値になる。
`huge` はその丸めでも正の無限大になる。この二つを区別して決める必要がある。

- **A（推奨）:** 最近接・偶数丸めの結果が有限なら受理する。
  無限大へ overflow する literal は静的に拒否する。`near_max` は受理、`huge` は拒否。
- **B:** IEEE の最近接・偶数丸めを範囲外にも適用し、符号つき無限大を受理する。
  `near_max` は最大有限値、`huge` は正の無限大。
- **C:** 厳密な token の絶対値が最大有限値を超えた時点で静的に拒否する。
  `near_max` と `huge` をともに拒否する。

影響する義務: source の小数 literal elaboration、定数の診断、
Lean/Rust oracle の conversion result、有限範囲の端の受理完全性。
`Binary64Decimal.convert_success_iff` / `convert_boundary_iff` の範囲外分岐を
source の受理・診断へ接続する主張に関わる。
有限な値の比較・NaN の非反射性・有限範囲内の丸めの正確性には影響しない。

回答に依存しない実装は `Binary64Decimal.convert`。
厳密な絶対値が最大有限値以下の token は、整数演算だけで binary64 へ変換し、
全有限 bit pattern に対する最近接性と midpoint の偶数選択を証明した。
その範囲外は内部結果 `outsideFiniteRange` として区別する。
これは source の型エラーや runtime error の採用ではなく、上記の未決定箇所を表す境界である。
