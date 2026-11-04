# 数値リテラル

## 1. 権威と対象範囲

このページは、`syntax-v0`の式位置で用いる整数リテラルと浮動小数点数リテラルを定める。
浮動小数点数の受理形式と字句境界は、2026年11月4日のparser-gap-closure追補にあるWP-4に従う。
対象は式の構文と直接Rowan CSTである。
PatternとTypeExpressionでは浮動小数点数を受理せず、数値型、精度、範囲、評価も定めない。

## 2. 受理構文

```text
Digit := "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9"
IntegerLiteral := Digit+
FloatLiteral := Digit+ "." Digit+ [ Exponent ]
              | Digit+ Exponent
Exponent := ("e" | "E") [ "+" | "-" ] Digit+
```

小数点の直後にはdigitが必要である。
指数記号と任意の符号の後にもdigitが必要である。
`1.5`、`0.25`、`1e3`、`2.5e-3`、`1E3`は浮動小数点数リテラルになる。

## 3. 受理と境界

式のvalue位置は、整数リテラルまたは浮動小数点数リテラルをprimary一つとして受理する。
完全な指数部は同じ浮動小数点数tokenに含める。
指数部が不完全な場合、直前の完全な整数または小数形式でtokenを閉じ、`e`または`E`以降を通常のrecoveryが所有する。

二つのdotは浮動小数点数tokenに含めない。
したがって、`0..10`、`0..`、`0..<10`、`1..`は整数から始まり、既存の`..`境界を保つ。
`1.`と`1.e3`もdotの直後にdigitがないため、整数から始まる。

field tailのdot直後にadjacentな整数がある場合、その整数は浮動小数点数の開始ではなくpositional field nameになる。
この局所境界は[fixed tailのページ](call-field-path-tails.md)で定める。

## 4. 直接Rowan CST

`IntegerLiteral`は`Integer` tokenを一つ直接持つ。
`FloatLiteral`は浮動小数点数のsource spelling全体を持つ`Float` tokenを一つ直接持つ。

```xml
<OperatorChain>
  <FloatLiteral><Float text="2.5e-3" /></FloatLiteral>
</OperatorChain>
```

## 5. Recovery

`1e`は整数と`e`のrecoveryになる。
`1e+`は整数と`e+`のrecoveryになる。
`1.`は整数と既存のdot-tail recoveryになる。
浮動小数点数のpattern構文は受理せず、pattern内のfloat形式は既存のinteger-patternとarm recoveryを通る。

## 6. Composition

数値リテラルは、prefix演算子、dynamic operator chain、ML application、call、index、および通常のprimaryを受理するほかの式位置で使える。
周囲の位置は[動的演算子列](operator-chain.md)で定める。
