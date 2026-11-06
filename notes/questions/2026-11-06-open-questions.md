# 未決定の問い（2026-11-06）

ここにある選択肢は仕様の決定ではない。推奨は先頭に置く。
既存の決定を広げず、回答に依存しない核と証明を先に進める。

## Q1. operation の payload pattern が非網羅の catch を許すか

状態: **未回答**。出典: `spec/03-expressions.md` 3.8、`spec/05-effects.md` 5.2。
operation arm の payload pattern と value arm は書けるが、operation ごとの
payload が非網羅のときの扱いは、現在の記述から確定できない。

例（構文の説明用。parser/oracle 実行はしていない）:

```yulang
act ask:
    our choose: bool -> int

catch action:
    ask::choose true, k -> k 1
    v -> v
// action が ask::choose false を起こす場合
```

- **A（推奨）:** 扱う operation ごとに payload pattern の網羅性を静的に要求する。
  guard 付き arm を網羅に数えず、非網羅なら拒否する。網羅できた operation key のみ行から引く。
- **B:** 非網羅の payload arm も許す。合う arm がない要求は元の継続とともに外へ渡し、
  その operation key を残余行に残す。

影響する義務: source arm の operation ごとの編成、payload pattern の網羅性、
source `catch` から `MultiOperationHandlerTyping.Expr.handler` への翻訳、行の残余の健全性。
同じ operation の arm が複数あることを、一律に拒否する仕様は追加していない。

この回答に依存せず証明した範囲: 相異なる解決済み operation key ごとに一つの全域な body を持つ
有限表の実行・独立型付け・checker の一致、shallow/multi-shot、許可 mask と符号付き重み。
表の key 一意性はこの核の表現条件であり、source payload arm の意味の決定ではない。

## Q2. 小数 literal の float はどの精度と丸めを持つか

状態: **未回答**。`spec/03-expressions.md` 3.1 は整数を任意精度、小数 literal を `float` とするが、
float の精度・丸めは書いていない。今回の依頼の「任意精度の整数・小数」が、小数にも任意精度を
要求するかを含めて決める必要がある。旧 `Inference.Base` には float 自体がまだない。

例: `0.1`、`9007199254740993.0`、非常に大きい指数を持つ小数。
仮数を全部保存することと、評価後の数値に丸めがないことは異なる。

- **A（推奨。通常の float と実装の小ささを優先する場合）:** IEEE 754 binary64。
  有限の範囲内の literal は最近接・偶数丸め。小数も任意精度という要求なら、この案は採らない。
- **B:** 有限小数を任意精度の十進数として正確に保持する。割算等の非有限小数の規則は別に定める。
- **C:** 任意精度浮動小数とし、精度・丸め context を持つ。context の渡し方も必要になる。

影響する義務: `LiteralValues.ofDecimal` の具体化、Lean/Rust oracle の値codec、
数値演算、float literal の解釈の一致。比較規則は精度と独立に次の問いへ分ける。
現在どの案も採用していない。`DecimalToken` と明示的な解釈引数だけを追加し、
整数・文字列・bool・unit と整数範囲の証明を先に閉じた。

## Q3. float literal pattern の比較は数値比較か、表現の一致か

状態: **未回答**。Q2の精度とは別の問い。
例: `0.0` のpatternは `-0.0` に合うか。選んだfloatモデルにNaNがある場合、NaN同士は合うか。

- **A（推奨）:** 選んだfloatの数値比較に合わせる。IEEEモデルなら正負の零は等しく、NaNは自分にも一致しない。
- **B:** 保存表現の一致にする。IEEEモデルならbit patternを比較し、正負の零を区別する。
- **C:** float literal pattern を静的に拒否し、必要ならguardで比較する。

影響する義務: `LiteralValues.matchCheck` のfloat比較、独立関係 `Matches` の具体化、
float patternの網羅性。保存値の構造的な等号 `eqCheck` と、言語のpattern比較は区別する。
現在は比較関数と関係の正確性を明示的な引数に取り、反射性を仮定しない。
整数・文字列・bool・unitの比較はこの回答に依存せず閉じている。
