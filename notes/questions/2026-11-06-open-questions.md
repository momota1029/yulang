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
