# F1追加監査: 高階の明示境界と実行段階

基点は `x-oracle.md`。意味論の提案ではなく、旧実機の成功範囲と失敗段階を切り分ける。

## 共通入力

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our higher(f: [ping] int -> [ping] int) = f(ping::get())
handle(higher plain)
```

`f` の注釈と `plain`/`\x -> plain x` だけを変えた。全12入力で `check` は0、`dump --poly`は0。下表は `run --print-roots`。

| fの注釈 | plain | eta wrapper |
|---|---|---|
| `[ping] int -> [ping] int` | exit1, conflicting type candidates: [ping] vs [] | 同じ |
| `[ping] int -> int` | exit0, 7 | exit0, 7 |
| `int -> [ping] int` | exit1, conflicting type candidates: [ping] vs [] | 同じ |
| `[_] int -> [ping] int` | exit1, unhandled ping::get | exit0, 7 |
| `[ping] int -> [_] int` | exit0, 7 | exit0, 7 |
| `int -> int` | exit0, 7 | exit0, 7 |

注釈なし高階、直接適用、pipeも7を返す。これらはF1の通るべき具体例で、全高階関数の完全性を証明しない。

## 失敗段階

- 明示両row版は `dump --poly-raw` 成功だが `dump --mono` と `dump --runtime-ir` でも同じconflictとなる。実行器に到達する前のspecialization側のエラーであり、単にhandlerの実行時意味論の問題とはいえない。
- interpreter/evidence-vm両方で明示両rowは同じ失敗、引数rowのみ版は7、wildarg直接版はunhandled、wildarg eta版は7だった。バックエンド固有問題だけとは説明できない。
- wildarg直接版はmono生成自体は成功。従って明示両rowの失敗と同じ段階ではない。具体的なadapter/hygiene経路の根本原因は未特定。
- エラー文字列の定義は旧 `crates/specialize/src/lib.rs:305–313`、生成候補が複数あり、stacktraceを取得していない。特定のresolver行を原因と断言しない。

## 新spec / Leanへの含意

旧 `constraints/machine/propagate.rs:234–245` は純粋引数slot (`Neg::Bot`) なら期待引数行を戻り行へ流す特例を持つ。単なる空行制約ではない。

新 `spec/05-effects.md` §5.5c は考え方を確定し、cast/subtypeの位置付けとcarrier表現の細部を要確認としている。`Common.common_arrow_iff` の標準矢印関係にはこの特例がなく、`Core.CommonSyntax.Typing.strictApp` の実引数行joinは関数間の変換とは別である。前回の質問ノートの未決定範囲は維持する。

この実機conflictを新specの「拒否すべき例」として採用しない。型検査成功を実行可能性の確認としない。X25全体を旧実機と一致済み/Lean統合済みとも言わない。

全入力・出力は `runtime-cycle-2-effects-patterns.md`。本文の表は解釈を含む要約である。

## 標準prelude対照

標準prelude有りでも、明示両row版はspecialization conflict（155.151秒）、wildarg直接版はunhandled（0.207秒）、wildarg eta版は7（0.224秒）。no-preludeだけが原因という説明にはならない。標準preludeは指定Y2のlibから読み、実装は変更していない。
