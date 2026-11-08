# Cycle 3 list spread: source経路の独立レビュー

旧 Y2 `d4c8bc8fc`。既存 source と保存済み標準dumpを読み、名前衝突の改名対照を追加した。matcherの改修・ビルドはしていない。

## 既存失敗を起こす式をdumpで特定

`list-suffix-rest` の標準dumpには、pattern binder `d2288:last` が実際にある。しかしbodyの `(init,last)` の第2要素はそのbinderへのreferenceではない。

```text
e8398:(e8396:r3454:"#op:nullfix:last"->d396:"std.core.ops.#op:nullfix:last" e8397:())
```

schemeも `std::data::list::list 'a -> [std::control::flow::loop] (std::data::list::list 'a,int)`。`list-middle-rest` にも同じnullfix呼出がある。従って、初期suffix/middle試験は「束縛した末尾要素を返す」つもりのsourceが、標準環境では `last` 制御演算子を呼ぶ試験になっていた。初期のunhandled loop::lastをlist remainder matcherの失敗証拠として使ってはいけない。

## source経路

- `lib/std/core/ops.yu:9` は `pub nullfix(last) = loop_last()`。
- 同`:54` は `my loop_last() = std::control::flow::loop::last()`。
- `lib/std/control/flow.yu:18-21` は `loop` family の `last: () -> never` を宣言する。
- `crates/infer/src/lowering/expr/chain.rs:544-555` は Ident と Nullfix を別々にlowerする。Nullfixならローカル変数参照経路でなく `lower_nullfix_op_use_at` に進む。
- `crates/infer/src/lowering/expr/tail.rs:445-452` はsymbolのnullfix実装を解決しunitを適用する。dumpの形と一致する。
- pattern側 `crates/infer/src/lowering/pattern.rs:155-178` はtrue/falseとnullary constructor以外のbare nameをlambda paramとしてbindする。今回dumpにもlast binderはあるので、「pattern自体がlast演算子になった」という説明ではない。

この局所経路は保存済みdumpとsourceの双方で裏付けられる。コンパイラ内部全体のstep traceを取ったわけではないが、「実験bodyがbinderを使っていない」という点は単なる推測ではない。

## matcher/表示について言える範囲

`crates/mono-runtime/src/runtime/bind.rs:127-168` のlist matcherはprefix/suffix長を検査し、Rustのlist indexで前後要素を束縛、`index_range(prefix_len,suffix_start)` をrestに渡す。`crates/evidence-vm/src/runtime.rs:24628-24669` も同様にhost list sliceを作る。読んだ両実装には標準Yulangのloop::last呼出はない。よってこれらの局所matcherが直接この効果を要求するという仮説を支持しない。

一方、backend全体の経路や全型・全list長について正しいとは証明していない。matcherをhost実装で見つけただけでsource bridgeや一般完全性を証明したことにはならない。初期の「返り値を整数tupleだけにする」対照にもbodyに同じlastを残したため、表示系との切り分けとして不十分だった。この点を訂正する。first/prefixの時間切れにはlastを含まないため、今回の名前衝突だけでそのtimeoutまで説明しない。

## 改名対照

初期sourceを変更せず、新規case `list-suffix-rest-renamed` と `list-middle-rest-renamed` に `last` → `end_item` のみを施した。標準cacheを指定しcheck/run各30秒上限。全文は `runtime-cycle-3-list-renamed.md/json`。結果は下に追記する。

### 改名対照の実測結果

- suffix改名: check/runとも30秒timeout。値は未取得であり、成功・拒否のどちらとも判定しない。
- middle改名: checkは30秒timeout、runはexit0、`run roots [((1, [2, 3], 4), (1, [], 4), (0, [], 0))]`。

中間restの長さ4/2/1入力では、名前だけを変えて意図した結果が得られ、同じlist表示を含んでもloop::lastは発生しなかった。初期middle失敗をlist matcherやlist表示の欠陥とする説明はこの対照と合わない。suffixそのものは時間切れなので、middle成功をそのままsuffix成功に転用しない。check成功も主張しない。

親側で別の長時間標準checkが同時実行されており、資源競合の可能性を排除できない。時間切れを言語の停止性・拒否やモデルの失敗に置き換えない。以後新規の重い試験は開始していない。
