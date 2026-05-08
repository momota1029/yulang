# Language Surface TODO

目的: 基本機能がまとまりを持って見える程度まで増えたので、言語として見える判断を明示的に保つ。

## Error handling

設計参照:

- `notes/design/error-handling-plan.md`

現在の方向:

- `error` は parser keyword として入っている。
- `error fs_err:` は enum と act operation をまとめて定義する最小 sugar として入っている。
- error constructor は data constructor と effect operation の両方として使える。
- `fail` は `std::prelude` の先頭側で `prefix(fail)` として export される。parser/lower の keyword や特例ではない。
- 現在の `fail` は effect operation を prefix で読ませる暫定 no-op operator。error value と対応 operation をつなぐ generated `fail` はまだ未実装。
- 最終的な `fail err` は error value と対応する operation をつなぐ。role に固定しない。
- `not` / `return` / `last` / `next` / `redo` は parser builtin ではなく prelude の operator export として扱う。
- list の末尾取得は `xs.last` を優先し、`last xs` という関数呼び出し互換は持たない。
- `die` / `warn` / `say` は Perl/Raku 系の scripting convenience として別枠で扱う。
- `std::undet` の分岐破棄は `reject` に寄せ、error の `fail` と分ける。
- `from` entry は広い error family への cast / wrapper を生成する。`error` 専用ではなく、ordinary enum でも使える方向にする。
- `variant from source_type` は ordinary enum / error の単一 payload variant として parse され、`Cast source_type -> enum_type` impl を生成する。
- `std::result::result 'ok 'err` は入っている。
- `error E:` は `E::wrap` を生成する。これは対応する単一 error effect を捕まえて `result ok E` に閉じる helper として扱う。
- `io_err::raise` のような generated aggregation handler は狭い error effect を広いものへ集約する。role method ではなく、error namespace に生える関数として扱う。

TODO:

- `from` entry の collision rule と diagnostics を固める。
- generated `fail` surface の正確な形を定義する。特に data constructor と same-name effect operation の文脈解決を固定する。
- `die` / `warn` / `say` の std placement と host behavior を決める。
- `Cast` を role、builtin relation、syntax-directed conversion のどれにするか決める。
- `enum` variant の `from` grammar と collision rule を決める。
- generated `raise` handler の signature と desugaring を決める。
- anyhow 的な `any_err` と、`Display E` を要求して `result ok any_err` に落とす primitive `catch_any` / `wrap_any` を設計する。
- constructor-like effect arms の handler syntax を決める。
- `never` が user-facing signature にどう現れるか決める。
- `E::wrap` で `never` 計算を包む時に成功側型をどう明示・既定化するか決める。

## Special-case reduction

目的: parser / lowering に埋め込まれた std 名や局所的な構文例外を減らし、できるだけ prelude / std の宣言と一般規則へ寄せる。

現在:

- `not` は `std::ops` の operator export に寄せ、prelude はそれを reexport する。
- `return` / `last` / `next` / `redo` / `fail` は prelude の operator export に寄せた。
- `last xs` 互換は持たない。list の末尾取得は `xs.last` を使う。
- `+` / `-` / `*` / `/` / 比較演算子は `std::ops` に operator export を置き、prelude はそれを reexport する。
  - downstream parse の構文 surface は `std::ops` / `std::prelude` 宣言から取れる。
  - `!=` は lower 特例を外し、`std::ops` の ordinary operator wrapper で扱う。
  - `+` / `-` / `*` / `/` / `==` / `<` / `<=` / `>` / `>=` も lower の role method bridge を外し、ordinary operator wrapper で扱う。
  - operator wrapper の direct role method call は、forward constraints と transparent wrapper export で concrete role method へ閉じる。
- `lazy` operator header を追加した。lazy operator は operand をすべて `() -> value` thunk として受け取る。
- `and` / `or` は lower 特例ではなく、`std::ops` の `pub lazy infix` operator として扱う。

残り候補:

- `sub` / `for` / `var` は synthetic act を生成する。これは単純な std 関数化ではなく、糖衣展開の入口として責務を明示する。
- list literal / list spread は runtime primitive list と密結合している。標準ライブラリ surface と primitive lower の境界を明示する。

## Result type

- `result 'ok 'err = ok 'ok | err 'err` は `std::result` に追加済み。
- `result` は最初の error mechanism ではなく、effectful computation を value に閉じる方法として扱う。
- `std::result` には `map` / `and_then` / `unwrap_or` を追加済み。
- helper function を決める。
  - `map_err`
  - `or_else`
  - `E::wrap` 以外の error effects と result values の変換

## Casts

設計参照:

- `notes/design/casts.md`

TODO:

- どの cast を implicit、explicit、forbidden にするか決める。
- `from` cast は variant に由来する predictable な widening として扱う。
- ambiguous casts に対して予測しやすい diagnostics を保つ。

## Derive

目的: `error` sugar、`from`、`Display`、`any_err` で増える定型 impl
生成を、後から見ても責務が分かる surface に整理する。

TODO:

- `derive Display` の対象と生成規則を決める。
- `derive via` の構文を決める。
- `derive via` が委譲してよい role / method / assoc type の範囲を決める。
- `error` sugar が暗黙生成する `Throw` / `wrap` / 将来の `Display` と
  explicit derive の責務境界を決める。
- `variant from source_type` と derive-based cast generation の関係を整理する。
- generated impl の由来を diagnostics / IR で追えるようにする。
- derive が role selection の曖昧さを増やす場合の diagnostics を決める。

## Optional records

設計参照:

- `notes/design/optional-records.md`

TODO:

- default evaluation order を明確にする。
- subtyping との相互作用を明確にする。
- missing fields の runtime behavior を明確にする。
- 悪い optional-record pattern に対して focused diagnostics を追加する。

## References

TODO:

- `&xs[0].field` のような nested projections を明確にする。
- string index update semantics を入れるつもりなら決める。
- `$x` と `&x` を小さな example 付きで文書化する。

## Effects

TODO:

- handler type examples を追加する。
- unhandled effect diagnostics を改善する。
- hygiene / id stack の前提は、user に関係する場合だけ文書化する。
- host effects は call site では普通の function のように見える状態を保つ。
