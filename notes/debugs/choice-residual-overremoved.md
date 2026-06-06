# ⑧ choice の残差 effect 行が消えすぎる（解決済み: fixture indentation）

## テスト
`tests::choice_preserves_parse_residual_on_callback_and_result_effects` — `crates/yulang-infer/src/tests.rs`

`choice` は `p` / `q` を `catch` し、`parse::fail` だけを扱う。
未処理の `parse` effect は callback 側にも result 側にも残るため、テストは次を確認する。

- rendered type の `p` / `q` callback が `unit -> [...]` の形で effect row を持つ
- compact scheme 上で `p` / `q` / result の `parse` 残差が同じ `TypeVar` を共有する

## 2026-06-07 結論

最初の失敗原因は推論器本体ではなく、テスト fixture の Rust 文字列だった。

`"...\n\             ..."` のような Rust string continuation は、次行先頭の whitespace も含めて捨てる。
そのため、Yulang 入力として意図していた indentation が失われ、`choice` の body が空になっていた。

実際には次のような構造で lower されていた。

- `pub choice(...): ... =` は空 body の item
- `my snap = parse::snapshot()` は root level の別 item
- `catch p(): ...` も root level の別 item
- `p()` / `q()` は `choice` parameter scope の外に出るため、param ではなく unresolved `Ref` になる

この状態では `catch p()` が `choice` の本体に存在しないので、catch branch の不足や subtract の成否以前に、
callback の latent effect を観測できない。

## 修正

fixture を `concat!` で行単位に分け、各行の indentation を明示した。
これで `choice` body が正しく block として parse され、`p()` / `q()` が parameter として解決される。

また、compact 構造の assertion は「parse row が 1 本だけある」という表示上の正規形を要求しない形にした。
現在の compact 結果は、同じ残差変数を持つ parse row が nested / duplicated に見える場合がある。
このテストの責務は row 正規形の固定ではなく、`p` / `q` / result が同じ未処理 `parse` 残差を共有することの確認である。

2026-06-07 の再測定では、rendered type は概ね次の形になる。

```text
(unit -> [[parse<...>; ρ & [parse<...>; ρ]] & [parse<...>; ρ]] α)
-> (unit -> [[parse<...>; ρ & [parse<...>; ρ]] & [parse<...>; ρ]] α)
-> [parse<...>, ρ] α
```

したがって、`p` / `q` callback の effect は消えていない。
残っている違和感は row の nested / duplicated 表示であり、この regression の主対象ではない。

## バグ表

| | |
|---|---|
| 期待値（正）| rendered type の p/q callback は parse effect を持つ。compact では p_residual == q_residual == result_residual |
| 実際値（誤）| fixture の indentation が消え、`choice` body が空になった結果、p/q callback effect を持つ構造が作られていなかった |

## なぜ期待値が正しいか

`choice` は `parse::fail` を 1 種類 handle し、他の `parse` operation は素通しする。
したがって、`p` / `q` callback と `choice` result の effect は同じ残差 row を共有する。

`unit -> α` は「callback が pure」ではなく、この regression では `p()` / `q()` が param call として lower されていないことの症状だった。

## 見るべき場所

- `crates/yulang-infer/src/tests.rs` の fixture 文字列
- Yulang block indentation を含む Rust fixture では `concat!` など、indentation が source に残る書き方を使う

## 改竄防止

`p` / `q` callback が parse effect を持つことは choice のセマンティクスから確定。
期待を `(unit -> α) -> (unit -> α) -> ...` に下げて通すのは不可。

一方で、このテストは compact の row 正規形を 1 本に固定するものではない。
row 正規化を詰める場合は、別テストで「同じ残差の nested / duplicated parse row が表示段階でどうなるべきか」を扱う。
