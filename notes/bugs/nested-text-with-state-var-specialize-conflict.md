# 入れ子 text_with + 状態変数の specialize slot 衝突

日付: 2026-07-02。発見: Claude (Fable 5)（`my &x = ... do` 糖衣の検証中）。
状態: **resolved**。糖衣とは独立の既存問題（手書き λ で同一エラーを再現済み）。

## 症状

`text_with` を入れ子にし、内側の callback から外側の状態変数を読むと、
`check` は通るが実行時（specialize 段）に落ちる:

```text
conflicting type candidates for slot 46:
  [std::io::file::file, std::io::file::io_err, 'open12]
  vs [&a#2:0(std::text::str::str), &b#2:1(std::text::str::str)]
```

## 再現（--host unsupported、mock handler 併用）

```yu
my edit() = std::io::file::text_with "/a": \a0 ->
    my $a = a0
    my inner = std::io::file::text_with "/b": \b0 ->
        my $b = b0
        &b = $b + $a          -- 外側の instance を内側の callback で使う
        &a = $a + "!"
        (($a, $b), $b)
    ((inner, $a), $a)
```

- `my &a = text_with("/a", do)` の糖衣形でも同一エラー（slot 番号のみ違う）。
- **状態変数を使わず純粋値（`a0` / `b0` の字句閉包）だけなら通る**。
  収載済みの `file_text_with_nested_cross_file` fixture はこの形で、
  本問題を（意図せず）回避している。
- 局所の無注釈関数（`with_val`）の入れ子 + 状態変数は check / run とも通る。
  つまり「注釈付き std 公開関数（`text_with: ... ['e] ...`）の row 変数へ、
  synthetic instance act の行が入る instantiation」と「file 行が入る
  instantiation」が specialize の同一 slot に合流するのが疑い所。

## 影響

- `my &x = ... do` 糖衣（実装済み）の単段使用・rollback・undet 分岐独立・
  局所関数入れ子はすべて動作する。壊れるのは「std の注釈付き with 系の
  入れ子 × 状態変数の交差」だけ。
- file 指示書の fixture 6（nested cross-file）は現行の純粋値形のままでよい。
  状態変数版の追加はこの bug の解決後。

## 手掛かり

- specialize2 の slot 単一化が、'e の二つの instantiation
  （[file, io_err, tail] と [instance acts]）を同一 slot に割り当てている。
  役割的には generic fallback / provider-env 依存の分類対象のはず。
- 過去の類例: role demand の中心乗っ取り（2026-06-13、Bounds 化で解決）と
  同系の「複数候補の合流」だが、こちらは effect row の slot。

## 解決

原因は `text_with` 糖衣ではなく、specialize2 の effect row candidate refinement だった。
入れ子の `text_with` と state var handler は、`e = file/io + &a + &b + e`
に近い recursive row equation を作る。既存 resolver は open tail が upper-prefix
へ到達している証拠を見ず、tail が一時的に閉じて見えた候補を hard upper として扱ったため、
`[file, io_err, tail]` と `[&a, &b]` の conflict になっていた。

修正では、closed upper に見える row でも、lower の open tail からその upper item
へ到達する upper-bound chain がある場合だけ、finite row 解へ畳むようにした。
到達証拠が無い `[file, tail] <: [&state]` のような通常の不一致は、これまで通り
refinement しない。

固定した regression:

- `tests/yulang/regressions/runtime/file_text_with_nested_state_var.yu`
- `file_text_with_nested_state_var` contract case
- specialize2 unit tests:
  - `effect_row_recursive_tail_refines_to_finite_closed_row`
  - `effect_row_tail_does_not_refine_to_unreachable_closed_upper`
