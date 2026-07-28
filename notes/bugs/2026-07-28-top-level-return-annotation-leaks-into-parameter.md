# トップレベル関数の戻り値注釈が構築先struct名と一致すると引数まで巻き込まれる

発見日: 2026-07-28
状態: **修正済み（2026-07-28、`f327989c`）**
発見経緯: `notes/design/2026-07-28-subtype-fallthrough-closure.md` の STF-H push 後、
CI で `my_type_ancestry_allowed` 契約が回帰。その fixture 修正中に、修正案自体が
別の pre-existing バグ（本件）に阻まれた。

## 症状

トップレベル関数の戻り値型注釈が、body内で構築する struct 型と一致すると、
**注釈の効果が戻り値だけでなく引数側にも及ぶ**。

```yu
struct zzz { qqq: int }
my mk (a: int): zzz = zzz { qqq: a }
mk 1
```

```console
compile error [yulang.lowering]: source has lowering errors
  detail: cannot use `int` where `zzz` is required: no implicit cast from `int` to `zzz`
  hint: run `yulang check` to see source ranges before running
```

`mk` の宣言は `(a: int): zzz` であって `a` を `zzz` に注釈していないのに、
`mk 1` が「`int` は `zzz` が要る場所では使えない」と拒否される。

`dump --poly` で見ると、`mk` の推論型が `(int & zzz) -> zzz` という intersection に
なっている。

## 戻り値注釈を外すと直る

```yu
struct zzz { qqq: int }
my mk (a: int) = zzz { qqq: a }
mk 1
```

```console
run roots [zzz({qqq: 1})]
```

## project 開始前から存在する

`175db5b6`（今日の subtype fallthrough closure project 開始前）でも同じ形で再現した。
今日の一連の修正（`650fec0b`、STF-D〜H等）とは無関係の独立したバグである。

## 発見した経緯（誤解に注意）

`file_mock_text_with_rollback_on_error`（`notes/bugs/2026-07-28-local-var-effect-residual-transport-gap.md`）
とは無関係。あちらは STF-H の後に露出した effect residual の問題で、
本件は STF-H の bisect 中に**別の fixture 修正を試みていて**偶然踏んだ。

`my_type_ancestry_allowed.yu`（STF-H が `int <: owner::hidden` の暗黙変換を
正しく拒否するようになった際に発覚。fixture 自体が fail-open coercion に
依存していた——これは正しく閉じられた。その修正案として
`my make (value: int): hidden = hidden { raw: value }` という形を試したところ、
本件バグに阻まれた）。

## 根本原因（判明済み）

`f67dba12`（local binding の二重適用）とは**別の機構**だった。
`crates/infer/src/lowering/body/mod.rs:2178` 付近のトップレベル binding lowering は
実際には二重適用を正しく回避していて、本件はそこに到達すらしていなかった。

真因は **parser の precedence バグ**。ML-style 適用（`mk (a: int): zzz` のように
括弧の前にスペースがある形）では、末尾の `: zzz` が binding 自身の戻り値注釈ではなく、
**最後の引数パターン `(a: int)` の中に飲み込まれて**しまっていた
（`crates/parser/src/pat/parse.rs:123` 付近、ML 引数を外側と同じ `min_prec` で
parse していたため `TypeAnn` がそのまま届いていた）。

括弧無し（`mk(a: int): zzz`、ApplyC 形）は最初から正しく parse できていた。
つまり「struct 名と戻り値型が一致する」ことは条件ではなく、**ML-style 適用に
戻り値注釈を付けること自体**が条件だった。引数が複数ある場合も、影響を受けるのは
常に最後の引数だけだった。

## 修正

`Prec::ApplyML` という TypeAnn より強い precedence 階層を新設し、ML 引数の nud を
その固定 precedence で parse するよう変更（`crates/parser/src/pat/parse.rs`）。
括弧内部の注釈（`(a: int)` 自体）の解釈は変えていない。infer 側は無変更——
純粋に parser 層のバグだった。

検証: parser 全8バイナリ350件、infer 991件、yulang 376件（既知flake1件除く）、
`--test cli` 158件、stdlib 全体の `check-poly-std` でエラー0件。判明していた
再現条件マトリクス（struct/enum/qualified nominal 戻り値、中間 `my` 束縛、
複数引数、local ML-style binding）を全て再検証し修正を確認。

## 関連

- `crates/parser/src/pat/parse.rs`（修正箇所、`Prec::ApplyML`）
- `crates/infer/src/lowering/body/mod.rs`（トップレベル binding lowering。
  疑ったが無関係と判明）
- `f67dba12`（local binding での別の二重適用バグ。似た症状だが機構は無関係）
