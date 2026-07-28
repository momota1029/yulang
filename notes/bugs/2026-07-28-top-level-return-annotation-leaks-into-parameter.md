# トップレベル関数の戻り値注釈が構築先struct名と一致すると引数まで巻き込まれる

発見日: 2026-07-28
状態: 未修正
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

## 未確認事項

- `654fec0b` 以前の parameter/local binding 二重適用バグ（`f67dba12`）と
  同じ機構が原因か、それともトップレベル binding 固有の別経路か。
  `f67dba12` は「header result annotation と whole binding annotation の
  二重適用」を local binding で修正したが、本件はトップレベルで起きている。
  トップレベルは「二重適用を回避できている」はずだった
  （`crates/infer/src/lowering/body/mod.rs:2178` 付近）。ここが本件でも
  正しく機能しているか要確認。
- struct 名と戻り値注釈が一致することが条件か、それとも任意の nominal 型
  一致で起きるか（enum/error でも再現するか）は未確認。
- 引数が複数ある場合にどの引数が巻き込まれるか（全部か、body 内で
  struct field へ使われた引数だけか）は未確認。

## 関連

- `crates/infer/src/lowering/body/mod.rs`（トップレベル binding lowering、
  header result annotation と whole binding annotation の分離箇所）
- `f67dba12`（local binding での同種の二重適用を修正済み。トップレベル版が
  同じ根なのか別なのかが本件の核心）
