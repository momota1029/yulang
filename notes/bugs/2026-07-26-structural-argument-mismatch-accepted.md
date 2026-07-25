# 構造型の引数不一致が受理され、誤った型の値が流出する

発見日: 2026-07-26
状態: 未修正
発見経緯: 効果操作のタプルペイロード調査（`notes/bugs/2026-07-25-effect-operation-tuple-payload.md`）の
副産物。Codex が mono IR 中の不正な coercion に気づき、Claude が再現・特性化した。

## 症状

タプルを要求する引数位置に、タプルでない値を渡しても受理される。
しかも**宣言と食い違う型の値がそのまま流出する**。

```yu
my f(p: (int, int)) = p
f 2
```

```console
$ yulang --std-root lib --no-cache check <f>
（診断なし、exit 0）

$ yulang --std-root lib --no-cache run --print-roots <f>
run roots [2]
```

`f` の宣言は `(int, int)` を返すと言っているのに、`2`（`int`）が返る。

`bool` でも同じ。

```yu
my f(p: (int, int)) = p
f true
```
```console
run roots [true]
```

## mono IR に現れる不正な変換

```console
$ yulang --std-root lib --no-cache dump <f> --mono | grep coerce
coerce[int => int -> unit]
coerce[int => (int, int)]
```

`int` から `(int, int)` へ、また `int` から `int -> unit` への coercion が挿入されている。
どちらも宣言されていない変換である。

## 引数を実際に使うと

分解しようとすると実行時に落ちる。

```yu
my f(p: (int, int)) = { my (a, b) = p; a + b }
f 2
```
```console
runtime error [yulang.pattern-mismatch]: no pattern matched the value
```

メモリ破壊ではなく構造化エラーだが、型が嘘をついていることに変わりはない。
`f` を通した値を別の場所で `(int, int)` として扱う限り、同じ形で破綻しうる。

## 2026-07-25 に閉じた 3 件との関係

同じ「型検査が不一致を受理する」系統だが、位置と型の種類が異なる。

| | 位置 | 型の種類 | 状態 |
|---|---|---|---|
| `my f(): bool = 42` | 戻り値注釈 | 名前付き | 2026-07-25 に修正 |
| `with: our x.m: bool = 42` | companion method 戻り値 | 名前付き | 2026-07-25 に修正 |
| `struct t { x: bool }; t { x: 42 }` | struct literal の field | 名前付き | 2026-07-25 に修正 |
| **`my f(p: (int,int)) = p; f 2`** | **引数** | **構造型（タプル）** | **未修正** |

昨日の 3 件はいずれも `NominalCastNeeded` を発火して OCAST 分類器まで届いており、
provenance が不完全なため fail-open で素通りしていた。本件が同じ経路を通るのか、
そもそも `NominalCastNeeded` を発火しないのかは未確認である。

## 既に捕まっている近縁のケース

タプルの**要素数**不一致は捕まる。ただし `check` ではなく specialize 段階である。

```yu
my g(x: (int, int)) = x
g (1, 2, 3)
```
```console
compile error [yulang.unsatisfied-subtype]: unsatisfied subtype constraint: (int, int, int) <: (int, int)
```

これは `tests/yulang/cases.toml` の `subtype_tuple_arity_provenance` として契約化済み
（`kind = "run"`。`check` では通るため）。

つまり「要素数が違うタプル」は捕まるが、「そもそもタプルでない」は捕まらない。

## 着手前に確認すること

- 本件が `NominalCastNeeded` を発火するか。発火するなら 2026-07-25 の 3 件と同じ
  provenance 補完で閉じられる可能性がある。発火しないなら別の機構が要る。
- 不正な `coerce[int => (int, int)]` を挿入しているのはどの経路か。
- 修正を活性化した時に既存コーパスが何件壊れるか。昨日の 3 件では `lib/std` / `examples` /
  `tests/yulang` のいずれも 0 件だったが、本件は構造型なので分布が違う可能性がある。
- `coerce[int => int -> unit]` の方も同じ原因か、独立か。

## 関連

- `notes/bugs/2026-07-12-function-result-annotation-conformance-gap.md`（2026-07-25 に解決）
- `notes/bugs/2026-07-12-struct-field-type-conformance-gap.md`（2026-07-25 に解決）
- `crates/infer/src/analysis/session/generalize.rs`、`crates/infer/src/lowering/constructor.rs`
  （昨日の修正が触った箇所。本件が同族なら近くにある可能性が高い）
