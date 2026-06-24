# Explicit Effect Contract Metadata

2026-06-24 時点の callback effect contract metadata の設計メモ。

このメモは、source annotation で明示された effect capture contract を、mono 型の形から
推測し直さず、lowering で抽出した構造化 metadata として specialize へ渡す方針を固定する。

## 背景

Yulang の handler hygiene は、型推論中の directed stack weight で表す。これは subtype
constraint の証拠であり、公開型へそのまま出すものではない。

一方で runtime は、specialize 後に実行される関数値や thunk がどの handler boundary を
越えてきたかを守る必要がある。runtime は型推論の row 文字列を見ても、どの effect が
source annotation によって捕捉契約されたものかを復元できない。

特に次の二つは意味が違う。

- inferred callback effect: 関数値の型から推論された latent effect
- explicit effect contract: source annotation が「この effect は handler が捕捉してよい」と
  明示した contract

この区別を mono 型から復元しようとすると、同じ型形状を持つだけの callback まで contract と
扱ってしまう。これは handler hygiene の規則ではなく、後段の推測に過ぎない。

## 現在の表現

`poly::expr::Arena` は lambda parameter の `DefId` に対して、明示 contract を保存する。

```rust
arg_effect_contracts: FxHashMap<DefId, ArgEffectContract>
```

`ArgEffectContract` は runtime marker へ変換できる最小情報だけを持つ。

```rust
struct ArgEffectContract {
    markers: Vec<ArgEffectContractMarker>,
}

struct ArgEffectContractMarker {
    path: Vec<String>,
    depth: u32,
    resume: ContractResumePolicy,
}

enum ContractResumePolicy {
    PreserveMatchingPath,
    ForeignOnly,
}
```

ここで `path` は解決済み `TypeDeclId` から得た effect family path である。型推論中に
文字列名を見て分岐しない。

`depth` は contract が有効になる関数呼び出し深さを表す。例えば、

```yu
f: _ -> [flip] _
```

の `flip` は、引数値 `f` 自体を渡す時点ではなく、`f` が一度呼ばれた計算で発生するため
depth `1` の marker になる。

## Lowering

注釈 lowering は `AnnType` を走査して contract marker を抽出する。

- root が `AnnType::Function` の parameter annotation だけを `ArgEffectContract` の対象にする。
- function layer の `arg_eff` / `ret_eff` に concrete effect head があれば、`depth + 1` で marker を作る。
- nested function / tuple / type application の中の function annotation も同じ規則で走査する。
- wildcard と row tail は marker にならない。

root の computation annotation:

```yu
action: [flip] _
```

は `ArgEffectContract` ではない。これは handler subtraction の静的 contract であり、
annotation constraint lowering と directed stack weight 側で扱う。

## Specialize

specialize は `ArgEffectContract` を読むだけで、mono 型の形から contract を推測しない。

関数境界で必要な runtime marker は二種類ある。

- actual / expected runtime shape の差分から必要になる ordinary hygiene marker
- source annotation 由来の explicit argument contract marker

後者は `ArgEffectContract` からだけ作る。同じ mono 型形状を持っていても、contract metadata が
なければ argument marker は作らない。

## Runtime Marker への変換

`ArgEffectContractMarker` は specialize の `hygiene` module 内で `mono::GuardMarker` へ変換する。

現行 runtime には `guard_own_path` / `guard_foreign_path` /
`preserve_own_on_resume` という boolean field が残っている。ただし、source contract 側の意味は
`ContractResumePolicy` に閉じ込める。後段へ「なんとなく own marker を立てる」という boolean を
渡さない。

現在使う policy は主に `PreserveMatchingPath` である。これは、contract された path と同じ
handler family に対して、resume 後も同じ matching-path guard を維持することを表す。

runtime では、`PreserveMatchingPath` 由来の marker が request を carry するとき、
marker entry 時点で既に見えていた matching handler id を exposed guard id として持たせる。
これにより、

- `choice(p: () -> [parse] ...)` のような明示契約つき callback は、その呼び出し地点を囲む
  `parse` handler に捕捉される。
- `choice` が捕捉しない `parse::item` / `parse::snapshot` などは、同じ contract の下で外側の
  `run_str` handler へ流れる。
- 明示契約を持たない ordinary own-path guard は、この exposed id を自動では得ない。

この差は重要である。ordinary callback hygiene では、同じ path の内側 handler が callback 由来の
effect を偶然捕捉してはならない。一方、source annotation で effect contract を書いた callback は、
その呼び出し地点で見えている matching handler に捕捉を許している。

## 不変量

- explicit contract は source annotation からだけ生まれる。
- specialize は contract を mono 型から復元しない。
- inferred effect row と explicit contract を混同しない。
- root computation annotation の subtraction contract と callback argument metadata を混同しない。
- runtime field 名に `own` が残っていても、source-level の設計概念としては matching path /
  non-matching path として読む。
- cache 内の `poly::Arena` 形状が変わったら `POLY_CACHE_FORMAT` を上げる。

## 関連ファイル

- `crates/poly/src/expr.rs`
- `crates/infer/src/lowering/expr/lambda.rs`
- `crates/specialize/src/hygiene.rs`
- `crates/specialize/src/specialize2/emit.rs`
- `crates/specialize/src/specialize2/runtime_shape.rs`
- `crates/yulang/src/cache.rs`
