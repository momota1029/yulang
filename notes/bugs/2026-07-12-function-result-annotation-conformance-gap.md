# 関数戻り値 annotation が nominal な不一致を拒否しない

日付: 2026-07-12。発見: Codex（role impl associated type の影響範囲調査中）。
状態: **open / type-soundness blocker**。generic role impl conformance とは別の integration bug。

## 症状

関数 header の戻り値 annotation と body の concrete 型が異なっても `check` が通る。

```yu
my f(): bool = 42
f()
```

```bash
target/debug/yulang --no-prelude --no-cache check /tmp/function-result.yu
target/debug/yulang --no-prelude --no-cache run --evidence-vm --print-roots \
  /tmp/function-result.yu
```

観測結果:

```text
lowering errors: 0
run roots [42]
```

caller が宣言を信じて bool pattern で消費すると、int value はどの arm にも一致しない。

```yu
case f():
    true -> 1
    false -> 0
```

```text
runtime error [yulang.pattern-mismatch]: no pattern matched the value
```

## 根本原因

関数 body の lowering 自体は annotation を無視していない。
`lower_defined_lambda_params` は最終 body を
`connect_type_method_result_annotation`へ渡し、`AnnConstraintLowerer::connect_computation_detailed`
が body value と annotation の expected edge を接続する。

欠落は二段ある。

1. `check_result_annotation_type` は
   `compact_type_matches_signature_shape`だけを呼ぶ。`int` と `bool` はどちらも nominal
   constructor shape なので、この時点で区別されない。
2. generalization 後の`deferred_result_annotation_errors`も
   `poly_pos_matches_signature`を使うが、expected がBuiltin / Named / Applyの場合は
   actual が任意の`Pos::Con`ならtrueとする。path、builtin identity、type argumentを比較しない。

constraint machine は`int <: bool`から`NominalCastNeeded`を生成するが、
`AnalysisSession::constrain_nominal_cast`は該当cast candidateが0件でもdiagnosticを出さずreturnする。
結果として、二つのdiagnostic gateとmissing-cast gateのすべてを抜ける。

## 実害

- `check`が宣言型`bool`の関数を受理し、evidence-vmは実値`Int(42)`を返す。
- bool pattern、bool primitive、boundary consumerで実行時errorになる。
- evidence-vmの値は`RuntimeEvidenceValue::Int` / `Bool`というtagged enumなので、確認した
  経路ではmemory reinterpretationではなくstructured errorになる。
- API callerは公開signatureを信頼できず、型検査とruntime結果が食い違う。

## 境界

- 単純な値binding `my x: bool = 1` は`check_binding_annotation_type`のbuiltin mismatch
  checkで正しく拒否される。
- 本件はheader argsを持つ関数・methodのdeferred result annotation経路にある。
- role method requirementには別の`compact_type_matches_signature` checkがあり、同じ関数を
  そのまま直せばよいとは限らない。
- generic role impl conformance用のalpha-aware subsumption kernelを再利用できる可能性はあるが、
  binder ownershipとintegration時点は別途設計する必要がある。

## 関連

- `crates/infer/src/lowering/expr/lambda.rs`
- `crates/infer/src/lowering/expr/method_body.rs`
- `crates/infer/src/lowering/body/mod.rs`
- `crates/infer/src/lowering/signature_match.rs`
- `crates/infer/src/analysis/session/generalize.rs`
- `crates/evidence-vm/src/runtime.rs`


## 追記 2026-07-25: SOUND-A による範囲の精密化

型健全性トラックの第1スライス（SOUND-A、特性化）で、本件の範囲がより正確になった。
実機（release binary）で確認した現状は次の通り。

| 形 | 現状 |
|---|---|
| `my f: bool = 42` | 拒否される（`yulang.type-mismatch: int is not bool`） |
| `my f(): bool = 42` | **受理される（穴）** |
| `struct s { .. } with: our x.m: bool = 42` | **受理される（穴）** |
| `struct s { .. } with: our x.m(): bool = 42` | **受理される（穴）** |
| role impl の associated type 不一致 | 拒否される（2026-07-21 に修正済み） |

### 重要: companion method は素の関数とは別の欠陥である

当初は「同じ不完全な provenance を共有する一つの穴」と見ていたが、特性化の結果、
両者は異なる。

- **素の関数**（`my f(): bool = 42`）:
  `body.value <: bool` の subtype 制約は生成されており、`Return` 所有の root を持つ。
  `NominalCastNeeded` を発火し、OCAST 分類器まで到達する。分類が
  `Incomplete(UnknownOrigin)` になるため、CPROV-J の fail-open で素通りする。
  すなわち **provenance の不完全さ**が原因である。

- **companion method**（`with:` ブロック内）:
  `lower_type_method_binding` が `lower_type_method_body_expr` へ result type として
  `None` を渡し、後続の `defer_result_annotation_check` は形の検査だけを記録して
  subtype 制約を生成しない。結果として nominal producer は 0 本、分類器の shadow は空。
  すなわち **制約そのものが存在しない**。

したがって、素の関数側の provenance を補完しても companion method は直らない。
両者には別々の修復が必要である。

形の検査自体は動作していることも確認した。構造が違う注釈は拒否される。

```console
$ # our x.m: bool = \y -> y
error [yulang.invalid-signature]: s.m: signature type mismatch: expected a type constructor
```

通るのは「構造は一致するが nominal 型が違う」場合に限られる。

### 経緯についての注記

SOUND-A の最初の実装は、role impl のメソッド（既に健全）を "receiver-method" として
特性化し、companion method を取りこぼしていた。レビュー時に実機で確認して発覚した。
`sound_a_role_impl_associated_type_result_pins_...` は名前が示す通り既に閉じた経路の
特性化であり、companion method の特性化とは別物である。
