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

