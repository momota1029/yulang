# struct literal の field 型不一致が unresolved runtime boundary まで残る

日付: 2026-07-12。発見: Codex（role impl associated type の影響範囲調査中）。
状態: **解決済み（2026-07-25）**。`812bb5a6`。下記「解決」を参照。

## 症状

nominal struct fieldの宣言型とliteralの値型が異なっても`check`が通る。

```yu
struct S { x: bool }
S { x: 42 }
```

```bash
target/debug/yulang --no-prelude --no-cache check /tmp/struct-field.yu
target/debug/yulang --no-prelude --no-cache run --evidence-vm --print-roots \
  /tmp/struct-field.yu
```

観測結果:

```text
lowering errors: 0
runtime error [yulang.unsupported-runtime-feature]:
  unsupported expression in runtime: runtime boundary
```

## 根本原因

field signatureのconstraint生成そのものは存在する。

1. `lower_constructor_type`がstruct constructorのrecord payloadを作る。
2. `connect_constructor_arg_signatures`がfield variableから宣言型のnegative signatureへ
   subtype edgeを張る。ここでは`x <: bool`になる。
3. `lower_record_literal`はliteral側をanonymous record `{x: int}`としてlowerする。
4. constructor applicationとrecord invariant propagationにより`int <: bool`が生成される。

抜けているのは「direct castが存在しない」という否定結果の扱い。

- infer側の`AnalysisSession::constrain_nominal_cast`はcast candidatesが空なら何もせずreturnする。
- specialize2側の`TypeGraph::constrain_direct_cast`もcandidateが空でも`Ok(())`を返す。
- emitはactual / expectedが異なるままならcast instance無しの`ExprKind::Coerce`を生成する。
- evidence-vmはこのbare coerceを実装済み変換として扱えず`runtime boundary`で停止する。

missing required fieldはspecialize2に専用`UnsatisfiedSubtypeOrigin::MissingRecordField`があるが、
存在するfieldのvalue mismatchには対応するearly diagnosticがない。

## 実害

- nominal constructor contractに違反した値を`check`が受理する。
- errorはfield `x`の宣言位置・literal位置ではなくruntime boundaryまで遅れる。
- cast宣言が無い不一致と、将来runtimeで扱えるcoercionの区別が失われる。
- evidence-vmではstructured unsupported errorで止まり、確認した範囲でmemory unsafetyはない。

## 境界

- anonymous recordのwidth subtypingやextra field問題とは別。ここでは宣言済みfieldが存在し、
  そのvalue型だけが不一致である。
- constructor signature、record propagation、specialize expected-field伝播は存在するため、
  field annotationが完全に無視されているわけではない。
- 修正責務はgeneric role impl conformanceではなく、nominal expected edgeでcast candidateが無い時の
  compile-time rejectionとdiagnostic provenanceにある。
- alpha-aware structural type relationの一部は共有できても、runtime cast lookupとの統合は別sliceが必要。

## 関連

- `crates/infer/src/lowering/body/type_decl.rs`
- `crates/infer/src/lowering/constructor.rs`
- `crates/infer/src/lowering/record_lit.rs`
- `crates/infer/src/analysis/session/generalize.rs`
- `crates/specialize/src/specialize2/type_graph.rs`
- `crates/specialize/src/specialize2/emit.rs`
- `crates/evidence-vm/src/runtime.rs`


## 解決 2026-07-25

`812bb5a6` で閉じた。3 つの型健全性の穴のうち最後の 1 件である。

### 原因と修復

expected field edge は `connect_constructor_arg_signatures` で生成されていたが、その root が
`unknown_internal()` のままで、分類が `Incomplete(UnknownOrigin)` に落ちて fail-open されていた。

constructor / record literal の root 5 箇所を `Internal` へ付け替えた。

- `body/type_decl.rs`: constructor predicate → registered root
- `constructor.rs` の `constrain_constructor_arg_shapes`: record lower → constructor argument
- 同上: constructor argument → record upper
- `constructor.rs` の `connect_constructor_arg_signatures`: record field value → declared field signature
- `record_lit.rs`: literal result value → record lower

独立した source boundary は追加していない。tuple / value constructor signature root は
`UnknownInternal` のまま残す。これにより literal 使用側の `ApplicationArgument` 境界が唯一の
source owner となり、分類は `EligibleSourceBoundary(ApplicationArgument)` になる。

事前分析が警告していた `InternalOnly` への誤分類（宣言側を独立した source boundary にすると
source 義務が二つに分裂して起こる）は発生していないことを確認済み。

### 露出したランタイムの欠落と同時対処

結果注釈のときと同じく、義務を課すと未到達だったランタイム経路が露出した。
`struct t { x: float }` に `t { x: 1 }` を渡すと、field ごとの cast は正しく挿入される
（`m2 1`）が、その外側に冗長な record 全体の adapter が残り、両バックエンドで停止していた。

同じスライス内で対処した。record adapter を外すのは次を**すべて**満たす場合に限る。

- spread が無い
- field 集合が一致する
- 全 field が boundary 等価であるか、直接 cast を持つ
- raw / emitted の引数型と constructor 戻り型が一致する

1 つでも変換が adapter 任せなら adapter を残す。無条件に外すと必要な変換を黙って飛ばし、
値が壊れる。

### 測定

- `struct t { x: bool }; t { x: 42 }` → 拒否
- `(t { x: 1 }).x + 0.5` → 両バックエンドで `1.5`（変換が実際に起きている証拠）
- 型が一致する literal → `run roots [t({x: false})]`
- 先行スライスの非後退: 関数・companion method のピンは拒否のまま、`my g(): float = 1` も動作
- infer 958 / specialize 146 / yulang 365 / contract 229
- 既知の偽陽性対照 3 件は `InternalOnly` を維持、signature-privacy canary 2 件も通過
- poly dump hash・check-report hash・structural / row counts・制約総数はいずれも不変

### 経緯

先行スライスで「穴を塞いだらランタイムの欠落が露出した」経験があったため、本スライスでは
最初から `struct t { x: float }` の実行確認を検証項目に入れた。結果として同種の欠落を
着地前に発見できた。
