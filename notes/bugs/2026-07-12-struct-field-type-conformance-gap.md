# struct literal の field 型不一致が unresolved runtime boundary まで残る

日付: 2026-07-12。発見: Codex（role impl associated type の影響範囲調査中）。
状態: **open / type-soundness blocker**。associated type / function resultとは別の
constructor-argument and cast-resolution bug。

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

