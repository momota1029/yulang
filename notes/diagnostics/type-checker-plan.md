# Detailed Type Checker Plan

作成日: 2026-05-27

## 目的

詳細な型チェッカーは、既存の Simple-sub 推論器を置き換えるものではない。
推論器が作った型、制約、expected edge、origin、role / impl 情報を読み、
ユーザーが直せる structured diagnostic へまとめる層として置く。

最終的な利用先は CLI、LSP、playground である。表示文言や markdown は各 frontend
で作ってよいが、primary range、related information、diagnostic code、型の出自は
同じ `CheckReport` から読む。

扱う診断:

- Simple-sub の型不一致を、expected / actual とその出自付きで報告する。
- `case` / `catch` の枝不足、到達しない枝、guard 付き枝だけでは覆えない入力を報告する。
- role / type class 相当の impl が required member、member 型、prerequisite を満たさないことを報告する。
- missing / ambiguous impl、missing method、effect / handler mismatch を同じ diagnostic pipeline に載せる。
- runtime lowering / monomorphize 側の residual type は、通常の user path で内部エラーとして漏らさない。

## 非目的

- 型システムの意味を変えない。
- LSP / playground 側に別の型チェッカーを作らない。
- CST を後段で再走査して span や型を推測しない。
- `Any` を未解決型や fallback として使わない。
- path、module、fixture、関数名の文字列一致で型を決めない。
- solver の hot path に表示用文字列生成を混ぜない。

`Any` は Top、`Never` は Bottom、`Unknown` は唯一の不明型である。
診断できない状態は `Unknown` / unresolved obligation として残し、`Any` に逃がさない。

## 全体構成

目標の流れ:

```text
source / syntax
  -> lowering
       - type origins
       - expected edges
       - check sites
       - role / impl facts
  -> Simple-sub solver
       - type errors
       - bounds / compact results
       - selection / role obligations
  -> checker passes
       - type mismatch explanation
       - exhaustiveness
       - role impl conformance
       - effect / handler obligations
  -> CheckReport
  -> CLI / LSP / playground renderers
```

候補 module:

- `crates/yulang-infer/src/check/mod.rs`
  - public entrypoint: `check_lowered(state: &LowerState) -> CheckReport`
- `crates/yulang-infer/src/check/report.rs`
  - `CheckReport`, `CheckDiagnostic`, `DiagnosticCode`, `DiagnosticSpan`
- `crates/yulang-infer/src/check/type_mismatch.rs`
  - Simple-sub の `TypeError` と expected edge / origin の対応付け
- `crates/yulang-infer/src/check/exhaustiveness.rs`
  - `case` / `catch` の coverage
- `crates/yulang-infer/src/check/roles.rs`
  - role impl conformance と obligation diagnostics
- `crates/yulang-infer/src/check/effects.rs`
  - catch residual / unhandled effect diagnostics

移行中は既存の `surface_diagnostic.rs` を adapter として残し、`CheckReport` から
`SurfaceDiagnostic` へ落とす。CLI / LSP が直接文字列だけを読む期間を短くする。

## Report 形式

最小形:

```text
CheckReport {
  diagnostics: Vec<CheckDiagnostic>,
}

CheckDiagnostic {
  code: DiagnosticCode,
  severity: Error | Warning | Info,
  primary: Option<DiagnosticSpan>,
  summary: DiagnosticSummary,
  related: Vec<RelatedDiagnostic>,
  notes: Vec<DiagnosticNote>,
  machine: DiagnosticPayload,
}
```

`summary` は user-facing message を作るための材料で、solver / checker の中心処理では
長い表示文言を作らない。LSP / playground では `machine` を使って hover や
related information を組み立てる。

`DiagnosticCode` は最初は文字列 ID でよい。

- `type.mismatch`
- `type.expected_shape`
- `type.record.missing_field`
- `pattern.non_exhaustive`
- `pattern.unreachable_arm`
- `effect.unhandled`
- `effect.catch_non_exhaustive`
- `role.impl.missing`
- `role.impl.ambiguous`
- `role.impl.missing_member`
- `role.impl.unknown_member`
- `role.impl.member_type_mismatch`
- `role.impl.missing_prerequisite`
- `runtime.residual_type`

番号付き code は public docs と test fixture が増えてから固定する。

## Simple-sub 詳細診断

既にある材料:

- `TypeError { cause, kind, pos, neg, origins }`
- `ConstraintCause { span, reason }`
- `TypeOrigin { span, file_span, kind, label }`
- `ExpectedEdge`
- `ExpectedAdapterEdge`
- typed IR 側の `ExpectedEdgeEvidence`

追加したい材料:

- `TypeError` から関連する `ExpectedEdgeId` / derived edge を引ける索引。
- value type と effect type を分けた expected / actual provenance。
- function parameter、function return、record field、variant payload などの派生 edge path。
- annotation / binding / method signature / impl member declaration の file span。

診断の責務:

- primary span は、ユーザーが直す値、枝、注釈、impl member の位置へ置く。
- related span は、expected を作った注釈、関数 parameter、role method signature、
  actual を作った literal / binding / expression へ張る。
- 型表示は public projection を使い、raw type variable、internal evidence、
  handler adapter の内部名を通常表示へ漏らさない。
- `MissingImpl` / `AmbiguousImpl` は cast boundary の false positive と一緒に握りつぶさない。

最初の縦切り:

1. 現在の `collect_surface_diagnostics` と同じ出力を `CheckReport` 経由にする。
2. `ConstructorMismatch` で、best `ExpectedEdge` を選び、expected / actual の related を出す。
3. `1 + true`、annotation mismatch、if branch mismatch を小さい regression にする。
4. runtime lowering の `TypeMismatch` が出る ordinary path を、可能な限り infer 側の
   `type.mismatch` へ寄せる。

## `case` の網羅性

`case` は lower 時に check site を登録する。

候補形:

```text
CaseCheckSite {
  id,
  scrutinee_tv,
  scrutinee_span,
  arms: Vec<PatternArmSite>,
  result_tv,
}

PatternArmSite {
  pattern_id,
  pattern_span,
  guard_span,
  is_unconditional,
}
```

checker は solver 後に scrutinee の public shape を読む。

- enum / variant set が有限に分かる場合、未カバー variant を出す。
- tuple / record / literal pattern は、既存 pattern checker が持つ構造情報から coverage を作る。
- guard 付き arm は coverage には数えない。guard がある枝は「条件が偽なら通過する」扱いにする。
- wildcard / binding pattern は、それ以降の未カバー集合を空にする。
- scrutinee が `Unknown` を含む場合、網羅性 OK とはしない。未解決型の診断か保留 reason を出す。
- `Never` scrutinee は reachable input がないため missing branch としない。

禁止:

- `case` 本文の CST を後から再走査して arm を復元しない。
- variant 名の文字列一致だけで enum を決めない。
- fixture 名、module 名、std path に依存して coverage を変えない。

## `catch` の網羅性

`catch` は value branch と effect branch の両方を扱うため、`case` とは別 site にする。

候補形:

```text
CatchCheckSite {
  id,
  body_effect_tv,
  body_span,
  arms: Vec<CatchArmSite>,
  result_tv,
  residual_effect_tv,
}

CatchArmSite {
  effect_path_or_id,
  payload_pattern_span,
  continuation_span,
  guard_span,
  is_value_arm,
}
```

checker の方針:

- body effect row が閉じている場合、未処理 operation を `effect.catch_non_exhaustive` として出す。
- open row / `Unknown` を含む場合、網羅済みとは扱わず、未解決 effect row の related を出す。
- value arm が必要な構文なら、value arm 不足を catch site で報告する。
- resume / continuation の引数型 mismatch は、`type.mismatch` として `CatchBranch` /
  `ResumeArgument` の expected edge へ接続する。
- handler residual は diagnostics で説明し、runtime lowering で内部 trap として初めて見えないようにする。

## role / type class impl 検査

Yulang の role / impl は type class 相当の診断対象として扱う。
実装は role 名の文字列ではなく、lowering 済みの role / method / impl fact から検査する。

既にある材料:

- `RoleMethodInfo`
- `RoleImplCandidate`
- `TypeErrorKind::MissingImpl`
- `TypeErrorKind::AmbiguousImpl`
- `TypeErrorKind::MissingImplMember`
- `TypeErrorKind::UnknownImplMember`
- prerequisite 系の `TypeErrorKind`

追加したい check site:

```text
RoleImplCheckSite {
  impl_def,
  impl_span,
  role,
  args,
  member_defs,
  required_members,
  prerequisites,
}

RoleMemberCheckSite {
  method_def,
  member_def,
  declared_scheme,
  implemented_scheme_or_body_type,
  cause,
}
```

checker の責務:

- required member がない場合、role declaration と impl declaration を related に出す。
- unknown member がある場合、その member と role declaration を related に出す。
- member 型が role method scheme を満たさない場合、通常の `ImplMember` constraint として
  Simple-sub の `type.mismatch` に載せる。
- prerequisite が missing / ambiguous の場合、impl site と prerequisite declaration を related に出す。
- default body がある member は、missing としない。ただし default body 自体の型不一致は別診断にする。

テスト観点:

- role / method の名前を変えても、解決先が同じなら同じ診断になる。
- module path を変えても、同じ role / impl graph なら同じ診断になる。
- missing member と member type mismatch を別 code で出す。
- prerequisite missing / ambiguous を impl 本体の型不一致に潰さない。

## LS / playground 連携

LSP は compiler の別実装ではない。`CheckReport` を薄く変換する。

LSP:

- `CheckDiagnostic.primary` を `Diagnostic.range` にする。
- `code` を LSP diagnostic code に入れる。
- `related` を `relatedInformation` に入れる。
- diagnostic range 上の hover は、同じ diagnostic payload から短い markdown summary を出す。
- hover の型表示は public projection と size budget を通す。

Playground:

- CLI と同じ `CheckReport` を JSON payload にする。
- display string は playground 側で作ってよいが、code / range / related は共有する。
- blank / missing diagnostic regression は `CheckReport` の fixture で追う。

CLI:

- 既存の code frame を `CheckDiagnostic` から作る。
- 普通の user path では runtime lowering / monomorphize の内部 stage 名を出さない。

## 実装フェーズ

### Phase 0: 現状 inventory

- `TypeErrorKind` ごとの current primary range と related 情報を表にする。
- `ExpectedEdge` / `ExpectedAdapterEdge` がどの lower site で作られているか列挙する。
- role impl member の span と scheme をどこで持てるか確認する。
- `case` / `catch` の pattern arm 情報を lower 時にどこで登録できるか確認する。

### Phase 1: `CheckReport` adapter

- `CheckReport` / `CheckDiagnostic` / `DiagnosticCode` を足す。
- 既存 `collect_surface_diagnostics` を `CheckReport` から作る adapter に寄せる。
- 出力差分が出ない regression を入れる。
- LSP はまだ `SurfaceDiagnostic` 経由でよい。

### Phase 2: Simple-sub mismatch provenance

- `TypeError` と best `ExpectedEdge` の対応付けを作る。
- expected / actual の related span を増やす。
- annotation、application argument、if branch、record field を優先して対応する。
- false-positive cast boundary defer と fatal diagnostic の境界を code で見えるようにする。

### Phase 3: role impl conformance

- `RoleImplCheckSite` を作る。
- missing / unknown member を structured diagnostic 化する。
- member 型 mismatch を `ImplMember` cause の `type.mismatch` として出す。
- prerequisite missing / ambiguous の related を増やす。

### Phase 4: `case` / `catch` exhaustiveness

- `CaseCheckSite` と `CatchCheckSite` を lower 時に登録する。
- solver 後に finite shape / effect row から missing branch を計算する。
- guard 付き arm、wildcard、`Never`、`Unknown` の扱いを固定する。
- small fixture で enum case、error catch、open effect row を分けて確認する。

### Phase 5: LSP / playground

- LSP diagnostics を `CheckReport` 直読みにする。
- diagnostic hover を追加する。
- playground payload を shared report にする。
- blank / incomplete source でも diagnostic が消えない regression を入れる。

### Phase 6: docs / examples

- README / docs/status には user-facing な diagnostic 例だけを載せる。
- design note は internal として残し、古い実装状態と混ざらないようにする。
- example は大きな demo ではなく、診断理由が読める小さいものを使う。

## 性能方針

- check site は lowering 中に登録し、checker は `LowerState` / solver tables を一度読む。
- diagnostic の表示文字列は最後に遅延生成する。
- 型 pretty print は budget を持ち、巨大 role / effect evidence を通常表示へ漏らさない。
- `case` / `catch` coverage は有限集合が分かる場合だけ集合演算する。
- open row / `Unknown` を無理に閉じるための再推論を checker に入れない。
- LSP のファイル更新ごとに同じ std / dependency facts を再構築しない方針は
  static-analysis cache と揃える。

## テスト方針

- `crates/yulang-infer` の unit test で check site と report を直接見る。
- CLI 表示の snapshot は、文言を固定したい代表例だけに絞る。
- LSP は range、code、relatedInformation の regression を見る。
- Playground は blank / missing diagnostic と JSON payload shape を見る。
- 名前変更、module 移動、fixture 名変更に強いテストを入れる。
- `Any` fallback が入っていないことを、未解決型の negative test で確認する。

代表 fixture:

- `1 + true`
- `my x: str = 1`
- `if cond: 1 else: false`
- enum の `case` で 1 variant 足りない
- guard 付き arm だけでは coverage にならない `case`
- error / effect の `catch` で operation が足りない
- role impl missing member
- role impl unknown member
- role impl member type mismatch
- prerequisite missing / ambiguous impl

## 未決定事項

- missing `case` / `catch` branch を常に error にするか、実験中は warning を許すか。
- open effect row の網羅性を「未解決型診断」とするか、「網羅性を判定できない」note にするか。
- diagnostic code をいつ番号付き public code に固定するか。
- runtime residual type の一部を type checker 側へ吸い上げる境界をどこに置くか。
- role method signature の public projection をどの表示規則で畳むか。
