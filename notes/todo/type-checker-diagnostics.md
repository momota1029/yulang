# Detailed Type Checker Diagnostics TODO

目的: Simple-sub、`case` / `catch`、role / impl 検査の失敗を、CLI / LSP /
playground で同じ構造化診断として扱えるようにする。

設計本体:

- `../diagnostics/type-checker-plan.md`

## 直近の進め方

1. `CheckReport` の薄い adapter を作る。
   - 既存の `collect_surface_diagnostics` と同じ内容を返す。
   - 先に出力差分を出さず、後続の詳細化を小さくする。
2. Simple-sub 型不一致の provenance を増やす。
   - `TypeError` と best `ExpectedEdge` を対応付ける。
   - expected / actual の related span を出す。
   - annotation、application argument、if branch を最初の対象にする。
3. role impl diagnostics を構造化する。
   - missing member / unknown member / prerequisite missing を `CheckDiagnostic` にする。
   - member 型 mismatch は `ImplMember` cause の `type.mismatch` として扱う。
4. `case` / `catch` check site を lower 時に登録する。
   - 後段で CST を再走査しない。
   - guard 付き arm、wildcard、`Unknown`、`Never` の扱いを固定する。
5. LSP / playground を `CheckReport` 直読みに寄せる。
   - LSP `relatedInformation` と diagnostic hover を同じ payload から作る。
   - playground は JSON payload と code / range / related を共有する。

## 最初の実装単位

最初の PR / commit では挙動を変えず、構造だけを足す。

- `crates/yulang-infer/src/check/report.rs`
  - `CheckReport`
  - `CheckDiagnostic`
  - `DiagnosticCode`
  - `DiagnosticSpan`
  - `RelatedDiagnostic`
- `crates/yulang-infer/src/check/mod.rs`
  - `pub fn check_lowered(state: &LowerState) -> CheckReport`
- `crates/yulang-infer/src/surface_diagnostic.rs`
  - `CheckReport` から `SurfaceDiagnostic` へ変換する adapter を持つ。
- tests
  - current surface diagnostics の代表例が同じ message / span を返すことを見る。

この段階では型システム、solver、lowering の意味を変えない。

## 次の実装単位

`type.mismatch` を詳細化する。

- `TypeError` と `ExpectedEdge` の対応付けを `cause` / type vars / edge kind で選ぶ。
- `ExpectedEdgeKind::ApplicationArgument` は callee / parameter / argument の related を出す。
- `ExpectedEdgeKind::Annotation` は annotation と expression の related を出す。
- `ExpectedEdgeKind::IfBranch` は両 branch と expected join の related を出す。
- cast boundary で defer した constructor mismatch と、fatal にするべき mismatch を分ける。

確認する fixture:

- `1 + true`
- `my x: str = 1`
- `if true: 1 else: false`

## `case` / `catch` の準備

lowering で登録する site の候補:

- `CaseCheckSite`
  - scrutinee type var
  - scrutinee span
  - pattern arm spans
  - guard spans
  - result type var
- `CatchCheckSite`
  - body effect type var
  - catch body span
  - handled operation ids
  - value arm / effect arm spans
  - residual effect type var

TODO:

- enum / error / effect operation の finite set を、名前文字列ではなく definition / symbol から引く。
- guard 付き arm は coverage に数えない。
- wildcard / binding pattern 以降の arm は unreachable 候補にする。
- `Unknown` を含む場合に「網羅済み」と誤判定しない。

## role / impl 検査の準備

TODO:

- role declaration の required member と default body を check site へ残す。
- impl declaration の member span と body type / scheme を check site へ残す。
- missing / unknown member は role declaration と impl member を related にする。
- member 型 mismatch は solver の `ImplMember` constraint と同じ経路に乗せる。
- prerequisite missing / ambiguous は impl 本体の型不一致へ潰さない。

## 完了条件

- CLI、LSP、playground が同じ diagnostic code / range / related 情報を読める。
- Simple-sub の代表的な型不一致で expected / actual の出自が見える。
- `case` / `catch` の枝不足が、有限集合を根拠に診断される。
- role impl の missing / unknown / type mismatch / prerequisite failure が分かれて出る。
- checker が CST 再走査や path 文字列分岐に依存しない。
- 未解決型を `Any` fallback で隠していない。

## 参照

- `diagnostics-docs.md`
- `language-server.md`
- `static-analysis-speed.md`
- `../../crates/yulang-infer/src/diagnostic.rs`
- `../../crates/yulang-infer/src/surface_diagnostic.rs`
- `../../crates/yulang-infer/src/lower/state.rs`
- `../../crates/yulang-infer/src/solve/constrain.rs`
