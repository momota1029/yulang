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

2026-05-27 時点で完了:

- `CheckReport` / `CheckDiagnostic` / `DiagnosticCode` / `DiagnosticSpan` /
  `RelatedDiagnostic` を追加した。
- `collect_surface_diagnostics` は `CheckReport` 経由になった。
- `SurfaceDiagnostic` は互換 adapter として残しつつ、`code` / `severity` /
  primary `file_span` を落とさない。
- LSP diagnostics は `CheckReport` 由来の code を `diagnostic.code` に載せ、
  source を `yulang` として返す。
- LSP diagnostics は `SurfaceDiagnostic.related` を `relatedInformation` として返す。
- playground / wasm diagnostics は `code` と `related` を JSON payload に残す。
- 2026-07-03 に ambiguous role method の related candidate に
  `impl-candidate` origin を載せ、CLI contract / wasm playground payload で
  同じ構造化 origin を固定した。これはまだ specialization oracle bridge 由来だが、
  dedicated check-stage owner へ移す時も候補 impl の origin 名は維持する。
- 2026-07-03 に role/method unresolved / ambiguous 診断は check-stage owner へ移った。
  source 側は emission なしの `specialize::role_method_check` を読み、run 経路は従来どおり
  `SpecializeError::{UnresolvedTypeclassMethod, AmbiguousTypeclassMethod}` を返す非対称を維持する。

## 次の実装単位

`type.mismatch` を詳細化する。

- `TypeError` と `ExpectedEdge` の対応付けを `cause` / type vars / edge kind で選ぶ。
- `ExpectedEdgeKind::ApplicationArgument` は callee / parameter / argument の related を出す。
- `ExpectedEdgeKind::Annotation` は annotation と expression の related を出す。
- `ExpectedEdgeKind::IfBranch` は両 branch と expected join の related を出す。
- cast boundary で defer した constructor mismatch と、fatal にするべき mismatch を分ける。

2026-05-27 時点で一部完了:

- `TypeError` を `CheckDiagnostic` へ変換する入口は入った。
- `ExpectedEdgeKind::ApplicationArgument` / annotation 周辺の related 情報を
  `CheckReport` へ載せる regression を追加した。
- cast boundary で defer 可能な constructor mismatch は、既存の surface filtering を
  `CheckReport` 経由でも維持している。

確認する fixture:

- `1 + true`
- `my x: str = 1`
- `if true: 1 else: false`

2026-07-01 の public CLI golden first slice:

- `my x: int = true`
  - `check --no-prelude --no-cache`
  - `diagnostics: error: x: type mismatch: bool is not int`
  - `x: type mismatch: bool is not int`
- `my result = missing`
  - `check --no-prelude --no-cache`
  - `diagnostics: error: result: unresolved value name: missing`
  - `result: unresolved value name: missing`

この slice は型推論の意味を変えず、現在の CLI surface を固定する。
次の改善では、同じ原因を `CheckReport` 由来の source range / related information へ
接続し、CLI / LSP / playground の表示差分を縮める。

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
  - result effect type var

TODO:

- enum / error / effect operation の finite set を、名前文字列ではなく definition / symbol から引く。
- guard 付き arm は coverage に数えない。
- wildcard / binding pattern 以降の arm は unreachable 候補にする。
- `Unknown` を含む場合に「網羅済み」と誤判定しない。

2026-05-27 時点で `case` は一部完了:

- lowering 時に `CaseCheckSite` / `CaseArmCheckSite` を登録する。
- enum declaration / compiled artifact surface から有限 variant 集合を引く。
- unguarded enum variant arm だけを coverage に数え、guard 付き arm は related に回す。
- wildcard / binding arm 以降、重複 enum variant、完全な enum coverage 後の arm を
  `pattern.unreachable_arm` として報告する。
- `case` と arm の primary / related span は `FileSpan` を保持する。

2026-05-27 時点で `catch` は site / unreachable / shallow residual typing まで完了:

- lowering 時に `CatchCheckSite` / `CatchArmCheckSite` を登録する。
- source arm の span / guard span / value pattern span / effect operation pattern span /
  continuation span を `FileSpan` 付きで保持する。
- effect arm は operation path と、解決後の effect path を保持する。
- handler boundary 判定で runtime arm から外れる source arm も、`active` flag 付きで
  check site には残す。
- unguarded な value wildcard/binding arm 後の value arm と、同じ effect operation の
  unguarded payload-covering arm 後の effect arm は `pattern.unreachable_arm` として報告する。
- shallow catch / partial effect family の型は暫定実装。破綻は避けているが、
  期待している compact 表現にはまだ達していない。
- 目標は、scrutinee effect を `β`、handler residual tail を `γ` として
  `β <: [handled; γ]` を立て、catch result は基本 `γ`、continuation 起動の漏れや
  branch 不足のときだけ `β` が result に混ざる形。
- 現行実装には compact 表示や handled effect の型引数保持のための surface witness が残っている。
  これは最終仕様として扱わず、次の整理対象にする。

未着手:

- missing operation を user-facing diagnostic にする catch coverage。
- 複数 effect を含む catch coverage の diagnostic 集約。
- `Unknown` / `Never` を含む case coverage の明示的な保留 reason。

## role / impl 検査の準備

TODO:

- role declaration の required member と default body を check site へ残す。
- impl declaration の member span と body type / scheme を check site へ残す。
- missing / unknown member は role declaration と impl member を related にする。
- member 型 mismatch は solver の `ImplMember` constraint と同じ経路に乗せる。
- prerequisite missing / ambiguous は impl 本体の型不一致へ潰さない。

2026-05-27 時点で一部完了:

- source role method は `def_span` を記録する。
- missing required member の synthetic error は、required role member declaration を
  origin として保持し、`CheckReport.related` に出す。
- source role declaration は lowering 中に span を記録する。
- missing / unknown impl member の synthetic error は、role declaration を origin として
  保持し、`CheckReport.related` に出す。
- impl member type mismatch は lowering 中の check site と `ImplMember` cause を
  対応付け、role declaration と required role member declaration を related に出す。
- missing / ambiguous prerequisite は、失敗した source impl candidate の宣言 span を
  origin として保持し、`CheckReport.related` に出す。

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
