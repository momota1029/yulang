# Language Server TODO

目的: Yulang をエディタで触った時に、型・エラー・定義の位置が自然に見える状態にする。
LSP は compiler の別実装ではなく、parser / infer / diagnostics の構造化結果を薄く出す層として保つ。

## 公開後の優先

今は機能を増やすより、既に出している情報の信頼性を上げる。

1. diagnostics
   - compiler diagnostic の primary range をそのまま LSP range にする。
   - expected / actual の出自を `relatedInformation` に出す。
   - parser error、type error、role/method error を同じ diagnostic pipeline に載せる。
     2026-07-02 時点で role/method の unresolved / ambiguous は focused
     `SourceDiagnostic` regression に載った。残りは dedicated check-stage owner と
     parity fixture の拡張。
   - 空白・先頭コメント・未完成入力でも diagnostic が消えない regression を持つ。
     2026-07-03 に、先頭空行と `//` コメントの後にある type mismatch で primary
     range と related ranges が user source line に残る LSP/server canary を追加済み。
     同日に incomplete source `my x =` で parser diagnostic と lowering
     missing-body diagnostic が両方 LSP diagnostic list に残る canary も追加済み。
     missing-body 側は `yulang.missing-local-binding-body` code と hint を持つ。
2. hover
   - local binding、function parameter、method、effect operation の型を安定して出す。
   - diagnostic range 上では、エラーの短い説明と related information summary を出す。
     2026-07-02 時点で type mismatch と catch syntax diagnostic は実装済み。
   - internal evidence、handler_match、shift/peel、raw constraint noise は通常 hover に出さない。
   - `.list` などの method / role 経由の巨大型は、public projection か関数型の要約へ畳む。
3. editor integration
   - `yulang-editor` を LS と playground の共有 editor surface にする。
   - token classification は `tok-type` / `tok-function` / `tok-property` のような CSS class と
     LSP semantic token を同じ分類結果から出す。
   - playground 専用 highlighter と LS 用 token pass を分けない。
   - `cargo install yulang; yulang install std` 後に `yulang server` が動く状態を保つ。
   - Zed extension は公開前でも dev install で使えることを README から辿れるようにする。
   - std root が見つからない場合は、LSP diagnostic ではなく起動時の明確な status/error にする。

## 近い TODO

- `my a = 1 2` で diagnostic が LSP に出る regression を固定する。
  現状は `check` が通り、`run` の `yulang.not-callable` で落ちるため、
  check-stage owner 側の実装が先。
- diagnostic hover は実装済み。type / catch / role-method の compact regression で、
  shared structured payload から hover を作る経路を固定している。2026-07-03 に
  type mismatch の related range（型注釈側）でも同じ diagnostic summary を出す
  canary を追加した。
- detailed type checker の `CheckReport` を LSP diagnostics / hover の source of truth にする。
  role/method の focused bridge は実装済みなので、残りは check-stage owner への移管。
- hover type display は LSP payload size budget を持つ。残りは projection rule。
- method hover は resolved selection metadata の selected value type を使い、
  role impl の内部型ではなく呼び出し可能な関数型として出す。
- record field hover も resolved selection metadata の selected value type を使う。
  残りは effect operation hover と、巨大型の projection rule。
- local variable hover は shadowed lambda arg regression で、親束縛や古い scope の型を拾わないことを見る。
- completion / goto definition は hover と同じ symbol resolution table から出す。
- token classification の regression は type name、function binding / call target、
  dot method、record literal field について LS / playground の共有 classifier を固定している。
  残りは resolved highlight ありの constructor / enum variant 共有 fixture。
- release binary の `yulang server` 起動は `scripts/release-smoke.sh` と hardening gate で見る。

## 探索 follow-up（未着手）

- doc-comment hover の Markdown 生成を、現在の CST walk による static renderer
  (`crates/infer/src/doc_comment_render.rs`) から、hover request ごとに必要な一件だけを
  lazy に Yumark 評価する経路へ置き換える、または補完する。手で重複実装された static
  renderer の代わりに、本番化済みの algebra-passing `std::text::yumark` API を再利用する。
- 2026-07-18 の計測では、doc-comment 規模（約 5 operation）の小さい Yumark literal を、
  playground と同じ warm-worker / resident-std 設計
  (`crates/wasm/src/lib.rs`, `crates/yulang/src/source/std_sources.rs`) で warm-resident incremental
  evaluation した時の median は約 33–37ms だった。単一 hover の lazy 評価なら hover latency
  budget 内に入り得る。一方、file 内の全 doc comment を先に評価する eager bulk replacement は
  線形に増え、数十件を超えると遅くなるため、この数値はその設計を正当化しない。
- 実装前に必要だが、まだ存在しないもの:
  - evidence-vm には、whole-program run の外で checked sub-expression 一件だけを評価する
    isolated-expression-eval API がない。
  - raw-value-extraction API がなく、現在の rendering output は formatted text だけである。
  - doc comment ごとの content-hash memoization / invalidation 機構がない。
  - 既存の warm-residency API は「std を再利用し、fresh root 一件を compile + specialize + run」
    する経路だけを持つ。open file や以前の doc snippet の compilation state を incremental に
    再利用する API はない。
- 背景は `../design/2026-07-08-yumark-value-model-tagless-final.md` の
  `LS doc-comment display` 節を参照する。この TODO は、そこでの元の infeasibility finding のうち
  数値的 feasibility の結論を更新するが、同節が挙げた API prerequisite はまだ解決しない。
- これは active task ではなく、未着手の探索 follow-up として保留する。

## やらないこと

- LSP 側で CST を再走査して型や span を推測しない。
- compiler diagnostic の文字列を parse して related information を作らない。
- std path や関数名の文字列一致で hover 表示を特別扱いしない。
- playground 専用の表示規則を LSP にだけ入れない。
- LS と playground の token 分類を別々に実装しない。

## 参照

- diagnostics: `diagnostics-docs.md`
- detailed type checker: `type-checker-diagnostics.md`, `../diagnostics/type-checker-plan.md`
- public install flow: `../../README.md`
- LSP implementation: `../../crates/yulang/src/server.rs`
