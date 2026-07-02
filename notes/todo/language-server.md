# Language Server TODO

目的: Yulang をエディタで触った時に、型・エラー・定義の位置が自然に見える状態にする。
LSP は compiler の別実装ではなく、parser / infer / diagnostics の構造化結果を薄く出す層として保つ。

## 公開後の優先

今は機能を増やすより、既に出している情報の信頼性を上げる。

1. diagnostics
   - compiler diagnostic の primary range をそのまま LSP range にする。
   - expected / actual の出自を `relatedInformation` に出す。
   - parser error、type error、role/method error を同じ diagnostic pipeline に載せる。
   - 空白・先頭コメント・未完成入力でも diagnostic が消えない regression を持つ。
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
- diagnostic hover は実装済み。type / catch / role-method の compact regression で、
  shared structured payload から hover を作る経路を固定している。
- detailed type checker の `CheckReport` を LSP diagnostics / hover の source of truth にする。
- hover type display は LSP payload size budget を持つ。残りは projection rule。
- method hover は role impl の内部型ではなく、呼び出し可能な関数型として出す。
- local variable hover が親束縛や古い scope の型を拾わないよう、span / scope table を source of truth にする。
- completion / goto definition は hover と同じ symbol resolution table から出す。
- token classification の regression は type name、function binding / call target、
  dot method、record literal field について LS / playground の共有 classifier を固定している。
  残りは resolved highlight ありの constructor / enum variant 共有 fixture。
- release binary の `yulang server` 起動は `scripts/release-smoke.sh` と hardening gate で見る。

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
