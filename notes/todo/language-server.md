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
- hover type display の LSP payload size budget / large-type projection rule は実装済み
  （`64980b9d`, `a1e55e27`, `6f6c825a`）。
  `hover_entry_source_large_record_type_is_structurally_truncated` と
  `lsp_hover_for_source_hover_limits_large_payloads` で固定している。
- method hover は resolved selection metadata の selected value type を使い、
  role impl の内部型ではなく呼び出し可能な関数型として出す。
- record field hover も resolved selection metadata の selected value type を使う。
  effect operation hover も実装済みで、宣言・参照の範囲と public callable type は
  `hover_entry_source_reports_effect_operation_decl_type` /
  `hover_entry_source_reports_effect_operation_ref_type`、LSP range と fenced signature は
  `hover_for_source_reports_effect_operation_at_reference` で固定している。
- local variable hover は shadowed lambda arg regression で、親束縛や古い scope の型を拾わないことを見る。
- goto definition は hover と同じ、解決済み occurrence の symbol resolution table から出す。
  completion はその table だけでは names-in-scope / members-of-type を列挙できないため、
  別の enumeration accessor と member probe を使う（下記「completion」参照）。
- token classification の regression は type name、function binding / call target、
  dot method、record literal field について LS / playground の共有 classifier を固定している。
  残りは resolved highlight ありの constructor / enum variant 共有 fixture。
- release binary の `yulang server` 起動は `scripts/release-smoke.sh` と hardening gate で見る。

## completion（実装済み）

`38abb196`, `7f3f2971`, `3c44ab69`, `33537bf6`, `722fea5d` で、LSP completion の
end-to-end surface と、型情報を使わない候補、member 候補、local 候補まで実装済み。

### 現在の surface

- completion capability を登録済みで、`.` を trigger character として登録している。
- non-member context では次を返す。
  - export 済みの canonical list `parser::scan::KEYWORDS` にある keyword。
  - focused module に直接宣言された module-level value。
  - named import と glob import で入った value。re-export された glob value も含む。
  - cursor 位置で scope 内にある local binding。`my` binding、function parameter、
    lambda argument、`for` binder、case / catch の pattern binder を含む。
- member context（`x.` / `x.partial`）では、record field、nominal type method、
  reference-payload method、到達可能な effect operation を返す。この context では
  member 候補が keyword / global 候補を置き換える。
- detail text はすべて debug dump ではなく public type formatter を使う。
  `../design/2026-07-03-hover-public-type-projection.md` と同じ public projection 契約に従う。
- keyword 候補は analysis より前に作る。analysis failure、invalid position、timeout、
  worker slot 枯渇時も keyword-only へ degrade する。member context の失敗時は、
  dot の後に keyword を出さないため empty list を返す。

### member probe と enumeration

- bare `x.` は `scan_dot_field` が `.` と identifier の両方を要求するため、
  `Expr "x"` と detached `InvalidToken` になり、`SelectId`、selection span、
  receiver `TypeVar` のいずれも生成されない。
- completion 時は cursor にある partial member name を sentinel
  `yulang__completion__probe` へ置き換えた probe buffer を合成し、その buffer を analysis
  して得た selection から receiver type を読む。この処理は LSP adapter ではなく
  `crates/yulang/src/source/mod.rs` にあり、unit test 可能で、将来 wasm からも再利用できる。
- `crates/infer/` には additive な read accessor として、receiver `TypeVar` からの
  record-field 列挙、receiver-indexed の nominal / reference method 列挙、read-only の
  reachable-effect traversal を追加した。local binding の scope extent も
  `LocalDefUseTable` に additive に記録する。既存の resolution semantics は変更していない。

### 既知の残件

1. attached-role method は候補に含めない。`RoleMethodTable` は method name で index されており、
   receiver に適用可能かどうかは role constraint と impl resolution を必要とする。
   filter なしの列挙は呼び出せない method を提示するため、完了には applicability-aware な
   receiver-filtered view が必要。
2. source-order visibility は over-approximation のまま。completion query は
   `ModuleOrder::from_index(u32::MAX)` を渡すため、file 内で cursor より後に宣言された name も
   候補になる。完了には cursor byte offset から `ModuleOrder` への mapping が必要だが、
   現在は存在しない。use alias は order を保持するが source span を持たず、direct value の
   span は identifier だけを覆い、CST / order-position table も保持していない。
   なお、既存の exact-name resolution 自体も earlier declaration がない場合には最も近い
   later declaration を選び得るため、この over-approximation は最初に見えるほど挙動から
   離れてはいない。
3. local scope extent は executable position では正確だが、trivia-only position では
   under-report し得る。non-recursive binding の interval は次の CST item から始まるため、
   その直前の blank whitespace では binding を落とす場合がある。arm binding も guard または
   body expression から始まり、arrow / guard punctuation は含まない。error direction は安全で、
   scope 外の binding を候補に出すことはない。
4. LSP に last-good-analysis fallback はない。current buffer の analysis が完全に失敗すると、
   completion は keyword-only（member context では empty）へ degrade する。直前の成功した
   analysis を保持できれば、この状況を改善できる。

## lazy per-hover Yumark 評価（実装済み）

- 2026-07-18 の調査で、探索時に挙げていた API prerequisite は実装上の blocker ではないと
  分かった。doc-comment hover の lazy Yumark 評価は live LSP 経路まで実装済み。
- `crates/yulang/src/yumark_render_worker.rs` に、warm embedded std を保持する resident worker と
  content-keyed の bounded LRU cache を置いた。
- `crates/yulang/src/server.rs` の hover draft は signature と documentation の二部に分かれ、
  documentation draft が static renderer の fallback Markdown と、safe doc comment に対する
  optional lazy render input を保持する。
- live LSP は safe doc comment を resident worker で評価する。worker の失敗、timeout、起動不能時も
  常に利用できる既存 static renderer の結果へ graceful に fallback する。
- この実装には、parser-generated blank line を純粋な structural separator にすることと、連続する
  `--` line-doc comment を独立した文書ではなく一つの structural continuation として parse することの
  二つの Yumark 言語意味論修正も必要だった。詳細は
  `../design/2026-07-18-yumark-structural-boundaries.md` を参照する。
- Slice 9、すなわち lazy path を always-on だが graceful fallback を伴う補完経路から実際の
  default / primary policy にする判断は、production experience / usage feedback を待って明示的に
  defer する。技術的に blocked されているのではなく、方針を意図的にまだ決めていない。

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
