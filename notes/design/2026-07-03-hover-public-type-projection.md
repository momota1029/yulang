# Hover / playground 型表示の public type projection

決定日: 2026-07-03（改訂1: 2026-07-04）
状態: **実装は実質完了。残りは LSP の 1200 文字 hard cap と、非自明な
stack weight を含む型での dump / hover・wasm 綴り parity の二点。**
署名: Claude Fable 5

この文書は、LSP hover と playground 型表示が内部 evidence・solver 装飾・
巨大型を漏らさないための「公開表示用 formatter 入口」を固定する。
Contract v1 Priority 3（Diagnostics + LSP / playground parity）の
「hover は public projection を出す」項目の正本。

根拠（2026-07-03 調査時の出発点と、現行実装の確認）:

- 2026-07-03 時点では、LSP hover の def 経路と wasm exported types は debug 用の
  `poly::dump::format_scheme_with_path_rewriter` を直接使っていた。
  現在は両方とも `format_scheme_public_with_path_rewriter` を使う
  （`crates/yulang/src/source/mod.rs:3311`、`crates/wasm/src/lib.rs:521`）。
- 公開シグネチャ contract の dump `pub` 行は debug dump の綴りを保つ面である。
  そのため、単純な型では public projection と同じでも、stack weight を含む非自明な型は
  dump の `#0[Empty]` と hover / wasm の `@∅` がまだ一致しない。この差は P4 の残課題。
- public formatter は `arena` / `namer` / `path_rewriter` に加えて Public style、
  redaction / truncation counter、深さ・出力 budget を持つ。LSP の 1200 文字 cap
  （`crates/yulang/src/server.rs:793`）は構造的切り詰め後に残る最終文字列切断であり、
  これをどう扱うかは未完了。

## 0. 中心原理

> **hover / playground の型表示は、公開シグネチャ contract と同じ綴りへ収束する。**

debug dump は solver の真実を全部見せる面。公開表示は public signature の
綴りを正本とする面。この二つを同一 formatter の「様式（style）」として
分離し、消費面ごとの ad-hoc な文字列後処理を作らない。

## 決定 P1: 単一の公開表示入口

`poly::dump` に public style を追加する（`format_scheme_public`、
内部は `TypeFormatter` の `style: Debug | Public`）。これは実装済み。

- 入力は debug 側と同じ `TypeArena + Scheme + path_rewriter`。
- 消費面: LSP hover の def 経路、wasm exported types、将来の
  host manifest 表示・CLI 型表示。
- **debug 側の綴りは一切変えない。** 既存 dump テスト（`#0[Empty]` を
  期待値に持つ `crates/yulang/src/source/tests/case_02.rs:1563` / `:1573`
  を含む）は debug 面の固定であり、触らない。

戻り値は文字列単体ではなく `redactions: u32` と `truncations: u32` を伴う
（`PublicTypeDisplay`）。redaction と構造的切り詰めを消費面とテストが別々に
観測できるようにするため。

## 決定 P2: 内部 marker の扱い（漏出の二分類）

**クラス 1 — solver 帳簿の装飾。黙って落とす。**

- `#N` / `#N(n)` / `#N[...]` stack suffix
  （`crates/poly/src/dump/type_format/formatter.rs:968` / `:982`）
- `stack(T, { ... })` / `@0` / `filter[...]` / `floor` / `pop` の full 形
  （`formatter.rs:188` / `:905` / `:935`）
- `AllExcept(...)` / `All` / `Empty` の subtractability 表示
  （`formatter.rs:999` / `:1009`、`crates/poly/src/types.rs:147`）

根拠: 公開シグネチャ contract はこれらを含む綴りを拒否している。
つまり公開型の正しい綴りは最初からこれらを含まない。落とすことは
「嘘をつく」ではなく「公開綴りへの収束」であり、redaction に数えない。

**クラス 2 — 型本体に意味を持つ内部実体。隠さず redact する。**

- debug quote される合成名・`#...` segment を含む path / field / variant 名
  （`crates/poly/src/dump/type_format.rs:304`）
- centerless bounds の `lower <: upper` sandwich
  （`formatter.rs:730` / `:747`）。片側が自明（`All` / `Empty` 相当）なら
  他側だけを綴り、両側非自明なら redact。

redact の綴りは `…`（U+2026 一文字。Yulang 構文と衝突しない）。
`redactions` counter を増やす。redaction が公開面に現れることは
「internal が公開面に届いた」印であり、canary が検出したら表示の
問題ではなく上流の bug として扱う。fake clean な型を作文して見せる
方向には拡大しない（unsupported host が fake success しないのと同じ原理）。

## 決定 P2R（改訂1、2026-07-04）: stack weight は公開表示する

ユーザ決定により、クラス 1 のうち **stack weight（境界 id・pop 数・
subtractability）は「黙って落とす」をやめ、公開記法で表示する**。
根拠: これらは型の意味を大きく変える情報であり、重みは型変数ではなく
「出現」に付くため trailer に逃がせず、inline 表示が意味論的に必須。

公開記法（ユーザ提案・2026-07-04 採用）:

- 境界 id は `@N`（spec 2026-05-31 の `@h` 記法と同系）。
- subtractability はスタックに乗るものの実態で綴り分ける:
  - `Empty` → `(∅)` — この境界からは何も引けない（protect）
  - `All` → `(∀)` — 全 family を引ける
  - `Set(hs)` → `[hs]` — 行が乗っているので row 括弧をそのまま使う
  - `AllExcept(hs)` → `(except [hs])`
- pop 数は `(2)` のように数字括弧。数字括弧 = pop、記号括弧 =
  subtractability で衝突しない。pop(1) 単独（debug の裸 `#N`）は
  `@N` のみ。
- **省略規則**: 表示中の scheme に distinct な境界 id が 1 つしか
  ないときは id を省略する。さらに単記号（`∅` / `∀`）は括弧も省略して
  `'a@∅` の形にする。`except [hs]`・`[hs]`・pop 数は id を省いても
  括弧・ブラケットを保つ（`'a@(except [io])`、`'a@[io]`、`'a@(2)`）。
  裸の pop(1) は `'a@`。
- 例（`twice`、単一境界）:
  `(('a | 'b) ['c@∅] -> ['c@∅ & 'd@∅] 'b & 'e) -> 'a -> ['d] 'e@`
- `filter` / `floor` は spec 上 principal 型に現れない solver 内部
  なので、公開表示では従来どおり出さない（debug 専用のまま）。
  万一 Public 経路でこれらを含む weight に遭遇したら `…` redact
  として数える（fake clean にしない）。
- Unicode（`∅` / `∀` / `…`）は許容。型は表示するものであって
  書くものではない（ユーザ判断）。

これに伴い leak canary の deny 対象（`#` / `AllExcept` / `stack(`）は
不変。新記法はどれにも触れない。Stage 1 で追加した公開面の期待値
（marker が消えた綴りを固定したもの）は、この改訂で新記法へ更新して
よい。debug 面の期待値は従来どおり触らない。

実装状況: **完了**。`public_stack_weight_suffix` が単一境界の id 省略、
`∅` / `∀` / set / except / pop-count の各形を描画し、filter / floor と
複数 entry は `…` redaction にする
（`crates/poly/src/dump/type_format/formatter.rs:1368`）。各記法と redaction は
`crates/poly/src/dump/type_format.rs` の `public_scheme_*` test で固定している。

## 決定 P3: 構造的切り詰め（Stage 2）

深さ budget と出力 budget を public style に持たせ、超過 subtree を
`…` で綴る。これは実装済みで、深さ budget は 10、出力 budget は 600 文字
（`crates/poly/src/dump/type_format.rs:16`）。深さ超過と record tail の両方で
構造的に切り詰めることを `public_scheme_truncates_*` test が固定している。

LSP の 1200 文字 cap は構造的切り詰め後の最終安全網として現在も残る。
この hard cap の扱いは Stage 2 の残課題に記す。

## 決定 P4: parity の実行可能な錨

- **dump-parity**: `pub id x = x` の単純 case では public projection の出力 ==
  dump `pub` 行の型綴り、を
  `public_type_projection_matches_dump_public_signature_for_contract_type`
  （`crates/yulang/src/source/tests/case_02.rs:2126`）で固定している。
  ただしこれは部分完了に留まる。`twice` のように stack weight を含む型では、
  dump 側の `#0[Empty]` と hover / wasm 側の `@∅` が異なる
  （`case_02.rs:2100` / `:3881`、
  `crates/wasm/src/playground_tests.rs:860`）。非自明な型でも同じ綴りにすることが
  この parity の未完了部分。
- **leak canary**: LSP hover と wasm exported types の出力が
  `#` / `AllExcept` / `stack(` / `<:` / debug quote を含まないことを、
  既存 deny helper（`crates/yulang/src/source/tests/mod.rs:288`）の
  再利用で固定している。source hover は `case_02.rs:3881`、wasm exported types は
  `crates/wasm/src/playground_tests.rs:860` で実装・固定済み。単純 parity case では
  `redactions == 0` も固定している。

## Stage 分割

**Stage 1（完了。見た目の変化は marker の消失のみ）**

1. `poly::dump` に Public style、redactions / truncations counter を実装した。
2. LSP hover の def 経路を public 入口へ載せ替えた
   （`crates/yulang/src/source/mod.rs:3311`）。
3. wasm exported types を public 入口へ載せ替えた
   （`crates/wasm/src/lib.rs:521`）。
4. P4 の leak canary と単純 case の dump-parity test を追加した。既存 debug dump
   テストは期待値不変であることを確認している。非自明な stack weight の parity は
   下記の残課題。

停止条件: 既存テストの期待値変更が必要になったら、書き換えずに停止して
報告する。hover の既存期待値に marker が含まれていた場合は、それが
debug 面の固定か公開面の固定かを判定してから動く。

**Stage 2（実装済み。残課題は二点）**

- 構造的切り詰めの数値と `…` の見た目（P3）は完了。深さ 10、出力 600 文字を
  public formatter で扱う。
- hover の local arg / select 経路は完了。local arg は
  `format_inferred_*_public_with_path_rewriter` を通し
  （`crates/infer/src/check.rs:158` / `:189`）、record select と resolved method
  select は selected value の公開 formatter を通す
  （`crates/yulang/src/source/mod.rs:3172` / `:3198`）。
- redaction 綴りは完了。`PUBLIC_REDACTION` は U+2026 の `…` で、redaction と
  truncation は別 counter で観測する
  （`crates/poly/src/dump/type_format.rs:16`）。
- **未完了: LSP 文字列 cap。** `crates/yulang/src/server.rs:793` が構造的 public
  formatter 後にも hard 1200-char `take` と `"\n..."` suffix を適用している。
  完了は、structural truncation が通常・病的な入力とも妥当な上限に収めることを確認した上で、
  この cap を削除するか十分に引き上げること。
- **未完了: 非自明な型の dump / hover・wasm 綴り parity。** `twice` の stack weight は
  dump が `#0[Empty]`、hover / wasm が `@∅` であり、P4 の同一綴りの錨は単純 case にしか
  成立していない。

## 契約として固定済みのテスト一覧

`tests/yulang/cases.toml` には hover / LSP / wasm の case kind がないため、この層の契約は
以下の Rust regression test を `CONTRACT(hover-public-type-projection)` marker で固定する。
期待値や観測を変えるときは、この文書も同じ変更で更新する。

### `crates/poly/src/dump/type_format.rs`

- `public_scheme_renders_bare_pop_one_stack_weight_without_redaction` — `crates/poly/src/dump/type_format.rs`
- `public_scheme_omits_single_boundary_id_for_empty_subtractability` — `crates/poly/src/dump/type_format.rs`
- `public_scheme_omits_single_boundary_id_for_all_subtractability` — `crates/poly/src/dump/type_format.rs`
- `public_scheme_keeps_brackets_for_set_subtractability` — `crates/poly/src/dump/type_format.rs`
- `public_scheme_keeps_except_form_for_all_except_subtractability` — `crates/poly/src/dump/type_format.rs`
- `public_scheme_renders_pop_count_with_numeric_parens` — `crates/poly/src/dump/type_format.rs`
- `public_scheme_renders_multiple_boundary_ids_by_occurrence_order` — `crates/poly/src/dump/type_format.rs`
- `public_scheme_hides_quantifier_stack_sentinel` — `crates/poly/src/dump/type_format.rs`
- `public_scheme_redacts_full_stack_weight_shapes` — `crates/poly/src/dump/type_format.rs`
- `public_scheme_redacts_debug_quoted_names` — `crates/poly/src/dump/type_format.rs`
- `public_scheme_redacts_centerless_sandwich_bounds` — `crates/poly/src/dump/type_format.rs`
- `public_scheme_truncates_over_depth_budget` — `crates/poly/src/dump/type_format.rs`
- `public_scheme_truncates_sibling_tail_over_length_budget` — `crates/poly/src/dump/type_format.rs`

### `crates/yulang/src/source/tests/case_02.rs`

- `public_type_projection_matches_dump_public_signature_for_contract_type` — `crates/yulang/src/source/tests/case_02.rs`（単純 case のみ）
- `hover_entry_source_reports_lambda_arg_type` — `crates/yulang/src/source/tests/case_02.rs`
- `hover_entry_source_reports_lambda_arg_ref_type` — `crates/yulang/src/source/tests/case_02.rs`
- `hover_entry_source_uses_nearest_shadowed_lambda_arg_type` — `crates/yulang/src/source/tests/case_02.rs`
- `hover_entry_source_public_def_type_does_not_leak_private_markers` — `crates/yulang/src/source/tests/case_02.rs`
- `hover_entry_source_local_arg_type_does_not_leak_private_markers` — `crates/yulang/src/source/tests/case_02.rs`
- `hover_entry_source_record_select_type_does_not_leak_private_markers` — `crates/yulang/src/source/tests/case_02.rs`
- `hover_entry_source_large_record_type_is_structurally_truncated` — `crates/yulang/src/source/tests/case_02.rs`
- `hover_entry_source_reports_attached_role_method_selection_type` — `crates/yulang/src/source/tests/case_02.rs`
- `hover_entry_source_reports_record_field_selection_type` — `crates/yulang/src/source/tests/case_02.rs`
- `hover_entry_source_reports_selected_method_type` — `crates/yulang/src/source/tests/case_02.rs`

### `crates/wasm/src/playground_tests.rs`

- `run_inner_reports_exported_types` — `crates/wasm/src/playground_tests.rs`
- `run_inner_reports_exported_types_for_playground_std_source` — `crates/wasm/src/playground_tests.rs`
- `run_inner_exported_types_do_not_leak_private_markers` — `crates/wasm/src/playground_tests.rs`

## Do not

- debug dump の綴りを変えない。dump は solver の真実を見せる面のまま残す。
- 公開表示を通すために contract の deny を緩めない。
- クラス 2 の redact を「型を作り直して見せる」方向に拡大しない。
- 消費面（LSP / wasm）に formatter 出力の文字列後処理を足さない。
  現在の LSP final cap は既知の例外であり、Stage 2 の残課題として扱う。
  直したくなったら public style 側を直す。
