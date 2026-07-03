# Hover / playground 型表示の public type projection

決定日: 2026-07-03（改訂1: 2026-07-04）
状態: **決定済み（Stage 1・2 実装済み。改訂1 = 決定 P2R の実装が残り）**
署名: Claude Fable 5

この文書は、LSP hover と playground 型表示が内部 evidence・solver 装飾・
巨大型を漏らさないための「公開表示用 formatter 入口」を固定する。
Contract v1 Priority 3（Diagnostics + LSP / playground parity）の
「hover は public projection を出す」項目の正本。

根拠（2026-07-03 調査で確定した事実）:

- LSP hover の def 経路と wasm exported types は debug 用の
  `poly::dump::format_scheme_with_path_rewriter` を直接使う
  （`crates/yulang/src/source/mod.rs:2668`、`crates/wasm/src/lib.rs:462`）。
- 公開シグネチャ contract（dump の `pub` 行）は別入口 `format_scheme`
  （`crates/poly/src/dump/surface.rs:172`）で、`#` / `AllExcept` が出ない
  のは formatter の抑制ではなく contract 側の拒否
  （`crates/yulang/src/contract.rs:1306`、`deny_type_contains`）による。
- formatter の状態は `arena` / `namer` / `path_rewriter` のみ
  （`crates/poly/src/dump/type_format.rs:165`）。公開用オプション・
  深さ制限・構造的切り詰めは存在しない。LSP の 1200 文字 cap
  （`crates/yulang/src/server.rs:509`）は文字列切断で構造的ではない。

## 0. 中心原理

> **hover / playground の型表示は、公開シグネチャ contract と同じ綴りへ収束する。**

debug dump は solver の真実を全部見せる面。公開表示は public signature の
綴りを正本とする面。この二つを同一 formatter の「様式（style）」として
分離し、消費面ごとの ad-hoc な文字列後処理を作らない。

## 決定 P1: 単一の公開表示入口

`poly::dump` に public style を追加する（例: `format_scheme_public`、
内部は `TypeFormatter` の `style: Debug | Public`）。

- 入力は debug 側と同じ `TypeArena + Scheme + path_rewriter`。
- 消費面: LSP hover の def 経路、wasm exported types、将来の
  host manifest 表示・CLI 型表示。
- **debug 側の綴りは一切変えない。** 既存 dump テスト（`#0[Empty]` を
  期待値に持つ `crates/yulang/src/source/tests/case_02.rs:1563` / `:1573`
  を含む）は debug 面の固定であり、触らない。

戻り値は文字列単体ではなく `redactions: u32` を伴う
（例: `PublicTypeDisplay { text, redactions }`）。redaction の発生を
消費面とテストが観測できるようにするため。

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

## 決定 P3: 構造的切り詰め（Stage 2）

深さ budget と node budget を public style に持たせ、超過 subtree を
`…` で綴る。LSP の 1200 文字 cap は最終安全網として温存し、通常は
構造的切り詰めが先に効く状態にする。**具体的な数値と見た目は
Stage 2 の着手時にユーザ確認してから決める。**

## 決定 P4: parity の実行可能な錨

- **dump-parity**: public signature contract を通る `pub` def について、
  public projection の出力 == dump `pub` 行の型綴り、を固定するテストを
  代表 case で置く。
- **leak canary**: LSP hover と wasm exported types の出力が
  `#` / `AllExcept` / `stack(` / `<:` / debug quote を含まないことを、
  既存 deny helper（`crates/yulang/src/source/tests/mod.rs:288`）の
  再利用で固定する。加えて代表 public def で `redactions == 0` を固定する。

## Stage 分割

**Stage 1（着手可。見た目の変化は marker の消失のみ）**

1. `poly::dump` に Public style と `redactions` counter を実装する。
2. LSP hover の def 経路（`crates/yulang/src/source/mod.rs:2532` / `:2668`）
   を public 入口へ載せ替える。
3. wasm exported types（`crates/wasm/src/lib.rs:462`）を public 入口へ
   載せ替える。
4. P4 の dump-parity テストと leak canary を追加する。既存 dump テストは
   期待値不変であることを確認する。

停止条件: 既存テストの期待値変更が必要になったら、書き換えずに停止して
報告する。hover の既存期待値に marker が含まれていた場合は、それが
debug 面の固定か公開面の固定かを判定してから動く。

**Stage 2（ユーザ確認が停止点）**

- 構造的切り詰めの数値と `…` の見た目（P3）。
- hover の local arg / select 経路（`crates/infer/src/check.rs:139` / `:158`
  の inferred formatter。use-site `TypeVar` を表示用に落とす前処理が必要）。
- LSP 文字列 cap の置換。
- redaction 綴りの最終決定。

## Do not

- debug dump の綴りを変えない。dump は solver の真実を見せる面のまま残す。
- 公開表示を通すために contract の deny を緩めない。
- クラス 2 の redact を「型を作り直して見せる」方向に拡大しない。
- 消費面（LSP / wasm）に formatter 出力の文字列後処理を足さない。
  直したくなったら public style 側を直す。
