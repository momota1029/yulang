# host ABI Stage α + manifest 生成移行 実装手順書（Codex 向け handoff）

作成日: 2026-07-03
著者: Claude (Fable 5)
対象: Codex（または後続の実装 agent）
状態: ユーザ承認済みの二つの正本文書に基づく実装手順。**本手順書は正本ではない。**
判断に迷ったら常に正本へ戻ること。

## 正本（実装前に必ず全文を読む）

1. `notes/design/2026-07-03-host-abi-v0.md` — host 実装 ABI 契約 v0。
   `HostOpFn` / `BoundaryValue` / `HostOutcome` / `HostCtx` / 登録集合 / symbol mangling の定義。
2. `notes/design/2026-07-03-host-manifest-compiler-production-plan.md`（改訂1）—
   manifest の compiler 生成移行。`host` 修飾子（D2'）、schema（D3）、搬送（D4）、
   registry（D5'）、Stage 分割と Validation。
3. 背景の意味論: `notes/design/2026-07-02-host-act-ffi-decisions.md`（v2）。

規則（`.rules` / AGENTS.md にも同旨がある。違反は差し戻し対象）:

- **テスト期待値は正本から手で導出する。実装の出力から逆算しない。**
- **既存テスト・fixture の期待値を変更しない。** 例外は本手順書 WP3 §期待値更新に
  列挙したファイルだけ。それ以外の既存テストが落ちたら、直すのは実装のほう。
  直せないなら停止して報告する。
- 正本の意味論・Rollback 条件を実装の都合で変えない。変えたくなったら停止して報告する。
- workspace 全体を stash して base で全 `cargo test` を回さない（ハングする既知問題）。
  検証は §受け入れゲート のコマンド列だけを使う。

## 全体構成

三つの work package。**WP1 と WP2 は独立で、どちらからでも着手できる。
WP3 は WP1・WP2 の両方が受け入れゲートを通ってから。**
各 WP は単独で main に置ける状態（全テスト green・挙動変更ゼロ、WP3 のみ期待値更新あり）
で完了させる。WP をまたいで中途半端な状態を残さない。

---

## WP1: ABI Stage α — 骨格導入と file/console 載せ替え（挙動不変）

正本: ABI 文書 §2〜§4, §7, §8 Stage α, §11-1/2/3。

### 手順

1. **ABI 型の導入。** `crates/evidence-vm/src/runtime/host_abi.rs`（新規）に
   `BoundaryValue` / `CtorRef` / `HostOutcome` / `HostCtx` / `HostOpFn` /
   `HostOpRegistration` を置く。形は ABI 文書 §2〜§4 のとおり。
   - `CtorRef::Label` のみ実装（`Tag` は入れない。enum の variant 予約もしない —
     必要になる Stage 3 で足す）。
   - `BoundaryValue` の variant は §3 に列挙されたものだけ。List / Record を先回りで
     足さない。
2. **codec。** `RuntimeEvidenceValue` ↔ `BoundaryValue` の変換を runtime 側に書く。
   - 変換は所有コピー。`Rc` や内部値を `BoundaryValue` に格納しない。
   - `CtorRef::Label` → `DefId` の解決は起動時に一度（既存の
     `RuntimeEvidenceHostConstructors::from_labels`（runtime.rs 130-171）の機構を
     内部でそのまま使ってよい。解決できない label は structured failure、
     現行の `yulang.host-io-error` 系と同じ扱い）。
3. **9 実装関数の載せ替え。** runtime.rs の `file_load` / `file_store` / `file_meta` /
   `file_read_at` / `file_write_at` / `file_ambient_touch` / `file_ambient_get` /
   `file_ambient_set` / console write を `HostOpFn` 署名
   （`fn(&mut HostCtx, &BoundaryValue) -> HostOutcome`）の自由関数に移す。
   - runner の `self` に触れない。fs 呼び出しとドメインエラー構築のロジックは
     移動するだけで変えない。
   - console の出力先: 現在は runner 所有の `self.stdout`。登録時に預ける共有 sink
     （`Rc<RefCell<String>>` 等）に置き換え、runner は実行後にそこから回収する。
     `RuntimeEvidenceRunOutput` の stdout 内容は一字も変わらないこと。
4. **登録集合。** `builtin_host_registrations()` を evidence-vm が公開し、
   registry 構築時に受け取る。dispatch は関数ポインタ経由にする。
   - この WP では**解決（path → どの op か）は現行の `RUNTIME_HOST_MANIFEST`
     静的テーブルのまま**。変えるのは「解決後に何を呼ぶか」だけ。
   - `RuntimeHostOperation` enum は、静的テーブルの spec 構造体が要る間は残してよい
     （消すのは WP3）。
5. **新規テスト**（evidence-vm 内 unit test）:
   - 登録 API 経由で file の一操作を mock 実装（fs に触れない `HostOpFn`）に
     差し替え、その実装が呼ばれることを観測する（登録経路の smoke。
     独自 act の登録テストは WP3 まで書けない — 解決が静的テーブルのままなので）。
   - panic する `HostOpFn` を登録して呼ぶ → structured failure になり
     プロセスは死なない（`catch_unwind` 防御、ABI 文書 §11-3）。
   - `BoundaryValue` codec の往復（プリミティブ・Tuple・Constructor{Label}）。

### 受け入れ

- §受け入れゲート 全通過。**既存テスト・fixture の期待値変更ゼロ**（ABI 文書 §11-1）。
- `HostCtx` の公開 API に perform / resume / eval / runner へ触れる口がないこと
  （ABI 文書 §11-5、構成による保証）。

---

## WP2: manifest Stage 1 — `host` 修飾子と compiler 生成（挙動変更ゼロ）

正本: manifest 指示書 D1 / D2' / D3 / D6 / D7、Stage 1、Validation 5〜8。

### 手順

1. **`host` 修飾子。** `crates/parser/src/stmt/act_decl.rs` を起点に、
   `pub host act file:` を受理する。
   - **`host` は文脈キーワード。** act 宣言の修飾子位置でだけ意味を持たせ、
     識別子としての `host` を全域で潰さない（既存プログラムを壊さない）。
   - flag を `SyntaxKind::ActDecl` → module map → compiled namespace
     （`CompiledNamespaceTypeKind::Act` の系、infer/syntax.rs 1054 と
     infer/compiled_lowering.rs 190-260 が seam）まで bool 一枚で通す。
   - compiled namespace の直列化形が変わるので、compiled-unit cache の
     versioning / invalidation は既存の慣習に従う（黙って古い cache を読まない）。
   - `lib/std/io/file.yu` の `pub act file:` と `lib/std/io/console.yu` の
     out act に `host` を付ける。他の act には付けない。
2. **`poly::host_manifest`（新規モジュール）。** manifest 指示書 D3 の型
   （`HostActManifest` / `HostActManifestAct` / `HostActManifestOperation`、
   serde derive 付き）と検証・column 採番・hash・symbol mangling。
   - mangling は ABI 文書 §5 の長さ接頭辞方式。
     例で固定: `std.io.file.file` の `load` → `yu_host_3std2io4file4file_4load`。
   - unit tests: (act_id, op_id) 一意 / path prefix 検証 / column が入力順に
     依存しない / hash が決定的 / mangling の決定性と単射性
     （現行 9 op + `_` を含む人工セグメントのコーパス）。
3. **`crates/infer/src/host_acts.rs`（新規）。**
   - surface override 表: `read_at` / `write_at` → raw-compat の 2 件**だけ**。
   - 生成関数: compiled namespace の `host` flag 付き act と
     その act_operations（compiled_lowering.rs が既に収集している）から
     `HostActManifest` を組む。surface 既定 contract、tier 既定 sync。
   - override が宣言に存在しない op を指したら生成エラー（Err で返す。panic しない）。
4. **signature 文字列**は public signature printer（public signature canary が
   固定している既存の印字系）の出力を使う（D6）。新しい印字器を書かない。
5. **等価性テスト**（`crates/yulang` 内 — infer と evidence-vm の両方が見える）:
   compiled std から生成した manifest と
   `evidence_vm::runtime_host_manifest_operations()` が
   **(act_id, operation_id, path, tier, surface) で一致**する。
   signature は比較しない（正本の指示。D6 で正本が印字系に入れ替わるため）。
6. **消費点は一切変えない。** registry・static route 分類・CLI・既存テストはそのまま。

### 受け入れ

- §受け入れゲート 全通過。既存テスト・fixture の期待値変更ゼロ。
- 等価性テストと、manifest 指示書 Validation 6〜8
  （override drift エラー / host act の全宣言 op 網羅 + 非 host act の非掲載 /
  column・hash・symbol の決定性）が新規テストとして存在し green。

---

## WP3: manifest Stage 2 — 切替と削除（前提: WP1 と WP2 の完了）

正本: manifest 指示書 D4 / D5'、Stage 2、移行表、Validation 全項目。

### 手順

1. `RuntimeEvidenceSurface`（specialize/specialize2/runtime_evidence.rs 19）に
   `host_manifest` を載せる。導管は `known_state_handlers` の前例に従う。
   `EvidenceVmPlan` が保持し、runtime は `RuntimeEvidenceRunContext::from_plan` 経由で読む。
2. registry を `RuntimeHostRegistry::new(manifest, registrations, native_host_operations_enabled)`
   に変え、構築時に一度だけ (act_id, operation_id) で束ねて path → resolution の
   hash map を作る。
   - resolution 意味論は現行と完全一致（manifest 指示書 D5' の箇条書きどおり）。
     unknown act → `EscapedEffect`、manifest act の unknown / 未登録 /
     native 無効 op → capability failure。
3. static route 分類（evidence-vm/src/lib.rs 2779 の
   `runtime_host_manifest_has_known_act`）を plan の manifest 参照に切替、静的関数を削除。
4. `debug host-act-manifest` を「std を compile して生成 manifest を印字」に切替。
   std の収集は contract runner と同じ経路。行形式は現行 + `column=` を末尾に追加。
5. 削除: `RUNTIME_HOST_MANIFEST` / `RUNTIME_HOST_OPERATIONS` / `RUNTIME_HOST_ACTS` /
   path 定数 / 手書き signature 文字列 / `RuntimeHostOperation` enum /
   WP2 の等価性テスト。evidence-vm から act の path 文字列定数が消えていることが
   受け入れ条件の一つ。
6. host.rs の静的テーブル canary テストを、生成 manifest 側の canary に移設
   （contract 7 / raw-compat 2 の surface 集合、file 8 + console 1 の op 数、など
   同じ主張を生成側で言い直す）。
7. runtime unit tests（runtime.rs 20606 付近など静的テーブル前提のもの）には
   手組みのテスト用 manifest fixture helper を与える。
8. 新規テスト: 登録 API から**独自 act**（テスト用 manifest + mock 実装）を通す
   FFI smoke（ABI 文書 §11-2。WP1 では書けなかったもの）。
   manifest にあり実装がない op → capability failure。
   登録集合にあり manifest にない entry → fail（または構築時 debug_assert + テスト）。

### 期待値更新（既存期待値に触れてよい唯一の場所）

次の 3 箇所**だけ**、正本から手で導出した新しい期待値に更新する。
それぞれ「何が」「なぜ」変わるかを commit message に書く。

- `crates/yulang/tests/cli.rs` の `debug_host_act_manifest_prints_runtime_registry_view`:
  signature が printer 印字形になる差分と `column=` の追加。
  期待値は lib/std の宣言 + printer 規則から導出する（実行して出力を貼らない）。
- `scripts/release-smoke.sh:96` の manifest 出力確認: 同上。
- `crates/evidence-vm/src/runtime/host.rs` の unit tests: 手順 6 の移設に伴う削除・移動。

`tests/yulang/cases.toml` と public signature canary は**変更禁止**。
ここに差分が要るように見えたら実装が間違っている。停止して報告する。

---

## 受け入れゲート（各 WP の完了時に全部）

```bash
cargo fmt --all -- --check
cargo check -q -p poly -p infer -p specialize -p evidence-vm -p yulang
cargo test -q -p poly
cargo test -q -p infer
cargo test -q -p evidence-vm
cargo test -q -p yulang --test cli -- --test-threads=1
cargo run -q -p yulang -- --std-root lib contract --contract file-resource tests/yulang/cases.toml
```

WP3 完了時のみ追加:

```bash
scripts/release-smoke.sh <binary>
```

## 停止条件（進めずに、本手順書末尾の進捗ログに状況を書いて止まる）

- 既存テストが落ち、期待値を変えないと直せないように見えた
  （§期待値更新 に列挙した 3 箇所を除く）。
- capability failure と `EscapedEffect` の線引きが、既存 fixture のどれか一つでも変わる。
- `host` 修飾子の導入が、`host` を識別子として使う既存コードや
  非 host act の経路を壊す。
- compiled namespace / RuntimeEvidenceSurface の seam で act 宣言の全 op が見えない。
- `BoundaryValue` で表現できない越境が必要になった（内部値を直接渡したくなった）。
- `HostCtx` に runtime へ触れる口（perform / resume / eval）が要るように見えた。
- signature の印字形を「宣言 + printer 規則」から手で書き下せなかった。

## Do not

- 正本二文書と v2 の意味論・Rollback 条件を変えない。
- suspend tier / scheduler / `CtorRef::Tag` / 型レイアウト表 / band loading /
  Stage 3 に着手しない。
- `host` を全域予約語にしない。
- `BoundaryValue` に List / Record 等を先回りで足さない。
- 実装出力から期待値を逆算しない。
- workspace 全 stash → 全 cargo test をしない。
- 関係ない改善（リファクタ・依存更新・警告つぶし）をついでに広げない。

## 進捗ログ（実装 agent が追記する）

- （WP ごとに: 日付 / 変更したファイル / 受け入れゲートの結果 / 停止した場合はその状況）
- 2026-07-03 / WP2 Stage 1 partial:
  - Added the contextual `host` act modifier without reserving `host` globally:
    parser `ActDecl` now carries `Keyword "host"`, and ordinary `host`
    bindings still parse as identifiers.
  - Threaded the host act flag through `ModuleTable`, compiled namespace
    serialization, compiled namespace merge/restore, and the compiled namespace
    cache hash.
  - Marked only `std::io::file::file` and `std::io::console::out` as host acts.
  - Added `poly::host_manifest` with deterministic sorting, columns, stable
    hash, raw/contract surface, sync/suspend tiers, and A4 length-prefixed
    host symbol mangling.
  - Added `infer::host_acts::host_act_manifest_from_compiled`, generated from
    compiled namespace + lowering + typed surfaces. Signatures use the existing
    `poly::dump::format_scheme` printer over compiled typed schemes; no new
    signature printer was introduced.
  - Added the Stage 1 yulang equivalence test comparing compiler-generated std
    manifest with `evidence_vm::runtime_host_manifest_operations()` on
    `(act_id, operation_id, path, tier, surface)`, intentionally excluding
    signature per D6.
  - Validation:
    - `cargo fmt --all -- --check`
    - `cargo check -q -p poly -p infer -p specialize -p evidence-vm -p yulang`
    - `cargo test -q -p parser host -- --test-threads=1`
    - `cargo test -q -p poly host_manifest -- --test-threads=1`
    - `cargo test -q -p poly` (`48 passed`)
    - `cargo test -q -p infer host_acts -- --test-threads=1`
    - `cargo test -q -p infer` (`513 passed`)
    - `cargo test -q -p evidence-vm` (`105 passed`)
    - `cargo test -q -p yulang --test cli compiler_generated_host_manifest_matches_runtime_stage1_table -- --test-threads=1`
    - `cargo test -q -p yulang --test cli -- --test-threads=1` (`115 passed`)
    - `cargo run -q -p yulang -- --std-root lib contract --contract file-resource tests/yulang/cases.toml`
      (`57 passed`)
  - No stop condition hit. WP2 Stage 1 is complete; WP3 still waits for ABI
    Stage α.
- 2026-07-03 / WP2 Stage 1 drift hardening:
  - `infer::host_acts` now rejects raw-compat overrides that do not correspond
    to a declared host operation, matching the Stage 1 requirement that override
    drift is an error instead of a silent contract fallback.
  - Added the `UnknownRawCompatOverride` build error and unit coverage for both
    matching and missing overrides.
  - Validation:
    - `cargo fmt --check`
    - `cargo test -q -p infer host_acts -- --test-threads=1` (`3 passed`)
    - `cargo test -q -p yulang --test cli compiler_generated_host_manifest -- --test-threads=1`
      (`1 passed`)
    - `cargo test -q -p infer -- --test-threads=1` (`515 passed`)
    - `cargo check -q -p infer -p yulang`
  - No stop condition hit.
- 2026-07-03 / WP2 Stage 1 no-prelude drift follow-up:
  - Narrowed raw-compat override drift checking to host acts present in the
    compiled namespace. This preserves `--no-prelude` custom host-act programs
    while still rejecting missing `read_at` / `write_at` when the std file host
    act is present.
  - Added a CLI canary proving an unregistered user-declared `pub host act stop`
    reports `yulang.unsupported-host-capability` for `stop` rather than falling
    through as an unhandled effect.
  - Validation:
    - `cargo fmt --check`
    - `cargo test -q -p infer host_acts -- --test-threads=1` (`4 passed`)
    - `cargo test -q -p yulang --test cli compatible_run_custom_host_act_without_registration_reports_capability_error -- --test-threads=1`
      (`1 passed`)
    - `cargo test -q -p infer -- --test-threads=1` (`516 passed`)
    - `timeout 720s cargo test -q -p yulang --test cli -- --test-threads=1`
      (`118 passed`)
  - No stop condition hit.
- 2026-07-03 / WP3 Stage 2 complete:
  - Carried compiler-generated host manifests into `EvidenceVmPlan`,
    `RuntimeEvidenceRunContext`, and `RuntimeHostRegistry`.
  - Switched runtime host resolution to the generated manifest lookup plus
    `HostOpRegistration` binding. Unknown manifest acts remain escaped effects;
    unknown / unregistered / disabled operations under manifest acts remain
    unsupported host capabilities.
  - Switched static route host classification to the plan manifest only.
  - Switched `debug host-act-manifest` to compiler-generated manifest output
    and removed the public static runtime operation manifest view.
  - Removed the static runtime host operation table from evidence-vm:
    `RUNTIME_HOST_MANIFEST`, `RUNTIME_HOST_OPERATIONS`, `RUNTIME_HOST_ACTS`,
    path constants, handwritten signatures, `RuntimeHostOperation`, and the
    Stage 1 equivalence test are gone.
  - Runtime unit tests now use hand-built manifest fixtures for host ABI and
    registry cases.
  - Validation:
    - `cargo fmt --all -- --check`
    - `cargo check -q -p poly -p infer -p specialize -p evidence-vm -p yulang`
      (`0m0.077s`)
    - `cargo test -q -p poly` (`48 passed`, `0m0.231s`)
    - `cargo test -q -p infer` (`514 passed`, `0m5.395s`)
    - `cargo test -q -p evidence-vm -- --test-threads=1`
      (`104 passed`, `0m0.247s`)
    - `cargo test -q -p yulang --test cli -- --test-threads=1`
      (`115 passed`, `3m0.036s`)
    - `cargo run -q -p yulang -- --std-root lib contract --contract
      file-resource tests/yulang/cases.toml` (`57 passed`, `3m24.052s`)
    - `scripts/release-smoke.sh target/debug/yulang` (`release smoke ok`,
      `1m56.020s`)
  - No stop condition hit. WP3 Stage 2 is complete. Stage 3 constructor type
    table work was not started.
