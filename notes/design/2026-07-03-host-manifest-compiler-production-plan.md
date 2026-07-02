# host act manifest / registry の compiler 生成移行 指示書

決定日: 2026-07-03（改訂1: 同日）
著者: Claude (Fable 5) — ユーザの依頼により作成。
状態: **決定済み（authoritative・ユーザ承認 2026-07-03、改訂1 込み）**

改訂1（2026-07-03）: ユーザ指摘「これは FFI ではない」を受け、
[2026-07-03-host-abi-v0.md](2026-07-03-host-abi-v0.md)（host 実装 ABI 契約 v0）の
**subset** として改訂した。変更点: D2 の designation 表を `host` 修飾子構文に置換（D2'）、
D5 の実装定数を ABI の登録集合 API に置換（D5'）、D3 schema に symbol 名を追加。
manifest = symbol の名前空間、registry = symbol 解決、という ABI 文書の読み替えに従う。

位置づけ:

- [2026-07-03-host-abi-v0.md](2026-07-03-host-abi-v0.md)（ABI v0）の Stage β に相当する。
  本文書の registry は ABI の登録集合を受け取る側であり、矛盾したら ABI 文書が勝つ。
- [2026-07-02-host-act-ffi-decisions.md](2026-07-02-host-act-ffi-decisions.md)（以下 v2）
  §F2「lowering は host act ごとに構造化 manifest を出す」と実装順 thin path 1〜2 の実装展開。
  意味論は一切変えない。v2 と矛盾したら v2 が勝つ。
- notes/todo/contract-v1-file-resource-priority.md priority 2（Host act FFI registry）の本体。
- notes/todo/record-replay.md「最重要・時間制約のある一手」（manifest に operation 識別子を
  最初から含める）を schema レベルで先取りする。

テスト期待値は本文書と宣言（lib/std のソース）から手で導出する。実装出力から逆算しない。
実装の都合で意味論を変えたくなったら、実装を止めてユーザに確認する。

## 0. 目的と非目的

目的:

> **「どの act が host 提供で、どんな operation を持つか」の正本を、
> evidence-vm の Rust 静的テーブルから、compiler が宣言から生成する manifest へ移す。**

現在は `crates/evidence-vm/src/runtime/host.rs` の `RUNTIME_HOST_MANIFEST`
（`RUNTIME_HOST_OPERATIONS` / `RUNTIME_HOST_ACTS` の `&'static` テーブル）が正本で、
`lib/std/io/file.yu` の `pub act file:` 宣言と**手作業で同期**している。
op を一つ足すたびに runtime の Rust テーブル・path 配列・signature 文字列を編集する現状を、
「std の宣言を直せば manifest が追随し、runtime は名前で実装を束ねるだけ」に変える。

移行後の責務分界:

- **compiler（正本）**: どの act が host か、各 op の path / 型 / tier / surface / 列番号。
- **runtime（実装の束）**: (act_id, operation_id) 名前キーの Rust 実装表。
  manifest との照合は registry 構築時に一度だけ。

非目的（本工事で触らないもの）:

- tier の表面綴り（v2 F6 の per-op 注釈）。`host` **修飾子そのものは D2' で導入する**が、
  現行 op が全部 sync である間、tier を構文に出さない（manifest 上は既定 sync）。
- suspend tier / scheduler / server accept（v2 thin path 5）。
- wire codec・型レイアウトの一般化（v2 F4 の全体）。Stage 3 で constructor 表のみ扱う。
- record/replay の実装。schema に列番号と hash を**置く**だけで、消費はしない。
- capability failure / EscapedEffect の意味論変更。境界は現行と同一に保つ。

## 1. 現状の棚卸し（正確な消費点一覧）

正本テーブル:

- `crates/evidence-vm/src/runtime/host.rs` — `RUNTIME_HOST_OPERATIONS`（9 op:
  console.out.write / file の load, store, meta, read_at, write_at, ambient_touch,
  ambient_get, ambient_set）、`RUNTIME_HOST_ACTS`（2 act）、`RUNTIME_HOST_MANIFEST`。
  各 spec は act / operation_id / tier（全部 sync）/ surface（contract 7, raw-compat 2）/
  signature（手書き文字列）/ path / `RuntimeHostOperation` enum を持つ。

消費点:

1. **runtime dispatch** — `RuntimeHostRegistry::resolve`（host.rs）→
   `handle_escaped_request` / `try_handle_runtime_host_request`（runtime.rs 12050 付近）。
   escape した request の path を線形走査で照合。
2. **plan 時分類** — `runtime_host_manifest_has_known_act`（evidence-vm/src/lib.rs 2779）。
   static route の GenericFallback を `HostEscape` と非 host に分ける。
3. **CLI** — `yulang debug host-act-manifest`（yulang/src/main.rs `run_host_act_manifest`）。
   引数なしで静的テーブルを印字。
4. **テスト** — host.rs 内 unit tests（op 数 / surface 集合 / path 一意性 / tier canary）、
   `crates/yulang/tests/cli.rs` `debug_host_act_manifest_prints_runtime_registry_view`。
5. **release smoke** — `scripts/release-smoke.sh:96` が manifest 出力行を確認。
6. **隣接（本工事では現状維持）** — `RuntimeEvidenceHostConstructors::from_labels`
   （runtime.rs 130-171）が `DumpLabels` から constructor DefId を名前解決。Stage 3 候補。

宣言側の既存資産（生成の材料が既にあることの確認）:

- `lib/std/io/file.yu` の `pub act file:`（8 op、typed signature 付き）、
  `lib/std/io/console.yu` の out act。
- infer の `CompiledLoweringSurface::from_module_table`（compiled_lowering.rs 246 付近）が
  act ごとの `act_operations`（type_path + op 名 + signature）を既に収集・直列化している。
- crate 依存: poly が最下層（infer / specialize / evidence-vm / yulang すべてが poly を見る）。
  `DumpLabels` が poly::dump にある前例のとおり、共有データ型は poly に置ける。

## 2. 設計決定

### D1. manifest は宣言から生成する（usage からではない）

manifest は「compile された世界（std 込み）の act 宣言」の関数であって、
プログラムが実際にどの op を perform するかに依存しない。
file を一度も触らないプログラムでも manifest は全 9 op を載せる。
これは capability failure の報告（known act / unknown op の区別）と
`debug host-act-manifest` の安定性に必要。
mono が未使用 def を刈っても manifest には影響しない（namespace 宣言由来だから）。

### D2'. host 指定は宣言が持つ: `host` 修飾子（改訂1）

「どの act が host か」の正本は**宣言側**に置く（ABI 文書 R-band1）。v2 F1 の綴りに従い、
修飾子一語だけを導入する:

```yu
pub host act file:
    pub load: path -> result str io_err
    ...
```

- 対象は `lib/std/io/file.yu` の `pub act file:` と `lib/std/io/console.yu` の out act の
  二箇所（＋将来の clock / random / server）。
- tier の per-op 注釈は**導入しない**（現行全 op が sync。綴りは v2 F6 のとおり provisional）。
- 実装 seam: `SyntaxKind::ActDecl`（infer/syntax.rs 1054 付近で `ModuleTypeKind::Act` に
  落ちる系）に host flag を足し、module map → compiled namespace
  （`CompiledNamespaceTypeKind::Act`）まで bool 一枚を通す。非 host act の経路には
  一切影響を与えないこと（opt-in 修飾子）。
- **op の列挙・path・signature は宣言から取る。** file.yu に op を足せば manifest に
  自動で載る（surface は既定 contract、tier は既定 sync）。
- 例外として **surface の raw-compat 指定だけ**は小さな override 表として
  `crates/infer/src/host_acts.rs`（`std_paths.rs` の隣）に残す:
  read_at / write_at の 2 件。これは contract 統治のメタデータであって言語意味論ではなく、
  両 op の退役（migration-canary の完了）と同時に表ごと消える。
  override が宣言に存在しない op を指したら**生成エラー**（黙って落とさない）。
- 旧 D2 の designation 表（host act の path 列挙を compiler 内 Rust 表に置く案）は
  **改訂1 で棄却**。band が自分の host act を宣言する世界（ABI 文書 §1）で成立しないため。
- manifest は cache せず、毎回 compiled surface から決定的に再計算する。
  override 表の変更は compiler 変更と同格に扱う（`runtime_hash` の系）。

### D3. データ型と検証は poly::host_manifest

新モジュール `crates/poly/src/host_manifest.rs`（`poly::dump::DumpLabels` の前例に従う）。
serde derive を付ける（record/replay とアーティファクトでの再利用のため）。

```rust
pub struct HostActManifest {
    pub acts: Vec<HostActManifestAct>,        // act_id 昇順
    pub operations: Vec<HostActManifestOperation>, // (act_id, operation_id) 昇順 = column 順
    pub hash: HostManifestHash,               // 決定的直列化の hash
}

pub struct HostActManifestAct {
    pub act_id: String,          // "std.io.file.file"（宣言の namespace path の dotted 形）
    pub path: Vec<String>,
}

pub struct HostActManifestOperation {
    pub act_id: String,
    pub operation_id: String,    // "load"
    pub path: Vec<String>,       // act path + operation_id
    pub tier: HostOperationTier, // Sync | SuspendOneShot | SuspendMultiShot（現状全部 Sync）
    pub surface: HostOperationSurface, // Contract | RawCompat
    pub signature: String,       // D6: public signature printer の出力
    pub column: u32,             // D7: record/replay 用の安定序数
    pub symbol: String,          // ABI 文書 A4 の mangling 規則で act_id + op_id から決定的導出
}
```

- `symbol` は native リンク用の名前（ABI 文書 §5）。VM 経路では表引きに使わないが、
  manifest が symbol 名前空間の正本であることを schema で固定する。
- act_id は namespace の dotted path。band が入れば band 修飾を含む path になる想定で、
  schema はそのまま通る形に保つ（ABI 文書 R-band1）。
- 型レイアウト表（ABI 文書 `CtorRef::Tag` の正本、v2 F4）は Stage 3 の拡張点として
  予約する。v0 では持たない。

構築時の検証（コンストラクタで強制、違反は Err）:

- (act_id, operation_id) 一意、path 一意、op path は必ず自 act path を prefix に持つ。
- column は (act_id, operation_id) 昇順で 0 起点連番。順序は入力順に依存しない。
- hash は fields の決定的直列化に対する hash。同じ宣言集合 → 同じ hash。
  hash 関数の選定は実装に委ねる（安定・非暗号で十分）。

### D4. 搬送は RuntimeEvidenceSurface → EvidenceVmPlan → runtime

- infer が compiled namespace（`CompiledLoweringSurface` が既に集めている
  `act_operations`）と D2 の designation から `poly::host_manifest::HostActManifest`
  を構築する関数を公開する。
- specialize の `RuntimeEvidenceSurface`（specialize2/runtime_evidence.rs 19）に
  `host_manifest` フィールドを足す。導管は `known_state_handlers` の前例
  （static-route Stage 0 で確立済み）に従う。
- `evidence_vm::build_plan(program, surface)` は署名を変えずに surface から
  manifest を受け取り、`EvidenceVmPlan` に保持する。
  これで CLI / wasm / テストのすべての呼び出し元が自動的に manifest を得る。
- runtime は `RuntimeEvidenceRunContext::from_plan` 経由で plan の manifest を読む。
  runtime への別引数追加はしない。

### D5'. runtime registry = plan の manifest × ABI 登録集合（改訂1）

host.rs から「host act が何であるか」の知識が消え、残るのは **ABI 文書 §7 の
登録集合 API と builtin 実装**だけになる:

```rust
// ABI 文書 A6 の HostOpRegistration。実装関数は HostOpFn（BoundaryValue 境界）。
// builtin 束は evidence-vm が builtin_host_registrations() として提供し、
// CLI はそれを registry に渡す。テストは同じ口から mock / 独自 act を登録できる。
RuntimeHostRegistry::new(manifest, registrations, native_host_operations_enabled)
```

- 旧 D5 の `HOST_IMPLEMENTATIONS` 定数（evidence-vm 内に閉じた実装表）は**改訂1 で棄却**。
  registry は外から登録集合を受け取る口であり、CLI 組み込みの file / console は
  その最初の利用者にすぎない（ABI 文書 §0 の subset 原理）。
  `RuntimeHostOperation` enum による内部 dispatch も、ABI 載せ替え（Stage α）完了後は
  関数ポインタ直持ちに置き換わって消える。
- registry は構築時に一度だけ (act_id, operation_id) で manifest entry と登録を束ね、
  path → resolution の lookup 表（hash map）を作る。
  **escape 時の照合は 1 lookup**。現行の線形 path 走査と文字列 if は消える
  （v2 F2「perform 時の文字列比較はゼロ」への実質的な一歩。op id を request に
  載せる完全形は suspend tier / scheduler 工事と一緒にやる）。
- resolution 意味論は**現行と完全一致**:
  - Yulang handler に catch された perform はそもそも escape しない（mock 優先、変更なし）。
  - path が manifest のどの act にも属さない → `EscapedEffect`（本物のエラー）。
  - manifest の act に属するが、(a) op が manifest にない、(b) op に Rust 実装がない、
    (c) `native_host_operations_enabled = false` → **capability failure**
    （`UnsupportedHostCapability`、現行と同じ）。
  - (b) が新顔だが v2 F1「host が実装を登録していない場合は capability failure」の
    実装そのもの。
- 登録集合にあって manifest にない entry は到達不能な実装なので、テストで検出する
  （registry 構築時 debug_assert でもよい）。

### D6. signature は compiler の printer 出力

静的テーブルの手書き signature 文字列（"path -> result str io_err" 等）は廃止し、
宣言の型を public signature printer（public signature canary で既に契約固定済みの系）で
印字したものにする。期待値は「宣言 + printer の規則」から手で導出する。
印字形が手書き文字列と変わる場合、cli.rs / release-smoke の期待行は
**Stage 2 の切替 commit で一度だけ**更新する（差分はユーザが見える形で残す）。

### D7. column と hash は最初から入れる（消費はしない）

record-replay.md の時間制約要件（「後付けは全 host act の再配線になる」）への対応。

- `column` は D3 の決定的序数。record エントリの `(act_id, op_id)` を数値で引けるようにする。
- `hash` は record ファイル header の `manifest hash` にそのまま使える値。
- runtime の perform 列番号（sequence number）や分岐 id は**本工事の範囲外**
  （record モード導入時。record-replay.md 参照）。

## 3. 消費点の移行表

| 消費点 | 現在 | 移行後 |
|---|---|---|
| runtime dispatch | `RUNTIME_HOST_MANIFEST` を線形走査 | plan の manifest から構築した registry を 1 lookup |
| static route 分類 (lib.rs 2779) | `runtime_host_manifest_has_known_act`（静的関数） | build_plan が surface の manifest を直接引く。静的関数は削除 |
| `debug host-act-manifest` | 引数なし・静的テーブル印字 | std を compile して manifest を印字（std の収集は contract runner と同じ経路）。行形式は現行 + `column=` 追記 |
| host.rs unit tests | 静的テーブルの canary | 生成 manifest の canary に移設（op 数 / surface 集合 / path 一意性 / column 連番 / hash 安定性） |
| cli.rs / release-smoke.sh:96 | 静的テーブル由来の期待行 | 生成 manifest 由来の期待行（signature 印字形と column の差分を一度だけ手で導出して更新） |
| evidence-vm runtime unit tests（20606 付近） | 静的テーブル前提で registry 構築 | テスト用 manifest fixture helper（手組みの小さな manifest）を追加 |
| `from_labels` constructor 解決 | DumpLabels を走査 | **Stage 2 では現状維持**。Stage 3 で manifest の型表へ |

## 4. Stage 分割

### Stage 1 — 生成（挙動変更ゼロ）

1. `host` 修飾子（D2'）: parser の ActDecl → module map → compiled namespace へ
   host flag を通し、file.yu / console.yu の 2 宣言に付ける。非 host act の経路は不変。
2. `poly::host_manifest`（D3）: データ型 + 検証 + hash + symbol mangling。unit tests。
3. `infer::host_acts`（D2'）: surface override 表（raw-compat 2 件のみ）と、
   compiled namespace の host act 宣言から `HostActManifest` を組む生成関数。
   override と宣言の drift はここでエラー。
4. **等価性テスト**（yulang crate、infer と evidence-vm の両方が見える場所）:
   compiled std から生成した manifest と `RUNTIME_HOST_MANIFEST` が
   (act_id, operation_id, path, tier, surface) で一致する。
   signature は比較しない（D6 で正本が入れ替わるため）。

受け入れ: 全テスト green、既存挙動・既存出力の変化ゼロ。等価性テストが通る。

### Stage 2 — 切替と削除（前提: ABI 文書 Stage α 完了）

ABI 文書 Stage α（`BoundaryValue` / `HostOpFn` / 登録集合 API の導入と
file / console 実装の載せ替え、挙動不変）を先に済ませる。その上で:

1. `RuntimeEvidenceSurface` に manifest を載せ、`EvidenceVmPlan` が保持（D4）。
2. registry を plan manifest × 登録集合で構築（D5'）。
3. static route 分類を plan manifest 参照に切替、`runtime_host_manifest_has_known_act` 削除。
4. `debug host-act-manifest` を生成 manifest 印字に切替（std compile 経路）。
5. `RUNTIME_HOST_MANIFEST` / `RUNTIME_HOST_OPERATIONS` / `RUNTIME_HOST_ACTS` /
   path 定数 / 手書き signature / `RuntimeHostOperation` enum / Stage 1 等価性テストを削除。
   実装関数群は `HostOpFn` 形で存続（Stage α で載せ替え済み）。
6. cli.rs / release-smoke / host manifest canary の期待値を手で導出して更新。

受け入れ: §6 の Validation 全通過。evidence-vm から act の path 文字列定数が消えている。

### Stage 3 — constructor 型表（任意・別承認）

`RuntimeEvidenceHostConstructors::from_labels` の hardcoded label 走査を、
manifest 側の act 別型表（constructor label → DefId、plan 時解決）に置き換える。
v2 F4（manifest タグ表）の最初の一片で、ABI 文書 §3 の `CtorRef::Label`（v0 暫定）を
`CtorRef::Tag` へ移行させる正本になる（= ABI 文書 Stage γ の入口）。**着手前にユーザ確認**。
record/replay の wire encode がこの表の最初の本気の消費者になる予定。

## 5. 決めないこと（実装しないと分からないこと）

- hash 関数と直列化形式の選定。
- surface override 表と登録 API の Rust 上の正確な形（内容は D2' / ABI 文書に固定、綴りは自由）。
- registry lookup 表の内部表現。
- `debug host-act-manifest` の std 収集の正確な経路（contract runner と同じ系ならよい）。

## 6. Validation

既存 fixture の不変（意味論を変えていないことの証明）:

1. `console_unsupported_host` / `file_unsupported_host` / `file_text_unsupported_host` —
   capability failure の綴りが変わらない。
2. `console_mock_out_handler` — handler catch が registry より優先（escape しない）。
3. file-resource subset（`--host unsupported` 含む）全通過。
4. manifest 外の act の escape → `EscapedEffect`（unknown effect テスト現状維持）。

新規:

5. Stage 1 等価性テスト（Stage 2 で削除）。
6. override drift テスト: 宣言にない op を surface override が指す → 生成エラー。
7. 宣言追従テスト: `host` 修飾子付き act の全宣言 op が manifest に載る
   （file act = 8、console out = 1 の canary を生成側で維持）。
   `host` なしの act が manifest に載らないことも同時に固定する。
8. column 連番・順序決定性・hash 安定性・symbol 単射性（同じ std → 同じ hash）。
9. manifest にあり実装がない op → perform で capability failure（D5'-(b)）。
10. 登録集合にあり manifest にない entry → テストで fail。
11. file を使わないプログラムでも `debug host-act-manifest` が全 op を印字（D1）。

## 7. Rollback 条件

次のいずれかが起きたら、実装を進めず本文書へ戻る。

- 選んだ seam（compiled namespace / RuntimeEvidenceSurface）で act 宣言の全 op が
  見えないケースが出た（unit merge で欠けるなど）。
- capability failure と EscapedEffect の境界が既存 fixture のどれか一つでも変わった。
- signature の印字形が「宣言 + printer 規則からの手導出」で書き下せなかった。
- 期待値が実装出力と食い違い、期待値側を変えたくなった（手導出の原則を破る形で）。

---

*署名: この文書は Claude (Fable 5) が 2026-07-03 に、v2（2026-07-02-host-act-ffi-decisions.md）
§F2 の実装展開としてユーザの依頼により作成した。同日の改訂1 で、ユーザ指摘
「これは FFI ではない」を受けて 2026-07-03-host-abi-v0.md（host 実装 ABI 契約 v0）の
subset に改めた（D2'/D5' への置換、schema への symbol 追加）。意味論の決定は一切含まず、
すべて v2 と既存 fixture の意味論を保存する。ユーザの承認をもって authoritative とする。
変更にはユーザの明示的な承認を要する。 — Claude (Fable 5)*
