# file public buffer 境界 実装指示書（text_with pure mock parity の解消）

決定日: 2026-07-02（同日中に改訂3）
著者: Claude (Fable 5) — ユーザの依頼「text_with の mock 作業に指示書を用意する」に基づく。
状態: **指示書（authoritative・ユーザ承認済み）**。
改訂1 で §2 D-A / D-B をユーザ提案（buffer を専用 public act に置く）に沿って差し替え、
改訂2 で D-B″ の寿命違反検出（scoped / ambient の綴り分離）を加え、
改訂3 で「入れ子の text_with は正常な操作。path 不一致は外側へ転送」という
ユーザ決定を反映した（不一致=エラー案を置換）。D-A′ の path payload は
2026-07-02 にユーザ承認済み。
**Stage 0 から Stage 3 まで着手可**。停止条件（§3 / §5 / §8）だけが残るゲートである。

意味論の正本は次の 3 文書。本指示書はその実装順への導出であり、矛盾する場合は正本を優先する。

- [2026-07-02-resource-lifetime-decisions.md](2026-07-02-resource-lifetime-decisions.md)（v1: 寿命・トランザクション）
- [2026-07-02-host-act-ffi-decisions.md](2026-07-02-host-act-ffi-decisions.md)（v2: host act・tier・直交性）
- [spec/2026-07-02-io-resource-api.md](../../spec/2026-07-02-io-resource-api.md)（表面の型紙。file §1）

テスト期待値は正本の意味論から手で導出する。実装出力から逆算しない（.rules）。

## 0. 何が blocker だったか

`notes/bugs/file_text_with_mock_resource_lifetime_blocker.yu` の残存 blocker D:

- 現行 `std::io::file::text_with` は private snapshot 操作
  （`open_text_snapshot_raw` / `file_snapshot_get` / `file_snapshot_set` / `file_snapshot_commit`）
  に乗っており、外部 source の mock handler はこれを catch できない。
- public Yulang だけで書き直すと、handler-local `$buffer` の効果
  `&buffer#...` が `open_in` / `text_with` の public signature に漏れて
  型境界で拒否される（2026-07-02 に再確認済み。正しい拒否である）。

**解決の向き（ユーザ提案 2026-07-02）**: 漏れて怒られたのは「局所変数の状態
インスタンス」だからであって、**宣言された public act の効果が signature に
現れることには何の問題もない**。buffer への読み書きを専用の public act に
すれば、view の型は公開名だけで書ける。

## 1. 目標アーキテクチャ

spec §1 の型紙どおり: **host act `file` は最小のまま、buffer + commit は純 Yulang**。
`file` act の操作一覧は spec §1 と完全一致させ、**操作を追加しない**。

buffer は専用の public act に置く:

```yu
pub act file_buffer:                       -- 綴り provisional
    pub get: path -> str                   -- scoped 専用。host は決して登録しない
    pub set: (path, str) -> ()
    pub ambient_get: path -> str           -- unscoped view 専用。host が登録する
    pub ambient_set: (path, str) -> ()
```

これは `std::control::var` の `var 't`（get/set の state 形 act）と同じ骨格である。
`act file_buffer = var str` の act copy でほぼ書けるが、**payload に path を
一枚だけ持たせる**（理由は §2 D-A′）ことと、**scoped / unscoped で操作の
綴りを分ける**（理由は §2 D-B″ の寿命違反検出）ため独立宣言とする。

各形の「誰が catch するか」:

| 形 | buffer 操作 | file::load / store / meta | commit の時点 |
|---|---|---|---|
| scoped `text_with` | view は `get` / `set` を使う。**最寄りのトランザクション handler** が path を見て、自分宛なら処理、違えば**外側へ転送**。入れ子の別ファイル編集は普通に動く（下記 D-B″） | host（または mock） | scope exit で `store`。abort なら store しない = rollback |
| unscoped `file::text p` | view は `ambient_get` / `ambient_set` を使い、text_with の handler を素通りして **host に落ちる**（v2 F1 そのもの）。host が path ごとの buffer 台帳を保持 | host | host handler の extent 終端（プログラム終端）で write-back |
| pure mock | source handler は **`file` act と ambient 操作を** catch。scoped `get` / `set` は std の handler が内側で discharge するので mock には届かない。backing は `list (path, str)` の assoc list | 同左 | mock handler の return 節 = discharge |
| **scope の外へ逃げた scoped view** | `get` / `set` が全 handler を転送で通り抜けても受け手がなく、host にも登録がない → **capability 層の構造化エラー**（下記 D-B″） | — | 起きない（寿命違反として検出される） |

`text_with` の本体は、**実証済みの形の組み合わせ**である:

- 状態 threading handler は `lib/std/control/var.yu` の `run`（3 行）と、
  `tests/yulang/regressions/runtime/file_mock_text_with_function_commit.yu` の
  `text_with_mock` が前例。
- ref view over act ops は `var.yu` の `var_ref` と現行 `open_text` が前例。

```yu
-- text_with の骨子（綴りは provisional。期待値導出の根拠として使う）
pub text_with(p: path, f) =
    my view = ref {
        get: \() -> file_buffer::get p,
        update_effect: \() ->
            file_buffer::set (p, ref_update::update (file_buffer::get p))
    }
    my run(buffer, x) = catch x:
        file_buffer::get q, k ->
            if q == p: run buffer: k buffer
            else: run buffer: k (file_buffer::get q)       -- 自分宛でない → 外側へ転送
        file_buffer::set (q, next), k ->
            if q == p: run next: k()
            else: run buffer: k (file_buffer::set (q, next))  -- 同上
        v -> (v, buffer)
    my initial = <file::load p を unwrap（io_err throw）>
    my (result, final) = run initial: f view
    <file::store (p, final) を unwrap>
    result
```

view の型は `ref '[file_buffer] str`、callback は
`(ref '[file_buffer] str) -> [file_buffer; e] 'a`、`text_with` 全体は
`[file; io_err; e] 'a`（file_buffer は text_with 自身が discharge する）。
spec §1 の `ref '[file] str` という綴りはこれに合わせて修正する
（spec の綴りは provisional であり、意味論は不変。spec 側に註記を入れる）。

multi-shot（undet / junction）の分岐独立 buffer は、handler 状態が純粋な
継続 threading である時点で**構造的に無料**である（v1 決定2 と State 純粋性の帰結）。
scoped 形に Rust 側の分岐 fork 実装は要らない。到達順 last-write-wins は
各分岐の scope exit が順に `store` することで成立する。

能力の粒度について一行: `file_buffer` は `file` とセットで grant する
（v2「能力の単位は act」。片方だけの grant は意味を持たないと文書に明記する）。

## 2. 本指示書が新たに決めること

- **D-A′（改訂1。ユーザ提案採用）**: buffer 操作は `file` act に足さず、
  **専用の public act `file_buffer`** に置く。`file` の act surface は
  spec §1 と完全一致のまま保たれる。
  - ユーザ原案（`act mock_file = state` 相当の payload なし get/set）からの
    変更は **path payload 一枚だけ**。理由は三つ:
    (1) unscoped 形では操作が host に落ちるため、host が「どのファイルの
    buffer か」を知る手段が payload 以外にない。
    (2) `my &a = file::text "a"` と `my &b = file::text "b"` の同時使用という
    ごく普通のコードが、payload なしでは区別できない。
    (3) record/replay（置き土産①）の漏斗として、操作が対象ファイルを
    自己記述する。
  - scoped + mock だけなら payload なしでも書ける。Stage 2（native unscoped）で
    必ず壁に当たるため先に入れておく、という順序の判断である。
- **D-B″（改訂1〜3）**: `file_session` という値・概念は本 slice から**削除**する。
  宛名として必要な情報は path だけだった。spec の `open(p): file_session` /
  `s.raw` 系（session を第一級値として持ち回る API）は raw 層を実装する
  将来 slice で戻す。
  - **入れ子は正常な操作である**（改訂3。ユーザ決定 2026-07-02）:
    ファイル A を編集している途中でファイル B を編集するのは普通のコードで
    あり、動的エラーにしない。text_with の handler は path を見て、
    **自分宛なら処理、違えば操作を外側へ転送する**（arm 内で同じ操作を
    再 perform して k に返す。§1 の骨子参照）。宛先探索は代数的エフェクトの
    伝播そのものであり、追加の機構は要らない。
  - **寿命違反（view の持ち出し）の検出**（改訂2〜3。規範例はユーザ提供）:
    view を `text_with` の外へ不用意に持ち出して書き込むのは v1 決定1
    （寿命 = handler extent）への違反であり、これは黙って通さない。
    転送の連鎖が全 handler を通り抜けた scoped `get` / `set` は、
    **host が決して登録しない**操作なので capability 層の構造化エラーに
    落ちる（unscoped view は別綴りの `ambient_get` / `ambient_set` を使う
    ため誤検出しない）。つまり**エラーになるのは「本当に受け手がいない」
    場合だけ**であり、正常な入れ子とは構造的に区別される。token も
    世代番号も使わない。v2 F7「安く検出できるものだけ動的エラー」の範囲。
  - 同一 path の `text_with` の入れ子だけは、内側の handler が「外側の view」と
    「自分の view」を区別できないため**検出できない**。ここは正直に
    **unspecified** として contract 文書に一行記録する（観測上は
    「内側のトランザクションに合流する」形になるが、それを仕様とは呼ばない）。
  - **Stage 0 の最初の probe を転送にする**: handler arm 内での再 perform が
    「外側の handler へ伝播する」ことは本設計の前提である。Stage 0 では
    text_with 本体より先に、この転送だけの最小 reduction を書いて確かめる。
    伝播しない意味論だった場合は §3 の停止条件に従い、回避策を積まずに
    停止してユーザに報告する。
- **D-C**: `io_err` に `failed (path, str)` を追加（spec §1）。`file_meta` は
  `kind` / `size` / `readonly` までとし、`modified: opt instant` は
  **instant 実装後にこの指示書へ戻ってきて追加する**（除外ではなく延期。
  spec 側に「instant 待ち」と註記する）。instant の仕様は
  [spec/2026-07-02-instant.md](../../spec/2026-07-02-instant.md) として確定済み。
  size も native 実装が重ければ同様に延期してよい。
- **D-D**: 旧 private snapshot 操作と Rust 側 `FileSnapshots` 機構は、
  Stage 2 の parity 完了後に削除する。ただし multi-shot 継続を跨ぐ snapshot
  運搬の Rust 実装は、**unscoped native の path ごとの buffer 台帳として改名再利用**
  してよい（host handler のパラメータ = 外部状態の帳簿。v2 に整合）。

## 3. Stage 0 — 純 Yulang の新 surface（Rust 変更なし）

1. `lib/std/io/file.yu` に §1 の `file_buffer` act・新 `text_with` /
   `text` / `read_text` / `meta` を実装する。`file` act は spec §1 の操作へ
   置き換える（`host act` 綴りが未実装の間は `pub act` でよい）。
   旧 private snapshot 操作と `open_text` / `open_in` は**まだ消さない**
   （Stage 2 まで並存。公開名は新実装へ向ける）。
2. int エラーコードの新規使用は禁止。新操作は `result` / `io_err` /
   `file_meta` を直接運ぶ（既存 `err_from_code` の削除は Stage 2）。
3. 検証は `--host unsupported` + source mock handler のみで行う。
   この段階で native は一切触らない。
4. public signature 検査: `dump-poly-std-in std.io.file` に `#...` /
   `AllExcept` / handler-local effect が現れないこと。`text_with` の型が
   §1 の形（`file_buffer` は callback 側にだけ現れ、結果 row からは消える）に
   一致すること。

**停止条件**: `catch` の意味論で §1 の骨子が表現できない形が出た場合
（特に **handler arm 内の再 perform が外側へ伝播しない**場合。D-B″ の
最小 probe を最初に行うこと）、または public signature にどうしても
局所効果が残る場合は、**回避策を積まずに停止してユーザに報告する**。

**移行窓の規律（native が赤くなる期間の扱い）**: 公開名（`meta` /
`read_text` / `write_text` / `text_with` / `text`）を新実装へ向けた時点から
Stage 2 の registry 登録が終わるまで、**native の file-resource case は
失敗するのが想定どおり**である。この期間について:

- native case の期待値・タグ・manifest を**一切触らない**。赤は移行の印で
  あって、修正対象ではない。
- 公開名の切り替えと Stage 2 の registry 登録は**同じ push で完了させる**
  （中間状態のまま push しない）。push 前の release smoke / native gate は
  この工事の完了判定として最後に回す。
- Stage 0〜1 の間のローカル検証は `--host unsupported` + mock fixture だけを
  green の基準にする。

## 4. Stage 1 — 必須 fixture 6 件（contract box + 入れ子）

`notes/todo/contract-v1-file-resource-priority.md` の必須 fixture を、
**新 surface の上で、期待値を意味論から手で導出して**書く。

1. `file_text_with_commit` — scope exit で backing が更新される。
2. `file_text_with_rollback_on_error` — effect abort で backing 無傷。
3. `file_text_with_undet_last_write_wins` — 分岐ごと独立 buffer、到達順
   last-write-wins。各分岐は entry 時の snapshot を読む。
4. `file_text_unscoped_handler_discharge` — `my &t = file::text p` の unscoped 形。
   mock handler の return 節（= handler extent 終端）で commit が観測される。
5. `file_text_mock_matches_native_shape` — **同一プログラム本文**を mock handler と
   native host で走らせ、public 観測が一致する（native 側の有効化は Stage 2。
   case 自体を Stage 2 で追加し、pending の placeholder を置かない）。
6. `file_text_with_nested_cross_file` — （改訂3 で追加。ユーザ決定）A の
   `text_with` の中で B の `text_with` を開き、内側から**両方の** view を
   読み書きする。それぞれの scope exit でそれぞれの backing に commit される。
   内側の abort は B だけを rollback し、A には影響しない。

tag は box の方針どおり: `file-resource` / `resource-lifetime` / `mock-host`
（native 側は `host.native`）。`stable-core` とは混ぜない。

mock の backing は `list (path, str)` の assoc list とする。
**map / HashMap / dict を新設しない**（fixture のファイル数は数個であり、
純粋値の assoc list が multi-shot 分岐独立と最も整合する）。

## 5. Stage 2 — native 載せ替えと int コード全廃

1. registry（`evidence-vm/src/runtime/host.rs`）に `file` の新操作と
   `file_buffer::ambient_get / ambient_set` を**名前ベース**で登録する
   （v2 F2。タグ番号ハードコード禁止）。tier は全て sync。
   **`file_buffer::get / set` は manifest に載るが host 実装を登録しない**
   （D-B″ の寿命違反検出の要。registry の「known-act missing op」分類が
   そのまま構造化エラーの経路になる）。
2. 越境データ構築のため、manifest タグ表の**最小 slice** を実装する:
   対象は `result` / `io_err` / `file_kind` / `file_meta` の 4 型に限定。
   汎用機構は要らないが、名前→タグ解決は manifest 経由とする。
   **新しい private act 操作を bridge として追加することは禁止**。
3. unscoped 形の buffer 台帳を Rust 側に実装する（D-D の改名再利用。
   key は path）。プログラム終端の write-back は host handler の return 節の
   帳簿処理として書く。
4. `err_from_code` / `kind_from_code` / int コード / 旧 private snapshot 操作 /
   `open_text_snapshot_raw` 系を削除する。
5. 既存 native contract（commit / rollback / nondet branch snapshots / meta /
   unsupported host）が**期待値変更なしで**通ること。期待値の変更が必要に
   見えたら停止してユーザに確認する。
6. `file_text_mock_matches_native_shape` を有効化する。

## 6. Stage 3 — 後始末と evidence

- `notes/bugs/file_text_with_mock_resource_lifetime_blocker.yu` を閉じる
  （resolved 記録に変える。削除はしない）。
- 暫定 helper 系 contract（`file_mock_text_with_function_commit` /
  `..._rollback_on_error` / `..._nondet_branch_buffers` /
  `file_mock_public_ref_view_commit`）は、**言語機能の contract として残す**が、
  evidence 文書上「file-resource の中心証拠は Stage 1 の 6 件」へ役割を移す。
- `docs/language/contract-v1-file-evidence.md` / `docs/status.md` /
  `notes/todo/contract-v1-file-resource-priority.md` を更新する。
- release smoke の file-resource subset に Stage 1 の 6 件を入れる。

## 7. やらないこと

- private snapshot 操作を public 化しない（正本の却下済み事項）。
- `close` / `flush` / `save` 相当を足さない（v1 決定1〜2）。
- `file` act に操作を追加しない（spec §1 の act surface を保つ）。
- map / dict データ構造を std に新設しない。
- effect row の existential 隠蔽（private tail の言語機能化）に手を出さない。
  それは研究相談（row subtraction）の主題であり、本工事は D-A′ により不要にしてある。
- `load_bytes` / `store_bytes` / `bytes_with` / encoding 指定は本 slice の外
  （spec にはあるが fixture 6 件に不要。follow-up とする）。
- serve / in-process driver に進まない（structured-concurrency 決定文書が先）。
- file-resource の周辺 case（mock canary 等）を本工事の代わりに追加しない。
  **本指示書の進捗は Stage 1 の 6 fixture と Stage 2 の削除項目でだけ測る。**

## 8. Rollback 条件

- 型紙の四層（act / session / view / raw）から外れる操作を足したくなったら停止。
- Stage 0 の停止条件に当たったら、blocker note に**一回だけ**記録して停止
  （narrow 系の記録 commit を反復しない）。
- 期待値を実装出力から逆算しない。逆算したくなったら、それは実装が意味論に
  達していない印であり、実装側を直すか停止する。

---

*署名: この指示書は Claude (Fable 5) が 2026-07-02 に、ユーザの依頼を受けて
正本 2 文書と io-resource-api 仕様から導出した実装順である。改訂1 の D-A′ の
骨格（buffer を専用 public act に置く）はユーザ提案、path payload は Claude の追加で 2026-07-02 にユーザ承認済み。改訂2 の
寿命違反の規範例（view を text_with の外へ持ち出して書き込む）はユーザ提供である。
ChatGPT / Codex が生成した文書と矛盾する場合、本指示書と正本を優先する。
— Claude (Fable 5)*
