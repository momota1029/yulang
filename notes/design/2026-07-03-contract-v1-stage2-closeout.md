# Contract v1 Stage 2 closeout（typed ambient io_err / raw-compat 退役）

決定日: 2026-07-03
著者: Claude (Fable 5)
状態: **仕様（authoritative）**。2026-07-03 ユーザ承認済み。
同日、D4（ambient 操作の `file` act への統合、ユーザ決定）を追補。
`.rules` の「設計文書の正本」節に登録済み。

この文書は、Contract v1: File Resource の残り blocker 2 件を閉じるための
仕様と実装指示を固定する。対象は
`docs/language/contract-v1-file-evidence.md` の Known Blockers 節にある:

1. native unscoped ambient read/write failures を typed `io_err` にする
2. `raw-compat` snapshot operations を public session boundary へ置き換えるか退役させる

意味論の正本は次の 3 文書であり、本文書はその Stage 2 適用である。

- [spec/2026-07-02-io-resource-api.md](../../spec/2026-07-02-io-resource-api.md)（API 表面）
- [2026-07-02-resource-lifetime-decisions.md](2026-07-02-resource-lifetime-decisions.md)（寿命・トランザクション）
- [2026-07-02-host-act-ffi-decisions.md](2026-07-02-host-act-ffi-decisions.md)（host act・二層エラー）

## 0. 決定点（D1〜D4）

### D1: unscoped `file::text` の失敗点は「作成時」に移す（eager touch）

io-resource spec §1 の型はもともとこう書かれている:

```yu
pub text(p: str): [file; io_err] ref '[file] str
```

`io_err` は **`text` の呼び出し行**に付き、返る ref の row には付かない。
つまり spec は最初から「失敗は lens 作成時、lens アクセスは buffer への
不可失敗 view」と決めている。現在の実装（lazy に ref を返し、最初の
`$x` 読みで native read が走って落ちる）のほうが spec からずれていた。

これを実装に写すため、ambient 操作を touch / get / set の三操作に割る。
置き場所は D4 により `file` act 内である（`file_buffer` act は消滅）:

```yu
pub act file:
    -- 既存の protocol 操作: load / store / meta（変更なし）
    pub ambient_touch: path -> result unit io_err   -- entry snapshot 読み込み。ledger 登録
    pub ambient_get: path -> str                    -- ledger hit（touch 済み前提）
    pub ambient_set: (path, str) -> unit            -- ledger 更新
```

`text` 本体は touch を unwrap してから ref を組む:

```yu
pub text(path: path): ref '[file] str =
    unwrap_io (file::ambient_touch path)
    ref {
        get: \() -> file::ambient_get path,
        update_effect: \() ->
            file::ambient_set (
                path,
                ref_update::update (file::ambient_get path)
            )
    }
```

**row leak を回避できる根拠**: 以前の result-wrapping 試行が row constraint を
漏らしたのは、unwrap（= `io_err` の throw）を **ref の closure の中**に置いた
からである。closure の row は公開 `ref` 型の一部として投影される。
本形では unwrap は `text` の**関数本体**にあり、これは `text_with` が
`unwrap_io (file::load path)` で既に通している形そのもの
（public signature canary 通過済みの前例）である。ref closure が行う操作は
不可失敗の `ambient_get` / `ambient_set` だけなので、ref の row は
`'[file]` のまま閉じ、`text` の公開型は spec §1 の綴りと完全一致する。

**missing パスへの `text` は `io_err::not_found`**。`text` は既存ファイルへの
snapshot lens であり、create 意味論は持たない。新規作成したい場合は
`write_text` を先に呼ぶ（create-on-text が欲しくなったら別綴りとして
spec 側で検討する。黙って空文字 buffer で始めることはしない —
missing read = typed failure という既存 evidence と矛盾するため）。

意味論上も一貫する: v1 決定2 の「scope entry で読む」の unscoped 対応物は
「作成点で読む」である。同一 path への二度目の `text` は ledger hit
（buffer 共有。ambient の定義どおり）。

### D2: handler-extent 終端 flush の失敗は structured runtime error のまま

discharge flush（プログラム正常終了時の dirty buffer 書き戻し）が失敗した
時点では、それを catch できるユーザ継続がもう存在しない。ここを typed
`io_err` にすることは原理的にできない。よって:

- flush 失敗は `yulang.host-io-error`（structured runtime error）に**残す**。
- これは手抜きではなく **unscoped 形の意味論上の非対称**として文書化する:
  scope を手放した代償として、書き戻し失敗は catch できない。
  catch したければ scoped 形（`text_with`）を使う。
- 同様に、`file::text` を経ずに untouched な path へ `ambient_get` /
  `ambient_set` を直接 perform した場合（out-of-protocol 使用）は、
  native runtime が暗黙 touch を行い、その失敗は `yulang.host-io-error` に
  分類する。typed `io_err` の保証は `file::text` 経由に対してだけ与える。

`ambient_set` は ledger 更新であり native では失敗しないため、
result 型にしない（失敗は flush 時点に集約され、上記の分類に従う）。
mock host が書き込み拒否を表現したい場合は、自前 handler の touch arm か
自前 discharge で typed に表現できるので、act 側を歪める必要はない。

### D3: snapshot 系 raw-compat は「退役」。file_session は post-v1

blocker 2 の「置き換えるか退役させるか」は**退役**と決める。

- 退役対象: `file` act の private 操作 8 件
  （`open_text_raw` / `file_get` / `file_set` / `file_flush` /
  `open_text_snapshot_raw` / `file_snapshot_get` / `file_snapshot_set` /
  `file_snapshot_commit`）と、その上の public helper 3 件
  （`open_text` / `open` / `open_in`）、および private `open_text_snapshot`。
- 理由:
  - `open_in` の snapshot-commit 意味論は、現行 `text_with` の
    load / λ / store protocol が完全に置き換え済みで、冗長である。
  - 現行 `open` は `ref '[file] str` を返すが、spec §1 の `open` は
    `file_session` を返す。綴りが将来と衝突し、意味論も一致しない。
    残すほど Contract v1 の中心 API が濁る。
  - 優先順位メモの既定「private snapshot helpers must not be made public
    just to satisfy this」に対し、public 化しない以上、残す理由は
    互換窓しかなく、その互換窓を使う契約はもう無い。
- **file_session（spec §1 の `open` / `open_with` / `s.text` / `s.raw`）は
  Contract v1 の完成条件に含めない。** post-v1 の standard-api slice として
  spec から実装する。`open` の綴りはそのために空けておく。
- `read_at` / `write_at` は**残す**。typed result 化済みで、将来 `s.raw` に
  畳まれる種であり、`raw-compat` surface タグと provisional range 意味論の
  注記が既に正直に付いている。Contract v1 の中心とは呼ばない（現状どおり）。

### D4: `file_buffer` act は `file` act に統合する（2026-07-03 ユーザ決定・追補）

ambient 三操作は独立の `file_buffer` act ではなく、`file` act 内の
`ambient_touch` / `ambient_get` / `ambient_set` とする。
`file_buffer` という act 名は消滅する。

- 根拠（ユーザの言語設計判断）: いずれもファイル操作であり、LL としての
  簡潔さとユーザフレンドリーな型を優先する。row は常に `[file]` 一つになり、
  `text` の公開型は spec §1 の綴り `[file; io_err] ref '[file] str` と
  **完全一致**する（provisional spelling 差分の消滅）。
- ambient であることの可視性は、row 名ではなく操作名の `ambient_` 接頭辞で
  保つ。失敗しない操作が素の型を持つことは `meta` に前例がある。
- **受け入れたトレードオフ**: `file` を scoped に catch する部分 mock の中で
  unscoped `text` 由来の ref が使われた場合、その ambient 操作は mock 側に
  routing される（arm があれば誤 routing、なければ escape）。これは型では
  検出されない。緩和策: (a) contract fixture は使う操作の arm を全部書く、
  (b) 全操作を assoc-list ledger で提供する complete mock helper
  （`with_mock_file(backing, body)` 相当）を std に置くことを Stage B 後の
  任意項目として推奨する。
- 却下した代替案: 分離維持 + 純 Yulang `with_file_buffers` 委譲 wrapper
  （spec §2 の ambient channel 形の file 版）。mock の問題は解けるが
  row の二重性（`[file, file_buffer]`）が残るため、ユーザが統合を選んだ。

## 1. エラー分類の全体表（file 系の到達点）

| 事象 | 層 | 観測 |
|---|---|---|
| unsupported host / handler 未登録 | capability | `UnsupportedHostCapability`（現状維持） |
| `file::load` / `store` / helpers の操作失敗 | operation | typed `io_err`（済み） |
| `file::text` 作成時の missing / denied / invalid | operation | typed `io_err`（**D1 で新規**） |
| touch 済み ledger への get / set | — | 失敗しない |
| untouched path への直接 `ambient_get` / `ambient_set` | out-of-protocol | `yulang.host-io-error`（D2） |
| discharge flush 失敗 | 資源終端 | `yulang.host-io-error`（D2） |

int エラーコードはどこにも存在しない（達成済みの不変条件を維持）。

## 2. Stage A: raw-compat snapshot 退役（先にやる）

削除が主体で、Stage B の manifest / canary 作業面を先に狭くする。

作業一覧:

1. `lib/std/io/file.yu`: D3 の退役対象を削除。`file_handle` への参照が
   これで消えるなら型ごと削除する。
2. `crates/evidence-vm/src/runtime/host.rs`:
   - `RuntimeHostOperation` の該当 variant と native 実装、handle table を削除。
   - `RUNTIME_HOST_OPERATIONS` から該当 spec entry を削除。
   - manifest unit tests（`raw-compat` surface の期待集合、
     「contract host ops should cover …」）を新しい表に合わせて更新する。
     更新後の `RawCompatibility` surface は `read_at` / `write_at` 系だけになる。
3. `tests/yulang/cases.toml`: `std_file_open_text_public_signature` /
   `std_file_open_public_signature` / `std_file_open_in_public_signature` を
   削除。runtime case で退役 helper を使うものがあれば case ごと削除する
   （他の case の期待値は触らない）。
4. `crates/yulang/tests/cli.rs`: 退役操作を参照する期待値を更新。
   `debug host-act-manifest` の release-smoke 期待行も同様。
5. docs: `contract-v1-file-evidence.md`（blocker 2 を closed に）、
   `docs/status.md`、`tests/yulang/README.md`（`raw-compat` の説明を
   range helpers のみに）を更新。

## 3. Stage B: typed ambient io_err（D1 / D2 の実装)

作業一覧:

1. `lib/std/io/file.yu`: `file_buffer` act を削除し、ambient 三操作を
   `file` act に追加（D4）、`text` を D1 の本体に書き換える。
2. `crates/evidence-vm/src/runtime/host.rs`:
   - `RuntimeHostAct::FileBuffer` を廃止し、ambient 操作を `File` act 配下へ
     移す（path は `std.io.file.file.ambient_*`）。manifest / manifest unit
     test / `debug host-act-manifest` の期待値も追随させる。
   - `ambient_touch` を追加（`path -> result unit io_err`、surface =
     `Contract`）。native 実装は「読んで ledger に登録。io 失敗を
     `io_err` コンストラクタへ分類」— 分類規則は
     `file::load` の既存分類（`not_found` / `denied` / `invalid_path` /
     `failed`）と同一関数を使う。
   - `ambient_get` / `ambient_set` は ledger hit / ledger 更新のまま。
     untouched path への直接 perform は暗黙 touch し、失敗を
     `RuntimeEvidenceRunError::HostIoError` に分類する（D2）。
   - discharge flush の失敗分類は現状（`HostIoError`）を維持する。
3. fixture（期待値は本文書 §1 の表から手で導出する）:
   - `file_text_native_missing_typed_io_err`: native、missing path への
     `file::text` が作成点で `io_err::not_found` を typed に報告する。
     既存 `file_text_native_missing_host_io_error` はこの case に**置換**
     される（missing read の期待値が structured → typed に変わるため）。
   - `file_ambient_get_untouched_missing_host_io_error`: native、
     `file_buffer::ambient_get` を直接 perform した out-of-protocol 使用が
     `yulang.host-io-error` になる。structured 側の coverage をここへ移す。
   - `file_text_mock_ambient_typed_not_found`: `--host unsupported` +
     source handler が `ambient_touch` arm で `result::err (io_err::not_found …)`
     を返し、呼び出し側が typed に catch できる。
   - `std_file_text_public_signature`: `text` の公開型を正確に固定する
     （`[file, io_err]` row + `ref '[file] str` — spec §1 の綴りと一致。
     `#...` / `AllExcept` / `Any` / `Unknown` を拒否する）。
   - 既存 `file_text_unscoped_native_handler_extent` /
     `file_text_unsupported_host` は意味を変えずに通り続けること
     （touch の追加と D4 の act 統合で変わる分 — 期待 signature と
     capability failure payload の act / 操作 id — は本文書から再導出する）。
   - discharge flush 失敗の native .yu case は、プログラム内から backing
     path を flush までに壊す手段が（raw 退役後は）無いため要求しない。
     代わりに evidence-vm の Rust unit test で「flush 失敗 →
     `HostIoError`」の分類を固定する。
4. spec 修正（D4 の反映）: `spec/2026-07-02-io-resource-api.md` §1 の
   host act `file` block へ ambient 三操作を追記する（本文書の追補と同時に
   適用済み。追補注記つき）。

## 4. 受け入れゲート

Stage ごとに、リポジトリの既存の順序で:

```bash
cargo fmt --all -- --check
cargo check -q -p evidence-vm -p yulang
cargo run -q -p yulang -- --std-root lib contract --contract file-resource tests/yulang/cases.toml
cargo test -q -p yulang --test cli -- --test-threads=1   # manifest / smoke 期待値
scripts/release-smoke.sh <binary>                         # focused file-resource set 更新込み
```

archive smoke（packaged binary + bundled std）は Stage B 完了後に一回で良い。
両 Stage 完了で `contract-v1-file-evidence.md` の Known Blockers は空になり、
Contract v1 は「file_session を含まない」定義（D3）の下で close へ進む。

## 5. Do not

- scoped `file_buffer` 操作・transfer arm・`same_path` 検査・raw snapshot の
  public 化を復活させない（evidence 文書の既存規則）。
- public signature canary を弱めて通さない。投影が row を漏らすなら、
  それは projection / infer 側の欠陥として報告し、実装を止める。
- `text_with` の 4 行 protocol と、spec §1 の protocol 操作
  （`load` / `store` / `meta`）の形を触らない
  （D4 で足すのは ambient 三操作だけ）。
- file_session をこの工事に混ぜない（post-v1）。
- fixture の期待値を実装出力から逆算しない。

## 6. Rollback 条件

- D1 の形にしても `text` の public signature に private row constraint が
  漏れる場合: canary をいじらず実装を止め、漏れの最小再現を
  `notes/bugs/` に置いてユーザへ報告する。
- eager touch が既存 Stage 1 protocol fixture のどれかの期待値変更を
  要求する場合: 本文書の適用を止めて正本 3 文書へ戻る
  （§3 で許した signature 再導出を除く）。
- 退役対象の操作に、テスト以外の生きた利用箇所が見つかった場合:
  削除せずユーザに確認する。

---

*署名: 本文書は Claude (Fable 5) が 2026-07-03 に、Contract v1 の残り
blocker 2 件（typed ambient io_err / raw-compat 処遇)を閉じるために起草した。
D1 は spec/2026-07-02-io-resource-api.md §1 の既定型への整合、D2 と D3 は
新規決定である。2026-07-03 にユーザが D1〜D3 を承認した。同日、ユーザの
設計判断（すべてファイル操作である・LL としての簡潔さと型のユーザ
フレンドリーさを優先）により D4 を追補し、ambient 操作は `file` act へ
統合された。
ChatGPT / Codex が生成した文書と矛盾する場合、本文書を優先する。
変更にはユーザの明示的な承認を要する。 — Claude (Fable 5)*
