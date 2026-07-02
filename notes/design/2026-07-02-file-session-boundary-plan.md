# file public buffer 境界 実装指示書（text_with pure mock parity の解消）

決定日: 2026-07-02（同日中に改訂4）
著者: Claude (Fable 5) — ユーザの依頼「text_with の mock 作業に指示書を用意する」に基づく。
状態: **指示書（authoritative・ユーザ承認済み）**。
改訂履歴: 改訂1 = buffer を専用 public act に（ユーザ提案）。改訂2 = scoped/ambient
綴り分離。改訂3 = 入れ子は正常・転送方式。**改訂4 = 型漏れ問題の最終解決として
scoped 側を state-passing プロトコルへ全面転換（ユーザとの設計相談で合意）。
file_buffer の scoped 操作・転送・same_path 検査は撤去**。
**Stage 0 から Stage 3 まで着手可**。停止条件（§3 / §5 / §8）だけが残るゲートである。

意味論の正本は次の 3 文書。本指示書はその実装順への導出であり、矛盾する場合は正本を優先する。

- [2026-07-02-resource-lifetime-decisions.md](2026-07-02-resource-lifetime-decisions.md)（v1: 寿命・トランザクション）
- [2026-07-02-host-act-ffi-decisions.md](2026-07-02-host-act-ffi-decisions.md)（v2: host act・tier・直交性）
- [spec/2026-07-02-io-resource-api.md](../../spec/2026-07-02-io-resource-api.md)（表面の型紙。file §1。
  callback の綴りは本指示書 §1 が置換する）

関連: [\my &x 束縛と &do の design note](2026-07-02-my-binder-sugar.md)（糖衣。**本 slice の外**）。

テスト期待値は正本の意味論から手で導出する。実装出力から逆算しない（.rules）。

## 0. なぜ改訂4 に至ったか（型漏れの三竦み）

- **公開 act + path 動的分岐**（改訂1〜3）: 入れ子対応の転送 arm が text_with
  自身の row に `file_buffer` を載せ、**全呼び出し元の型へ静的に伝播する**。
  動的には正しいが型が汚れる（ユーザ指摘 2026-07-02）。
- **局所変数（`my $buffer`）**: instance ごとに型が分かれ入れ子も精密だが、
  発話不能な instance 名が public signature を渡れない（元の blocker）。
- **結論**: 名前を隠す（存在型）か、名前が境界を渡らない形にする。存在型は
  研究相談トラック（row subtraction / 06-23 private tail projection の延長）。
  出荷は後者 = **state-passing プロトコル**で行う。

## 1. 目標アーキテクチャ（改訂4）

spec §1 の型紙どおり: **host act `file` は最小のまま**。操作を追加しない。

### scoped `text_with` — state-passing プロトコル

callback は「ref を受ける関数」ではなく **初期値を受けて (結果, 最終値) を返す関数**:

```yu
-- f : str -> [e] ('a, str)
pub text_with(p: path, f): [file; io_err; e] 'a =
    my initial = unwrap_io (file::load p)
    my (result, final) = f initial
    unwrap_io (file::store (p, final))
    result
```

これで全部である。handler なし・専用 act なし・転送なし。buffer は
**呼び出し側の λ の中の普通の局所変数**として生きる:

```yu
-- 糖衣が入るまでの手書き形（fixture はこれで書く）
file::text_with p: \t0 ->
    my $text = t0
    my before = $text
    &text = before + "!"
    ((before, $text), $text)      -- (body の結果, 最終 buffer)

-- 糖衣が入った後（notes/design/2026-07-02-my-binder-sugar.md）
file::text_with p: \my &text ->
    my before = $text
    &text = before + "!"
    (before, $text)
```

型漏れが消える理由: 発話不能な instance 効果は text_with の**行多相変数 `e`
への具体化**としてだけ流れ、どの公開スキームにも綴られない（貧者の存在型）。

### 各形の整理

| 形 | 状態の置き場所 | file act の使用 | commit / rollback |
|---|---|---|---|
| scoped `text_with` | **呼び出し側 λ 内の局所変数**（純粋スレッディング） | 入口 `load` 一回・出口 `store` 一回 | λ が値を返せば store。abort で λ が返らなければ store されない = rollback |
| unscoped `file::text p` | host の path ごとの台帳（ambient 操作） | 台帳の読み書き + extent 終端の write-back | handler extent（プログラム）終端で commit |
| pure mock | mock handler が `file` act と ambient 操作を catch。backing は `list (path, str)` の assoc list | 同左 | mock handler の return 節 = discharge |

```yu
pub act file_buffer:                       -- 綴り provisional。unscoped 専用に縮小
    pub ambient_get: path -> str           -- host が登録する
    pub ambient_set: (path, str) -> unit
```

**改訂3 までの scoped `get` / `set`・転送・`same_path` 検査は実装しない**
（作りかけがあれば撤去する）。

### 意味論の帰結（すべて機構ゼロで成立）

- **入れ子は自然に正しい**: 外側の `$text` を内側の text_with の λ から触るのは
  ただの字句閉包で、instance が別だから混線しない。型は行多相 `e` を通る。
- **rollback**: abort すれば λ が返らず、出口の `store` に到達しない。
- **undet 分岐独立**: 局所変数の純粋スレッディングそのもの（v1 決定2）。
  分岐ごとに λ が返り、分岐ごとに store、到達順 last-write-wins。
- **view の持ち出し**: `&text =` を閉包に包んで scope 後に呼べば、handler の
  消えた instance への操作 = **EscapedEffect 本来の意味のエラー**（v2 F2）。
  host 非登録トリックは不要になった。
- **同一 path の二重 text_with**: それぞれ独立 snapshot で編集し、exit 順に
  store（last-write-wins）。定義される挙動だが推奨しない、と docs に一行書く。

## 2. 本指示書が決めたこと（最終形）

- **D-A″（改訂4）**: scoped の状態は act ではなく**呼び出し側の局所変数 +
  state-passing プロトコル**で運ぶ。`file_buffer` act は unscoped の ambient
  対だけに縮小。`file` act は spec §1 と完全一致のまま。
- **D-B‴（改訂4）**: 入れ子・escape・同一 path の扱いは §1「意味論の帰結」の
  とおり。専用の検出機構・転送機構は**存在しない**（instance 識別と
  EscapedEffect が全部やる）。
- **D-C**: `io_err` に `failed (path, str)` を追加。`file_meta` は `kind` /
  `size` / `readonly` までとし、`modified: opt instant` は **instant 実装後に
  戻ってきて追加**（[spec/2026-07-02-instant.md](../../spec/2026-07-02-instant.md)）。
- **D-D**: 旧 private snapshot 操作と Rust `FileSnapshots` は Stage 2 parity 後に
  削除。Rust 実装は unscoped native の path ごとの台帳として改名再利用してよい。
- **D-E（改訂4）**: `\my &x ->` 糖衣と `&do` 改訂は**本 slice に含めない**。
  design note に切り出し済み。fixture・docs は当面プロトコル手書き形で書き、
  糖衣が入ったら表記だけ差し替える（text_with の型は変わらない）。

## 3. Stage 0 — 純 Yulang の新 surface（Rust 変更なし）

1. `lib/std/io/file.yu`: `file` act を spec §1 の操作へ（済みなら維持）。
   `file_buffer` act は ambient 対だけに縮小。`text_with` を §1 の 4 行の
   プロトコル形に書き直す（run handler 版は撤去）。`text` は ambient ref。
   `read_text` / `write_text` は load / store の unwrap。旧 private snapshot
   操作と `open_text` / `open_in` はまだ消さない（Stage 2 まで並存）。
2. int エラーコードの新規使用は禁止。
3. 検証は `--host unsupported` + source mock handler のみ。
4. public signature 検査: `dump-poly-std-in std.io.file` に `#...` /
   `AllExcept` / 局所効果が現れないこと。`text_with` の型が
   `(path, str -> [e] ('a, str)) -> [file; io_err; e] 'a` の形であること。

**停止条件**: プロトコル形で public signature に局所効果が残る場合、
または `(結果, 最終値)` の組を返す λ の型付けが想定どおりにならない場合は、
回避策を積まずに停止してユーザに報告する。
（改訂3 の「転送 probe」は不要になったため削除。）

**移行窓の規律（native が赤くなる期間の扱い）**: 公開名を新実装へ向けた時点から
Stage 2 の registry 登録が終わるまで、native の file-resource case は失敗するのが
想定どおり。この期間、native case の期待値・タグ・manifest を**一切触らない**。
公開名の切り替えと Stage 2 の registry 登録は同じ push で完了させる。
Stage 0〜1 の green 基準は `--host unsupported` + mock fixture だけ。

## 4. Stage 1 — 必須 fixture 6 件（contract box + 入れ子）

期待値は意味論から手で導出する。callback はプロトコル手書き形で書く。

1. `file_text_with_commit` — scope exit で backing が更新される。
2. `file_text_with_rollback_on_error` — effect abort で backing 無傷。
3. `file_text_with_undet_last_write_wins` — 分岐ごと独立 buffer、到達順
   last-write-wins。各分岐は entry 時の snapshot を読む。
4. `file_text_unscoped_handler_discharge` — unscoped 形。mock handler の
   return 節（= handler extent 終端）で commit が観測される。
5. `file_text_mock_matches_native_shape` — 同一プログラム本文を mock と native で
   走らせ、public 観測が一致（native 側の有効化は Stage 2）。
6. `file_text_with_nested_cross_file` — A の text_with の中で B の text_with を
   開き、内側から両方の buffer を読み書きする（外側は字句閉包で触る）。
   それぞれの exit でそれぞれ commit。内側の abort は B だけ rollback。

tag: `file-resource` / `resource-lifetime` / `mock-host`（native は `host.native`）。
mock backing は `list (path, str)` の assoc list。**map / dict を新設しない**。

## 5. Stage 2 — native 載せ替えと int コード全廃

1. registry に `file` の新操作と `file_buffer::ambient_get / ambient_set` を
   名前ベースで登録（v2 F2。タグ番号ハードコード禁止）。tier は全て sync。
2. manifest タグ表の最小 slice: `result` / `io_err` / `file_kind` / `file_meta`
   の 4 型に限定。新しい private act 操作を bridge にすることは禁止。
3. unscoped の台帳を Rust 側に実装（D-D の改名再利用。key は path）。
4. `err_from_code` / `kind_from_code` / int コード / 旧 private snapshot 操作を削除。
5. 既存 native contract が**期待値変更なしで**通ること。変更が必要に見えたら停止。
6. `file_text_mock_matches_native_shape` を有効化。

## 6. Stage 3 — 後始末と evidence

- blocker note を resolved 記録に変える（削除はしない）。
- 暫定 helper 系 contract は言語機能の contract として残しつつ、中心証拠を
  Stage 1 の 6 件へ移す。
- spec/2026-07-02-io-resource-api.md §1 の callback 綴り
  （`ref '[file] str` を渡す形）を本指示書のプロトコル形に改める註記を入れる。
  糖衣後の規範例は `\my &text ->` 形になる予定、とも書く。
- `docs/language/contract-v1-file-evidence.md` / `docs/status.md` / todo を更新。
- release smoke の file-resource subset に 6 件を入れる。

## 7. やらないこと

- private snapshot 操作を public 化しない。
- `close` / `flush` / `save` 相当を足さない（v1 決定1〜2）。
- `file` act に操作を追加しない。`file_buffer` に scoped 操作を復活させない。
- map / dict データ構造を std に新設しない。
- **`\my &x ->` / `&do` 糖衣をこの slice で実装しない**（design note の別トラック。
  file の fixture・実装はプロトコル手書き形で完結させる）。
- 存在型・row 隠蔽・第一級 instance に手を出さない（研究相談トラック）。
- `load_bytes` / `store_bytes` / encoding 指定は follow-up。
- serve に進まない（structured-concurrency 決定文書が先）。
- **進捗は Stage 1 の 6 fixture と Stage 2 の削除項目でだけ測る。**

## 8. Rollback 条件

- 型紙の四層（act / session / view / raw）から外れる操作を足したくなったら停止。
- 停止条件に当たったら blocker note に一回だけ記録して停止（記録 commit を反復しない）。
- 期待値を実装出力から逆算しない。逆算したくなったら実装側を直すか停止する。

---

*署名: この指示書は Claude (Fable 5) が 2026-07-02 に、ユーザとの設計相談を経て
確定した実装順である。改訂1 の「buffer を公開 act に」、改訂3 の「入れ子は正常」、
改訂4 の「プロトコル形 = 貧者の存在型」と `\my &x ->` 糖衣構想はユーザ発案。
パッケージ形（解釈1）との等価性論証もユーザによる。ChatGPT / Codex が生成した
文書と矛盾する場合、本指示書と正本を優先する。 — Claude (Fable 5)*
