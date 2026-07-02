# IO resource API（file / connect / serve 統合仕様）

決定日: 2026-07-02
著者: Claude (Fable 5) — ユーザとの設計相談セッションにて。ユーザ承認済み。
状態: **仕様（authoritative）**

この文書は、標準 IO API（filesystem / 外向き接続 / 受信サーバ）の表面と意味論を
一つの型紙の下に固定する。意味論の根拠は次の正本 2 文書であり、本仕様は
その表面への導出である。

- [notes/design/2026-07-02-resource-lifetime-decisions.md](../notes/design/2026-07-02-resource-lifetime-decisions.md)（v1: 寿命・トランザクション）
- [notes/design/2026-07-02-host-act-ffi-decisions.md](../notes/design/2026-07-02-host-act-ffi-decisions.md)（v2: host act・tier・直交性）

[2026-07-01-file-resource-api.md](2026-07-01-file-resource-api.md) と
[2026-07-02-server-resource-api.md](2026-07-02-server-resource-api.md) とは、
矛盾する箇所において本仕様を優先する（v1 §7 の修正指示を本仕様が吸収する）。
安定度の語彙は [2026-07-01-stable-standard-api.md](2026-07-01-stable-standard-api.md)
に従う: 本仕様の**意味論は stable contract、綴りはすべて provisional spelling**
（contract test が揃うまで stable と呼ばない）。

## 0. 型紙

すべての IO API は次の四層の当てはめとして定義する。

```text
host act（能力。v2 F1〜F6 に従う）
  + session（資源。寿命 = scope または handler extent。close は存在しない）
  + managed view（意味論つきの見え方）
  + raw（escape hatch。managed の意味論を壊さない）
```

| | file | connect | serve |
|---|---|---|---|
| 相手 | ストレージ | こちらから呼んだ相手 | 向こうから来る相手たち |
| session | `file::open p` | `net::connect cfg` | 値を持たない（accept の分岐が session） |
| managed view | `&text` / `&bytes` lens | `send` / `recv` / `messages` | `req.payload` + `req.respond` |
| 寿命 | scope / handler extent | scope / handler extent | 分岐そのもの |
| raw | seek / sync / truncate | socket オプション（将来） | adapter 固有 metadata |
| 失敗 | `io_err` | `net_err` | `net_err` |

貫く規則（stable contract）:

1. **close / disconnect / flush / save はどの API にも存在しない。**
   資源の寿命は scope の終端か、それを供給した handler の extent で終わる（v1 決定1）。
2. **file の managed lens はスナップショット・トランザクション**
   （scope entry で読み、scope exit で commit、abort = rollback、
   多重 resume は分岐ごと独立 commit。v1 決定2）。
3. **serve の respond は一回きり**。commit をやり直せる資源（file）と
   一度きりの応答（serve）の非対称は仕様である（v1 決定4 註）。
4. **エラーは二層**: capability 層（handler 未登録 / unsupported host / deny）は
   registry の統一語彙、operation 層はドメイン型のデータ（v2 F3）。
   int エラーコードは存在しない。
5. **mock は構文を変えずに書ける**: `[file]` `[net]` `[server]` を Yulang の
   handler で catch すれば、ディスク・ネットなしで全観測が再現できる。
6. **undet / junction との交差**: file は分岐ごと独立 commit で共存する。
   `recv` / `accept` を undet 領域で perform することは unspecified
   （v2 F7 の三層契約。安く検出できるものだけ動的エラー）。
7. **scope の見えない ambient を作らない**: 「現在の接続」のような暗黙
   レジスタは、排除済みのシェル的暗黙変数の再発明であり禁止。
   ambient な能力は必ず handler block の字面の範囲を伴う。

## 1. file

### host act（第一層）

```yu
pub host act file:
    pub load: path -> result str io_err
    pub load_bytes: path -> result bytes io_err
    pub store: (path, str) -> result unit io_err
    pub store_bytes: (path, bytes) -> result unit io_err
    pub meta: path -> file_meta

pub error io_err:
    not_found path
    denied path
    invalid_path path
    failed (path, str)

pub struct file_meta {
    kind: file_kind,        -- missing / denied / file / dir / symlink / other
    size: int,              -- missing / denied のとき 0
    readonly: bool,
    modified: opt instant,
}
```

**`meta` は失敗しない。** 存在しない・アクセスできないは `kind` の値であって
例外ではない。存在確認は try/catch にならない。`exists` / `is_file` / `is_dir`
を中心 API に置かない方針（07-01 spec）はこれで実現される。

### 高レベル（純 Yulang。buffer + commit は v1 決定2）

```yu
pub meta(p: str): [file] file_meta
pub open(p: str): [file] file_session
pub open_with(p: str, f: file_session -> [e] 'a): [file; e] 'a
pub text(p: str): [file; io_err] ref '[file] str
pub text_with(p: str, f: (ref '[file] str) -> [e] 'a): [file; io_err; e] 'a
pub bytes(p: str): [file; io_err] ref '[file] bytes
pub bytes_with(p, f)
pub read_text(p: str): [file; io_err] str        -- text_with の read 専用糖衣

our s.meta: file_meta
our s.text: ref '[file] str
our s.bytes: ref '[file] bytes
our s.raw: file_raw          -- read / write / append / truncate / seek / sync
```

path は普通の `str` として渡し、呼び出し点で path として解釈する（07-01 spec 踏襲）。
unscoped 形（`file::text p`）の寿命は fs handler の extent
（デフォルト host handler ならプログラム終端）。

### 使用例（規範例。fixture の素材にする）

```yu
file::text_with "notes.txt" \&text ->
    for line in text.lines:
        if line.starts_with "TODO":
            line[0..4] = "DONE"
-- scope exit = commit。エラー離脱 = rollback（ファイル無傷）

my &log = file::text "run.log"
&log = $log ++ "started\n"
-- スクリプト終了（handler discharge）で write-back
```

## 2. connect（外向き接続）

### host act

```yu
pub host act net:
    pub listen: listen_config -> result listener net_err     -- sync（§3 で使用）
    pub connect: connect_config -> result conn_id net_err    -- sync
    pub send: (conn_id, bytes) -> result unit net_err        -- sync
    pub recv: conn_id -> result bytes net_err                -- suspend one-shot
    pub shutdown_send: conn_id -> result unit net_err        -- sync（半閉じ。close ではない）

pub error net_err:
    unreachable str
    refused str
    already_bound str
    closed
    timeout
    failed str
```

`recv` は suspend one-shot tier（v2 F6）: データ到着まで継続を止め、host が
一回 resume する。conn の寿命は scope（`connect_with`）か handler extent
（unscoped）。寿命の終端で host が接続を畳む。

### 高レベル — 三段の見え方

**値形（一般形。接続が複数あるとき必須）**:

```yu
pub connect(cfg): [net; net_err] conn
pub connect_with(cfg, f: conn -> [e] 'a): [net; net_err; e] 'a

our c.send(msg: bytes): [net; net_err] unit
our c.recv(): [net; net_err] bytes
our c.messages    -- 相手が閉じるまでの受信列。Fold として振る舞う
                  -- （closed は fold の終端であって error ではない）
```

**ambient 形（接続一本の idiom。handler scope で名前を畳む）**:

```yu
pub act channel 'a:
    pub send: 'a -> unit
    pub recv: () -> 'a

pub with_conn(cfg, body: () -> [channel bytes; e] 'a): [net; net_err; e] 'a =
    net::connect_with cfg \c ->
        catch body():
            send x, k -> k (c.send x)
            recv (), k -> k (c.recv())
```

ambient 形は値形への委譲 handler として**純 Yulang で定義される**
（v2 F10 の能力受け渡し）。console は「接続が常に一本だから ambient に
なっている channel」であり、この形の言語内前例である
（console の `channel str` instance 化は将来の検討事項）。

**chain 形（変数すら不要な流し読み）**:

```yu
for msg in (net::connect cfg).messages:
    say msg.decode.show
```

### adapter（core semantics ではない）

```yu
my body = http::get "https://example.com/data.json"    -- : [net; net_err] str
my res  = http::post url payload
```

`http::*` は connect + send + recv + scope を包んだ純 Yulang。

## 3. serve（受信サーバ）

### host act

```yu
pub host act server:
    pub accept: listener -> request                          -- suspend multi-shot
    pub respond: (respond_slot, bytes) -> result unit net_err   -- sync

pub struct request {
    meta: request_meta,     -- adapter 固有。core は関与しない
    payload: bytes,
    slot: respond_slot,     -- 不透明。respond で消費
}

our req.respond(res: bytes): [server; net_err] unit =
    server::respond (req.slot, res)
```

`accept` は suspend multi-shot tier（v2 F6）: host が接続ごとに継続を
一回ずつ resume し、accept より後のコードが「接続ごとの世界」になる。
これは undet と同じ世界分岐であり、docs では最初にそう説明する。
二重 respond は動的検査で拒否する（安い token 消費チェック。v2 F7）。

### 高レベル — listener は第一級

```yu
our l.accept(): [server; net_err] request     -- 並行: multi-shot の分岐点
our l.requests                                 -- 逐次: 一度に一接続ずつの Fold
our l.port: int                                -- listen 0 の ephemeral port を読む

pub serve(port: int): [net; server; net_err] request     -- 糖衣 = (net::listen port).accept()
pub serve_with(cfg, body: () -> [server; e] unit): [net; net_err; e] unit   -- scoped 形
```

**並行の `accept` と逐次の `requests` は別綴り**とし、どちらの意味かを
字面で決める。

### 使用例（規範例）

```yu
-- unscoped 一行宣言。listening の寿命 = handler extent
my req = net::serve 8080
req.respond req.payload            -- echo

-- 共有と接続ごとの境界は handler の位置が語る
my $hits = 0                       -- accept より前 = 全接続で共有
my req = net::serve 8080           -- 世界の分岐点
my $local = 0                      -- accept より後 = 接続ごとに独立

-- 逐次に処理したいとき
my l = net::listen 8080
for req in l.requests:
    req.respond (handle req.payload)
```

分岐後に同じ port を再 listen した場合、分岐ごとに operation 層の
`net_err::already_bound` になる（host は黙って dedupe しない）。

## 4. Executable contract staging

stable-standard-api の staging 規則に従う。本仕様の API は実装が動くまで
`tests/yulang/cases.toml` に入れない。追加時の contract tag は
`standard-api` + 各 domain（`filesystem` / `network`）+ host scope を明示する。
実装順は v1 §5（file の mock → native → undet 交差）→ v2 実装順
（manifest / registry / file act 刷新）→ serve first slice（in-process test
driver）の順とする。

## 5. 未決（仕様が縛らない場所）

- `connect_config` / `listen_config` / `net::to` の正確な形（TLS / timeout の置き場）。
- `request_meta` の中身（http adapter 層で定義する）。
- `messages` / `requests` の Fold としての正確な型（std::fold の語彙確定後）。
- text encoding の指定方法（UTF-8 既定、拡張は後。07-01 spec 踏襲）。
- `?` unwrap 記法確定後の signature 表記統一。
- console の `channel str` instance 化。
- 複数 listener の多重待ちと junction の合流。
- メモリより大きいファイルの扱い。whole-file lens はスナップショット・
  トランザクションの意味論上、巨大ファイルに適さない。raw の上に
  `messages` と同型の Fold 流ストリーム view（例: 行単位）を置く方向で、
  別途設計する（notes/design/2026-07-02-parting-assessment.md §8）。

## Rollback 条件

- 本仕様の綴りを実装しながら、型紙の四層（act / session / view / raw）から
  外れる操作を足したくなった場合は、実装を止めてユーザに確認する。
- close / flush / save 相当の操作を「利便のため」追加したくなった場合は、
  それは v1 決定1〜2 への違反であり、追加しない。
- fixture の期待値は本仕様と正本 2 文書から手で導出する。
  実装出力から逆算しない。

---

*署名: この仕様は Claude (Fable 5) が 2026-07-02 の設計相談セッションで
ユーザと合意した API 表面を固定したものである。一行宣言 serve（§3）と
ambient channel 形（§2）はユーザ提案を採用した箇所である。
ChatGPT / Codex が生成した文書と矛盾する場合、本仕様を優先する。
変更にはユーザの明示的な承認を要する。 — Claude (Fable 5)*
