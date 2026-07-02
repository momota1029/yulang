# file / serve / connect API 具体案

作成日: 2026-07-02
著者: Claude (Fable 5)
状態: **承認済み → 仕様へ昇格済み（2026-07-02）**。正式版は
[spec/2026-07-02-io-resource-api.md](../../spec/2026-07-02-io-resource-api.md)。
本文書は検討過程の記録として残す。以後の参照・修正は spec 側に対して行うこと。
意味論の根拠は正本 2 文書:
[2026-07-02-resource-lifetime-decisions.md](2026-07-02-resource-lifetime-decisions.md)（v1）と
[2026-07-02-host-act-ffi-decisions.md](2026-07-02-host-act-ffi-decisions.md)（v2）。

## 0. 型紙 — 三つの API は同じ形の三回の当てはめ

```text
host act（能力）
  + session（資源。寿命 = scope または handler extent、close なし）
  + managed view（意味論つきの見え方）
  + raw（escape hatch）
```

| | file | connect（外へ繋ぐ） | serve（受ける） |
|---|---|---|---|
| 相手 | ストレージ | こちらから呼んだ相手 | 向こうから来る相手たち |
| session | `file::open p` | `net::connect cfg` | **accept が接続ごとに分岐を配る**（session を値で持たない） |
| managed view | `&text` / `&bytes` lens（トランザクション） | `send` / `recv` / `messages`（Fold 流） | `req.payload` + `req.respond`（一回きり） |
| 寿命 | scope / handler extent | scope / handler extent | 分岐 = 接続の寿命 |
| raw | seek / sync / truncate | socket オプション等（将来） | adapter 固有 metadata |
| 失敗 | `io_err`（データ） | `net_err`（データ） | `net_err` + host policy |

serve だけ session を値で持たないのは欠陥ではなく v2 §F6 の帰結:
接続ごとの世界は multi-shot resume が**継続として**分岐させるので、
「いま自分がいる分岐」こそが session であり、値にする必要がない。

## 1. file

### host act（第一層。v2 F1〜F4 に従い痩せた形）

```yu
pub host act file:
    pub load: path -> result str io_err
    pub load_bytes: path -> result bytes io_err
    pub store: (path, str) -> result unit io_err
    pub store_bytes: (path, bytes) -> result unit io_err
    pub meta: path -> file_meta                 -- 失敗も kind で表す（下記）

pub error io_err:
    not_found path
    denied path
    invalid_path path
    failed (path, str)          -- その他。str は host の説明文

pub struct file_meta {
    kind: file_kind,            -- missing / denied / file / dir / symlink / other
    size: int,                  -- missing/denied のとき 0
    readonly: bool,
    modified: opt instant,
}
```

設計判断: **`meta` は失敗しない**。存在しない・アクセスできないは例外ではなく
`kind` の値（`missing` / `denied`）。存在確認が try/catch にならない。
`load` / `store` は本当に読めなかったときだけ `io_err` を返す。

### 高レベル（純 Yulang。buffer + commit は v1 決定2 のトランザクション）

```yu
pub meta(p: str): [file] file_meta
pub open(p: str): [file] file_session
pub open_with(p: str, f: file_session -> [e] 'a): [file; e] 'a
pub text(p: str): [file; io_err] ref '[file] str
pub text_with(p: str, f: (ref '[file] str) -> [e] 'a): [file; io_err; e] 'a
pub bytes(p: str): [file; io_err] ref '[file] bytes
pub bytes_with(p, f)

-- file_session の view
our s.meta: file_meta
our s.text: ref '[file] str          -- snapshot transaction lens
our s.bytes: ref '[file] bytes
our s.raw: file_raw                  -- append / truncate / seek / sync / read / write
```

wrapper の作りの例（host act → error effect への持ち上げ）:

```yu
pub text_with(p: str, f) =
    my buf = (file::load p).else \e -> e.throw     -- 将来は (file::load p)?
    my &cell = ref::of buf                          -- 純粋 state（分岐ごと独立）
    my out = f &cell
    (file::store (p, $cell)).else \e -> e.throw     -- scope exit = commit
    out
-- error effect で途中離脱したら store に到達しない = rollback（v1 決定2）
```

### 使い心地

```yu
-- 設定を読むだけ
my conf = file::read_text "config.toml"             -- text_with の read 専用糖衣

-- ファイルは耐久性のある & 変数（v1 §0）
file::text_with "notes.txt" \&text ->
    for line in text.lines:
        if line.starts_with "TODO":
            line[0..4] = "DONE"
-- ここで commit。エラー離脱ならファイル無傷

-- unscoped: スクリプト終了（= fs handler discharge）で write-back
my &log = file::text "run.log"
&log = $log ++ "started\n"

-- 存在とメタ
if (file::meta "cache.bin").kind.is_file:
    ...

-- 低レベルが要るときだけ raw
file::open_with "data.bin" \s ->
    s.raw.append chunk
    s.raw.sync
```

## 2. connect（外へ繋いで受け取る側）

### host act

```yu
pub host act net:
    pub connect: connect_config -> result conn_id net_err      -- sync
    pub send: (conn_id, bytes) -> result unit net_err          -- sync
    pub recv: conn_id -> result bytes net_err                  -- suspend one-shot
    pub shutdown_send: conn_id -> result unit net_err          -- sync（半閉じ。close ではない）

pub error net_err:
    unreachable str          -- 接続先に届かない
    refused str
    closed                   -- 相手が閉じた後の send / recv
    timeout
    failed str
```

`recv` が suspend one-shot tier の代表例（v2 §F6）: データが来るまで
継続を止め、host が一回 resume する。**close 操作はない**——conn の寿命は
scope（`connect_with`）か handler extent（unscoped）で、寿命の終端で
host が接続を畳む（v1 決定1）。

### 高レベル

```yu
pub connect(cfg): [net; net_err] conn
pub connect_with(cfg, f: conn -> [e] 'a): [net; net_err; e] 'a

our c.send(msg: bytes): [net; net_err] unit
our c.recv(): [net; net_err] bytes
our c.messages: -- 相手が閉じるまでの受信列。Fold として振る舞う
                -- （closed は fold の終端であって error ではない）
```

`messages` が Yulang らしさの中心。受信ループを書かず、コレクションと
同じ顔で畳む（[[project_core_roles]]: Fold が主役）:

```yu
-- 購読して流れてくるものを処理
net::connect_with (net::to "feed.example.com" 9000) \conn ->
    for msg in conn.messages:
        say msg.decode.show

-- 一往復
net::connect_with (net::to "api.local" 7070) \conn ->
    conn.send query.encode
    conn.recv().decode
```

### 2.5 conn の持ち回しについて（ユーザ質問、2026-07-02）

質問: connect 側で conn 値を持ち回すのは非直感的。serve のように
まとめられるか、それとも基本的すぎてまとめてはいけないか。

答え: **conn の「名前」は接続が複数ありうる限り基本的**（proxy のように
二本張るとき、区別する名前は消せない）。しかし**接続が一本の場合は、
名前を値ではなく handler スコープに畳める**。Yulang では ambient な能力は
effect scope として表すのが正統で、しかも新機構ゼロで導出できる。

serve が一行化できたのは multi-shot resume が「いまいる分岐」を session に
してくれたから。connect にはその手品がない（相手は一人）ので、名前の置き場は
二つしかない: **値（conn）か、handler の scope か**。

```yu
-- 一本のときの ambient 形: send/recv が裸の operation になる
pub act channel 'a:                  -- 2026-06-29 server sketch の channel act を再利用
    pub send: 'a -> unit
    pub recv: () -> 'a

pub with_conn(cfg, body: () -> [channel bytes; e] 'a): [net; net_err; e] 'a =
    net::connect_with cfg \c ->
        catch body():
            send x, k -> k (c.send x)
            recv (), k -> k (c.recv())

-- 使い心地
net::with_conn (net::to "api.local" 7070) \() ->
    send query.encode
    my reply = recv()
```

これは F10（能力の明示的受け渡し = 委譲 handler）の実例そのもので、
純 Yulang で書ける。そして前例が言語内に既にある: **console が
「誰も持ち回さない ambient channel」**である（`console::read_line()`）。
stdin/stdout は、接続が常に一本だから ambient になっている channel にすぎない。
console を `channel str` の instance として説明し直せる可能性もある（要検討）。

境界も一つ引く: **scope の見えない ambient（「現在の接続」レジスタ）は作らない**。
それは排除済みのシェル的暗黙変数（`$_`）の再発明になる
（[[project_no_implicit_shell]]）。ambient は必ず handler block の字面の
範囲を伴う。

補足: 一本の接続の多くは chain が持ち回し自体を吸収する——

```yu
for msg in (net::connect cfg).messages:     -- conn 変数を作らず一行
    say msg.decode.show
```

### 便利層（adapter。core semantics ではない）

```yu
my body = http::get "https://example.com/data.json"     -- : [net; net_err] str
my res  = http::post url payload
```

`http::get` は connect + send + recv + scope を包んだだけの純 Yulang。

## 3. serve（受ける側）

### host act

```yu
pub host act server:
    pub accept: () -> request                       -- suspend multi-shot（v2 F6）
    pub respond: (respond_slot, bytes) -> result unit net_err   -- sync

pub struct request {
    meta: request_meta,      -- adapter 固有（http なら method / path / headers 相当）
    payload: bytes,
    slot: respond_slot,      -- 不透明。respond で消費（二重 respond は動的検査で拒否）
}

our req.respond(res: bytes): [server; net_err] unit =
    server::respond (req.slot, res)
```

### 高レベル

```yu
pub serve(cfg, body: () -> [server; e] unit): [net_err; e] unit
```

### 使い心地 — 接続ごとの分岐が直線コードになる（v2 F6 の中心）

```yu
-- echo サーバ。ループなし。accept から先が「接続ごとの世界」
server::serve (net::listen 8080) \() ->
    my req = server::accept()
    req.respond req.payload

-- http adapter を被せた形
http::serve 8080 \req ->
    case req.route:
        get "/health" -> http::ok "alive"
        get "/data"   -> http::ok (load_data req.query)
        _             -> http::not_found
```

state が要るときも、純粋 state スレッディングが分岐ごとに独立だから
接続間で混ざらない（v1 決定2 と同じ機構）。接続をまたいで共有したい
カウンタ等は、serve の**外側**の handler で受ける——共有の範囲が
handler の位置として目に見える:

```yu
my $hits = 0
server::serve (net::listen 8080) \() ->
    my req = server::accept()
    &hits = $hits + 1            -- 外側 state = 全接続で共有（handler の位置が語る）
    req.respond (show $hits).encode
```

## 3.5 一行宣言 serve（ユーザ提案、2026-07-02 採用方向）

ユーザ提案: `serve` ブロックと `accept` は一つにまとめられる——
一行の宣言で「ここから先が接続ごとの世界」にできるはず。

これは新機能ではなく、**型紙の unscoped 形**である。file に `text_with`
（scoped）と `text`（unscoped、寿命 = handler extent）の両形があるのと同じく、
serve にも両形がある。sketch 初版は scoped 形しか書いておらず、対称性に
穴が空いていた。

```yu
-- listener は第一級（sync）。accept が multi-shot の分岐点
pub host act net:
    pub listen: listen_config -> result listener net_err    -- sync
    ...
our l.accept(): [net; net_err] request                       -- suspend multi-shot
our l.port: int                                              -- listen 0 で ephemeral port を取った時に読む

-- unscoped（一行宣言）: listening の寿命 = handler extent（スクリプトが生きる限り）
my req = (net::listen 8080).accept()
req.respond req.payload

-- 糖衣
my req = net::serve 8080             -- = (net::listen 8080).accept()

-- scoped: listening の寿命を明示的に閉じたいときだけ
net::serve_with (net::listen 8080) \() ->
    my req = server::accept()
    ...
```

listener を第一級に残す理由（「listen は serve 以外に使い道があるか」への答え）:

- `net::listen 0` で ephemeral port を束縛して `l.port` を読む（テスト・並行起動）。
- 将来の複数 listener の多重待ち（junction との合流点になりうる）。
- accept を配る前に listener の存在だけ確認したい起動シーケンス。

共有/接続ごとの境界は、一行宣言でも handler の位置の規則そのままで読める:

```yu
my $hits = 0                          -- accept より前 = 全接続で共有
my req = net::serve 8080              -- ここが世界の分岐点
my $local = 0                         -- accept より後 = 接続ごとに独立
```

### 諸刃の明文化

- **下流の複製**: 一行宣言より後のコードはすべて接続ごとに走る。fork と同型で、
  undet が既に持つ性質と同じ。驚きを減らすため、docs では
  「`accept` は undet と同じ世界分岐である」と最初に書く。
- **分岐後の再 listen**: accept より後で `net::listen 8080` を再度 perform すると、
  分岐ごとに実行されて operation 層の `net_err`（already bound）になる。
  これは仕様（分かりやすいエラー）であって、host が黙って dedupe しない。
- **逐次処理したい場合**: 分岐したくないなら Fold 形を使う——
  `for req in l.requests:` は一度に一接続ずつの逐次 serve（multi-shot ではなく
  fold）。並行の `accept` と逐次の `requests` を別綴りにすることで、
  「どちらの意味か」が字面で決まる。

## 4. 三つを貫く規則（再掲、根拠つき）

- **close / disconnect / flush はどこにも無い**。寿命は scope か handler extent
  （v1 決定1）。半閉じ（shutdown_send）は close ではなく操作。
- **file の view はトランザクション、serve の respond は一回きり**。
  「commit をやり直せる資源」と「一度きりの応答」の非対称は v1 決定4 の註のとおり。
- **エラーは二層**: capability 層（handler 未登録 / unsupported host）は registry の
  統一語彙、operation 層（not_found / refused / closed）はドメイン型のデータ（v2 F3）。
- **mock はタダ**: `[file]` `[net]` `[server]` を Yulang の handler で catch すれば、
  ディスクもネットも無しで全部テストできる。構文は一切変わらない。
- **junction / undet との交差**: file は分岐ごと独立 commit で共存。
  net::recv / server::accept を undet 領域で使うのは unspecified（v2 F7 の三層契約）。

## 5. 未決として明示的に残すもの

- `connect_config` / `net::to` / `net::listen` の正確な形（TLS、timeout 設定の置き場）。
- `request_meta` の中身（adapter 層に置く。core には bytes + slot だけ）。
- `messages` の Fold としての正確な型（std::fold の語彙が確定してから）。
- text の encoding 指定（UTF-8 既定は file spec のとおり、拡張は後）。
- `?` unwrap 記法確定後の signature 書き直し（`.else \e -> e.throw` は暫定）。

---

*署名: この文書は Claude (Fable 5) が 2026-07-02 に、正本 2 文書の意味論から
導出した API 具体案である。承認されるまで provisional。 — Claude (Fable 5)*
