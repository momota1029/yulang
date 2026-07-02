# Server resource API

この文書は、標準 server API の仕様方針を固定する。
共通の安定度、host capability failure、scope exit の扱いは
[2026-07-01-stable-standard-api.md](2026-07-01-stable-standard-api.md) に従う。
multi-shot continuation と resource lifetime の相互作用は
[2026-07-02-resource-lifetime-decisions.md](../notes/design/2026-07-02-resource-lifetime-decisions.md)
を意味論の決定として扱う。

目的は HTTP framework を先に作ることではない。
Yulang の effect / continuation / resource lifetime に沿った host event session を
標準 API の中心に置くこと。

## Current executable slice

2026-07-02 時点で executable contract になっている server 関連の面は、
標準 server API ではなく release artifact と language-server process である。

現在守るもの:

- released `yulang` binary は bundled std を使って `yulang server` を起動できる。
- `scripts/release-smoke.sh` は opt-in で `yulang server` startup を確認できる。
- `scripts/hardening-smoke.sh` は release smoke 経由で server startup を既定で確認する。
- LSP diagnostics / hover / definition は compiler の structured output を薄く公開する。

まだ executable stable contract ではないもの:

- `std::server` module。
- `server::serve` / `server::open` / `server.accept` の surface spelling。
- request / response resource の exact type。
- wire codec / serialization API。
- cancellation、backpressure、timeout、connection close の failure shape。
- HTTP / WebSocket / stdin / test-driver adapters。
- wasm / playground / sandboxed host の unsupported-host typed failure。

このため、server API の `.yu` fixture はまだ `tests/yulang/cases.toml` に入れない。
manifest に入れるのは、native CLI または unsupported host で挙動を compact に観測できる
first slice ができた時点に限る。

## Center shape

server API の中心は long-lived host session である。
server session は外部 event を受け取り、Yulang continuation を resume し、
request resource を渡し、response capability を host adapter へ返す。

```yu
server::serve config \&server ->
  ...

my session = server::open config
my request = session.accept
request.respond response
```

scoped lifetime が必要な場合は `_with` form で continuation を受け取る。

```yu
server::open_with config \&server ->
  server.accept_with \&request ->
    request.respond response
```

`*_with` form は Haskell 風 do block ではなく、resource lifetime を閉じる
continuation marker / closure boundary として扱う。

## Host event semantics

最小の意味論は次である。

```text
serve(action):
  run action under a server capability
  on server.accept:
    store the current continuation in the host scheduler
    return to the host event loop
  on external event:
    resume one stored continuation with a request resource
  on request.respond:
    transfer the response value to the host adapter
```

`server.accept` は host event が来るまで current continuation を suspend してよい。
stored continuation は原則 one-shot である。
multi-shot server continuation は別 capability と別 API を要求する。

`server.accept` を `undet` / junction / multi-shot resume されうる領域の内側で
perform することは、最初は typed failure または structured diagnostic として拒否する。
host scheduler に保存された continuation が複製されると、stored continuation の
one-shot 保証と request response capability の消費規則が壊れるためである。

## Multi-shot asymmetry with files

file managed lens と server request resource は、multi-shot continuation に対して
同じ扱いにしない。

file managed lens は snapshot transaction として定義できる。各分岐は独立した buffer を
持ち、scope exit へ到達した分岐だけが commit し、abort した分岐は rollback する。
この commit は host state を上書きする操作であり、複数回起きても
last-write-wins として意味を持てる。

server request resource は外部 event に由来する one-shot response capability である。
同じ request に対する二重 response や、複製された scheduler continuation からの
複数 response は意味を持たない。したがって、server の multi-shot 対応は将来の
別 capability として明示的に設計するまで stable API に入れない。

## Request / response resource

request resource は、host event に由来する payload と response capability を持つ。

候補 surface:

```yu
request.meta
request.payload
request.respond response
request.raw
```

標準意味論として守ること:

- `request.respond response` は request の response capability を消費する。
- 同じ request capability で二重 response してはいけない。
- request scope が response なしで終わる場合の扱いは host policy と diagnostics に残す。
- request resource の lifetime は `accept_with` で明示的に閉じられる。
- raw request は adapter 固有の escape hatch であり、managed request の意味論を壊してはいけない。

## Wire boundary

host boundary を越える値には wire contract が必要である。

初期規則:

```text
Only data values with an explicit wire codec may cross the host boundary.
```

closure、ref、thunk、effectful continuation は wire value として暗黙に渡さない。
必要なら、それぞれ別 capability と別 spec を要求する。

候補:

```yu
pub role Wire 'a:
  pub encode: 'a -> bytes
  pub decode: bytes -> result 'a wire_err
```

wire codec がない値を host boundary へ渡そうとした場合は、silent stringify や
fake success ではなく typed failure または structured diagnostic にする。

## Hygiene and capabilities

external event は、server boundary が明示的に渡した capability だけを見る。
inner handler、local continuation、ref、thunk、closure を host event へ暗黙に渡してはいけない。

server handler は global ambient operation ではなく、provider grant / capability source である。
この境界は evidence VM の continuation machinery を再利用し、別の callback system を作らない。

## Adapter layers

HTTP / WebSocket / stdin / in-memory test driver は adapter であり、core semantics ではない。

最初の実装順:

1. in-process test driver。
2. stdin/stdout adapter。
3. HTTP adapter。
4. WebSocket adapter。

adapter が違っても、resource lifetime、one-shot request response、wire boundary、
capability failure の意味論は変えない。

## Relationship to FFI

server API は将来 FFI-backed implementation の上に置ける。
ただし、native ABI FFI を public surface に出す前に、server resource の lifetime と
wire boundary を固定する。

FFI-backed server adapter へ移っても、次は変えてはいけない。

- `accept` が continuation suspend/resume 境界であること。
- request response が capability 消費であること。
- host boundary を越える値に wire contract が必要なこと。
- unsupported host が fake success しないこと。
