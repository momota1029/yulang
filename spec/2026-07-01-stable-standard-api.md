# Stable standard API contract

この文書は、Yulang の標準 API を「たまたま動く helper」から
「互換性を持つ public contract」へ昇格させるための基準を固定する。

対象は、filesystem、server、host capability、将来の FFI-backed standard API である。
実装はまだ未確定でよい。ただし、ここに置く API は次の変更で壊しにくい
意味論上の境界を持つ必要がある。

## 方針

stable standard API は、薄い関数群ではなく resource / lifetime / capability contract
として定義する。

避ける形:

```yu
file::exists path
file::read_text path
file::write_text (path, text)
```

これらは便利な wrapper として後から置けるが、中心 API にはしない。
中心 API は、host resource を開き、scope で寿命を区切り、capability failure を
構造化して扱う形にする。

## Stability levels

標準 API には、次の安定度を明示する。

### Stable contract

言語として互換性を守る面。

- API の中心概念
- resource lifetime
- capability deny / unsupported / operation failure の区別
- scope exit で起きる後処理
- wasm / playground / native host での portability policy
- public examples と release artifacts で守るべき挙動

stable contract の変更には spec 更新、docs/status 更新、migration note、
public regression が必要である。

### Provisional spelling

表面名や引数順がまだ実装前または実験中のもの。

例:

- `file::open`
- `file::text_with`
- `server::serve`
- `server.accept_with`

provisional spelling は spec に候補として置けるが、release docs で stable と呼ぶ前に
CLI / playground / docs の contract test を持つ必要がある。

### Experimental / internal

runtime 実験、debug command、playground-only helper、現行 std の暫定 wrapper。
これは互換性の約束ではない。

現行の `std::fs` helper や `opt` / `bool` で失敗を返す host API は、
stable API の実装素材にはなりうるが、そのまま stable contract にはしない。

## Common host resource model

host resource API は次を共有する。

- resource は host capability によって作られる。
- capability がない場合は、通常の missing value ではなく capability failure である。
- wasm / playground / sandboxed host で unsupported な resource は、fake success にしない。
- operation failure と capability deny は区別する。
- high-level managed resource は close 済み state machine を表面に出さない。
- explicit lifetime が必要な API は `_with` form で scope を受け取る。
- scope exit で、write-back、unlock、response completion、continuation release などの
  後処理を行う。
- raw resource は escape hatch であり、managed API の意味論を壊してはいけない。

`_with` form は continuation marker または closure を受け取る。
Haskell 風 do block ではなく、後続計算に resource capability を渡す境界として扱う。

```yu
resource::open_with config \&resource ->
  ...
```

## Error and failure policy

stable API は、失敗を `nil`、`false`、空文字、空 list だけに潰さない。

少なくとも次は区別する。

- host capability denied
- host capability unsupported
- target does not exist
- target exists but operation is denied
- operation failed after capability was granted
- runtime bug / impossible internal state

最終的な表面は `error` / `result` / host failure effect の仕様確定に従う。
それまでは、old helper の `opt` / `bool` failure を stable と書かない。

## File API contract

filesystem は [2026-07-01-file-resource-api.md](2026-07-01-file-resource-api.md)
を現在の anchor とする。

stable contract:

- path は普通の `str` として渡し、API 呼び出し点で path として解釈する。
- `file::meta path` が metadata の入口であり、`exists` / `is_file` / `is_dir` を
  中心 API にしない。
- `file::open path` は file session を作る。
- `file::open_with path do` は file session の lifetime を scope で閉じる。
- `file.text` / `file.bytes` は whole-file managed lens であり、stream ではない。
- managed lens には close / save / flush を置かない。
- dirty buffer の write-back、unlock、close 相当は lifetime の終端で行う。
- durability、seek、truncate、sync などは `file.raw` 側へ閉じ込める。
- `raw.sync` は close ではなく、write capability を手放さない。

provisional spelling:

```yu
file::meta path
file::open path
file::open_with path do
file::text path
file::text_with path do
file::bytes path
file::bytes_with path do

file.meta
file.text
file.text_with do
file.bytes
file.bytes_with do
file.raw
```

## Server API contract

server API は HTTP framework から始めない。
stable core は、host event session と request/response resource の lifetime contract である。

server session は、外部 event を受け取り、Yulang continuation を resume し、
response を host へ返す capability を持つ。

provisional spelling:

```yu
server::serve config \&server ->
  ...

server::open config
server::open_with config do

server.accept
server.accept_with do
server.raw

request.meta
request.payload
request.respond response
request.raw
```

stable contract:

- `server::serve` / `server::open_with` は server resource の lifetime を scope で閉じる。
- `server.accept` は host event が来るまで current continuation を suspend してよい。
- `server.accept_with` は request resource の lifetime を scope で閉じる。
- `request.respond response` は request の response capability を使う。
- response 後に同じ request capability で二重 response してはいけない。
- request scope が response なしで終わる場合の扱いは、host policy と diagnostics に残す。
- external event は、server boundary が明示的に渡した capability だけを見えるものとする。
- inner handler / local continuation / ref / thunk / closure を host event へ暗黙に渡さない。
- stored continuation は原則 one-shot であり、multi-shot server continuation は別 capability とする。
- HTTP / WebSocket / stdin / test driver は、この core の adapter であって core semantics ではない。

最小の意味論:

```text
serve(action):
  run action under a server capability
  on server.accept:
    store the continuation in the host scheduler
    return to the host event loop
  on external event:
    resume one stored continuation with a request resource
  on request.respond:
    transfer the response value to the host adapter
```

値が host boundary を越えるには、wire contract が必要である。
初期規則は保守的に置く。

```text
Only data values with an explicit wire codec may cross the host boundary.
```

closure、ref、thunk、effectful continuation は、wire value として暗黙に渡さない。
必要なら別 capability と別 spec を要求する。

## Relationship to FFI

FFI は stable standard API の裏側になりうるが、stable API そのものではない。

当面の優先順位:

1. host capability FFI
2. file / server resource API の host-backed implementation
3. native ABI FFI

native ABI FFI は、ownership、threading、panic/error boundary、buffer lifetime を扱うまで
stable surface へ上げない。

FFI-backed implementation へ移っても、file / server API の lifetime、capability failure、
scope exit semantics は変えてはいけない。

## Contract gates

標準 API を stable と呼ぶには、少なくとも次が必要である。

- spec に stable contract と provisional spelling が分かれている。
- `docs/status.md` が current status と known limitations を説明している。
- native CLI で通る小さい public regression がある。
- unsupported host では structured diagnostic または typed failure が出る。
- release artifact に bundled std が入り、repo 外から同じ API を import できる。
- playground / wasm が native-only capability を fake success にしない。
- current provisional std helper を互換性 promise と混同しない docs がある。

## Non-goals

- current `std::fs` helper をそのまま stable と呼ぶこと。
- HTTP framework を最初の server API にすること。
- native ABI FFI を先に public surface にすること。
- `Any` を host value / FFI value の逃げ口にすること。
- parser / infer が std function name の文字列を見て API 特別扱いすること。
