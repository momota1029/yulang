# File resource API

この文書は、標準 filesystem API の現時点での仕様方針を固定する。
実装方法は未確定だが、API の意味論と境界はここを基準にする。
安定度の扱い、host capability failure、scope exit の共通規則は
[2026-07-01-stable-standard-api.md](2026-07-01-stable-standard-api.md) に従う。
resource lifetime / multi-shot continuation との相互作用については
[2026-07-02-resource-lifetime-decisions.md](../notes/design/2026-07-02-resource-lifetime-decisions.md)
を意味論の決定として扱う。

目的は、`read_text` / `write_text` / `exists` のような薄い関数群ではなく、
Yulang の lens / effect / continuation marker に沿った file resource API を作ること。

## Current executable slice

2026-07-02 時点では、中心設計の一部だけが executable contract になっている。
これは最終的な stable file resource API ではなく、host bridge と public surface を
固定するための first slice である。

現在 `tests/yulang/cases.toml` と CLI regression で守るもの:

- `std::text::path::of_bytes` / `to_bytes` は string-backed path model の
  byte conversion として動く。
- `path.show` は `path.to_bytes` と UTF-8 lossy conversion によって path payload を
  user-facing text にする。
- `std::io::file::read_text` / `write_text` は native CLI evidence VM route で
  host filesystem を読み書きする。
- `std::io::file::exists` / `is_file` / `is_dir` は native CLI evidence VM route で
  host metadata predicate として動く。
- `std::io::file::meta` は native CLI evidence VM route で
  `file_meta { kind, readonly }` を返す first metadata canary として動く。
  `kind` は `missing` / `file` / `dir` / `symlink` / `other` を区別する。
- `std::io::file::io_err::wrap` は failed file read/write を typed result boundary
  に変換し、display は失敗した path payload を含める。
- `std::io::file::open_text` / `open` / `open_in` / `text` / `text_with` は
  basic whole-file text ref の get/set と scoped callback spelling を通す。

まだ executable stable contract ではないもの:

- `read_at` / `write_at` の partial range semantics。
- directory listing、size、mtime などの portable metadata expansion。
- `file::meta` の final stable metadata type と denied / unsupported-host policy。
- OS-level locking と overlapping write session policy。
- explicit close/save/flush を置かない設計の最終 lowering。
- snapshot transaction、rollback、handler-extent lock release を含む完全な
  resource lifetime。
- wasm / playground / sandboxed host の unsupported-host typed failure。
- platform-native non-UTF-8 path の exact behavior。

この slice は `read_text` / `write_text` helper を中心 API へ昇格させるものではない。
helper は host bridge と error/result integration を観測するための executable surface
であり、中心 API は引き続き file session と managed lens である。
そのため、manifest 上の file helper / metadata canary cases は `stable-api` ではなく
`migration-canary` として分類する。

## 中心の形

標準 filesystem API の中心は、path 文字列から file session を作り、
そこから metadata、managed lens、raw resource を得る形にする。

```yu
file::meta path

my file = file::open path
my meta = file.meta
my &text = file.text
my raw = file.raw
```

scoped lifetime が必要な場合は、`do` continuation marker または通常の closure で
scope を明示する。

```yu
my result =
  my file = file::open_with path do
  my &text = file.text_with do
  ...
```

同じ意味を closure でも書ける。

```yu
file::text_with path \&text ->
  ...
```

`do` は Haskell 風の block syntax ではなく、後続計算を渡す continuation marker である。
`*_with` API はこの continuation を受け取り、scope exit で write-back / unlock / close
相当の後処理を行う。

## Path と metadata

`path` は長く保持する object として前面に出さない。
通常のユーザ値は `str` でよく、filesystem API の呼び出し点で path として解釈する。

`exists` / `is_file` / `is_dir` を中心 API としては置かない。
存在と kind は metadata の一部であり、`file::meta path` が唯一の入口になる。

```yu
file::meta path
# missing / denied / file / dir / symlink などを構造化して返す
```

正確な失敗表現は、error effect / result / host failure policy の確定後に決める。
ただし、metadata API は少なくとも次を区別できる必要がある。

- path が存在しない
- path は存在するがアクセスできない
- file / directory / symlink / other の kind
- size、mtime、readonly などの host metadata

`file.meta` はその session から見た backing file の metadata を読む。
dirty な managed lens の内容長などは text / bytes lens の情報であり、metadata と混同しない。

## Managed text / bytes lens

`file.text` と `file.bytes` は whole-file managed lens である。
stream ではない。

```yu
my &text = file::text path
my &bytes = file::bytes path
```

text lens は file content を `str` として扱う。
bytes lens は file content を bytes として扱う。
text の encoding は最初は UTF-8 を既定にし、encoding policy は後で拡張できる形にする。

managed lens は概念的に次を持つ。

- backing file identity
- current buffer
- dirty flag
- read / write capability
- lifetime scope

lifetime は値の生存ではなく scope の extent で決まる。
`text_with` / `bytes_with` / `open_with` の scope は、渡された continuation の終端で
閉じる。`file::text path` のような unscoped form は、その資源を供給した
filesystem handler の extent で閉じる。top-level で作った場合に program exit まで
伸びうるのは、デフォルトの host filesystem handler が program exit で discharge
されるためであり、GC finalizer や値の到達性に依存しない。

managed lens の安定意味論は snapshot transaction である。

1. scope entry で backing file を読み、managed buffer を作る。
2. 編集は buffer に反映される。
3. continuation が multi-shot resume される場合、buffer は分岐ごとに独立である。
4. scope exit に到達した分岐だけが dirty buffer を backing file へ commit する。
5. effect abort などで scope exit に到達しなかった分岐は write-back しない。
6. 複数分岐が commit する場合、commit 順は scope exit への到達順であり、
   last-write-wins である。

このため、managed lens は live file view ではない。scope 中の外部変更は commit 時に
上書きされうる。live access や細かい同期が必要な場合は、managed lens ではなく
`raw` API を使う。

安全性や lifetime の短さが必要な場合は、`text_with` / `bytes_with` / `open_with` を使う。

```yu
file::text_with path \&text ->
  ...
# scope exit で write-back / unlock / close 相当
```

## No close/save/flush on managed lens

managed lens には `close` / `save` / `flush` を通常 API として置かない。

明示的に「ここで書き込みを終えたい」場合は、明示的な close/save を呼ぶのではなく、
write scope 自体をそこで終える。

```yu
file::text_with path \&text ->
  ...
# ここで書き込み scope が終わる
```

この方針により、次の状態を表面化させない。

- close 済み handle を触る
- 二重 close
- save 済みだと思った dirty buffer
- save 後も編集権が残る state machine

durability や低レベル同期が必要な場合は、managed lens ではなく `raw` API を使う。

## Raw resource

`file.raw` は低レベル API への escape hatch である。
`sync`、細かい read/write、truncate、seek などはここに閉じ込める。

```yu
my file = file::open path
my raw = file.raw

raw.write bytes
raw.sync
raw.read
```

`raw.sync` は close/save ではない。
それまでの write を backing store へ同期する操作であり、editing right は手放さない。
resource lifetime は managed lens と同じく continuation extent または handler extent で
決まる。`raw.sync` はその lifetime を閉じず、lock release もしない。

raw resource に置く候補:

- `read`
- `write`
- `append`
- `truncate`
- `seek`
- `sync`

managed lens に置かないもの:

- `close`
- `flush`
- `sync`
- `seek`

## Locking

書き込み可能な file session / managed lens / raw resource は、lifetime 全体で書き込み権を持つ。
安全性が必要な host policy では、この lifetime 全体で write lock を保持する。

first slice の lock release 実装単位は、正確な scope exit ではなく filesystem handler
extent でよい。すなわち、program exit または mock / host handler discharge 時に、
その handler が供給した lock をまとめて返す。continuation segment drop hook が
evidence VM に入った後で、scope 単位の細粒度 release へ移せる。

標準意味論として守ること:

- 同じ runtime 内で、同じ backing file への overlapping write sessions は避ける。
- 同じ session 内の read は常に可能。
- `raw.sync` 後も write lock は保持される。
- lock release は close/save ではなく resource lifetime の終端で行う。

外部 process からの read/write は host lock policy に依存する。
標準 API の意味としては、他 process の read を必ず禁止する必要はない。
一方で、他 process または他 session の write は、安全 mode では排他する。
platform が advisory lock しか提供しない場合は、その制約を host policy と diagnostics に残す。

## API layers

高レベル API:

```yu
file::meta path
file::open path
file::open_with path do
file::text path
file::text_with path do
file::bytes path
file::bytes_with path do
```

file session views:

```yu
file.meta
file.text
file.text_with do
file.bytes
file.bytes_with do
file.raw
```

`file::text path` は `file::open path` から `.text` を取る shorthand として扱える。
`file::text_with path do` は `file::open_with path do` と `.text_with` を組み合わせる
shorthand として扱える。

## Implementation notes

この仕様は、実装が本当に OS file descriptor を開き続けることを要求しない。
高レベル lens は、低レベル raw operation の上に次のように実装してよい。

1. scope entry で file content を読む。
2. managed buffer と dirty flag を作る。
3. lens operation は buffer の get/set/update として扱う。
4. scope exit に到達した分岐だけが dirty buffer を backing file へ write-back する。
5. effect abort などで scope exit に到達しなかった分岐は buffer を捨てる。
6. multi-shot continuation の複数分岐は、分岐ごとに独立した buffer を commit する。
7. 必要な host policy では resource lifetime 全体で write lock を保持する。

raw resource はこの抽象化より下に置く。
高レベル lens が raw resource を使って実装されてもよいが、raw の状態機械を
managed lens の通常 API に漏らしてはいけない。

## Open questions

- error effect / result / host failure の最終表現。
- metadata の exact type と missing/denied の表し方。
- `file::open path` の既定 mode。read-only / read-write / create / truncate /
  append をどう指定するか。
- UTF-8 以外の encoding policy。
- directory listing と directory managed API を同じ resource model に載せるか。
- external process lock の platform 差を diagnostics にどう出すか。
- continuation segment drop hook をどの runtime layer に置き、lock release を
  handler extent から scope extent へ細粒度化するか。
