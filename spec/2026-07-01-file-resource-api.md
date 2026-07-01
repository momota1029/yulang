# File resource API

この文書は、標準 filesystem API の現時点での仕様方針を固定する。
実装方法は未確定だが、API の意味論と境界はここを基準にする。

目的は、`read_text` / `write_text` / `exists` のような薄い関数群ではなく、
Yulang の lens / effect / continuation marker に沿った file resource API を作ること。

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

編集は buffer に反映され、write-back は lifetime の終端で行う。
`file::text path` のような unscoped form は、その値が生きている間 write capability を持つ。
top-level で作った場合は、host filesystem effect の解決時または program exit まで
lifetime が伸びうる。

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
resource lifetime と lock release は scope exit に揃える。

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
安全性が必要な host policy では、この scope 全体で write lock を保持する。

標準意味論として守ること:

- 同じ runtime 内で、同じ backing file への overlapping write sessions は避ける。
- 同じ session 内の read は常に可能。
- `raw.sync` 後も write lock は保持される。
- lock release は close/save ではなく scope exit で行う。

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
4. scope exit で dirty buffer を backing file へ write-back する。
5. 必要な host policy では scope 全体で write lock を保持する。

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
