# FFI TODO

Yulang にはまだ FFI がない。
これは短期の public API ではないが、将来的には必須の機能として扱う。

理由は二つある。

- Yulang は effect / handler / lens / rich standard API を前面に出す言語であり、
  すべてを Yulang 自身で高速に実装する前提にはしない。
- 遅い言語ほど、OS、既存ライブラリ、native helper へ逃げる安定した境界が必要になる。

FFI は、単なる「C 関数を呼ぶ構文」ではなく、host capability と effect の境界として設計する。
filesystem / server API も、最終的にはこの境界と矛盾しない形で実装できる必要がある。

## 目的

- native helper / C ABI / system library を Yulang から呼べるようにする。
- hot path を Yulang runtime の外へ逃がせるようにする。
- standard API の一部を host implementation として差し替えられるようにする。
- playground / wasm / sandboxed host では明確に deny または unresolved にできるようにする。

## 非目的

- 型推論中で関数名や path 文字列を見て特別扱いすること。
- `Any` を FFI の逃げ口にすること。
- native backend の代替として、全言語機能を一気に native ABI へ落とすこと。
- unsafe な pointer / lifetime を最初から表面 API に露出すること。

## 層

FFI は少なくとも二層に分けて考える。

### Host capability FFI

標準 API や runtime host が提供する関数・resource を、Yulang の effectful operation として呼ぶ層。

例:

- filesystem
- server / socket
- clock
- process
- random
- environment variable

この層は、sandbox policy、diagnostics、capability deny を扱う。
最初に安定させるべきなのはこちら。

### Native ABI FFI

C ABI や platform library を直接呼ぶ層。

例:

- shared library loading
- symbol lookup
- primitive scalar conversion
- buffer / bytes passing
- callback

この層は、ABI、ownership、GC/lifetime、panic/error boundary、threading を扱う。
最初から広げると危険なので、host capability FFI の経験を踏まえて後で設計する。

## Effect boundary

FFI call は pure function として扱わない。
少なくとも host capability または unsafe/native effect を持つ。

```yu
ffi::call ...
# [host; ffi] または [unsafe; ffi] 相当
```

具体的な effect 名は未定だが、次は守る。

- host が許可しない FFI は runtime で曖昧に失敗させず、明確な failure にする。
- playground / wasm では deny 可能にする。
- diagnostics は「どの capability / symbol / ABI が許可されなかったか」を出す。
- effect を握りつぶして通常値だけにしない。

## Type boundary

最初の FFI type surface は小さくする。

候補:

- integer / float / bool
- bytes / pointer-like opaque handle
- string は encoding policy を決めてから
- struct layout は後回し
- callback は effectful continuation と絡むため後回し

FFI 型は Yulang の通常型推論へ無名で混ぜない。
必要なら、builtin / intrinsic / host definition として構造化された definition kind を持たせる。

## Filesystem / server API との関係

`spec/2026-07-01-file-resource-api.md` の file session / managed lens / raw resource は、
将来 FFI 上に実装されても意味が変わらないようにする。

特に:

- `.raw` は低レベル host resource への入口になりうる。
- managed lens は raw state machine を表面へ漏らさない。
- scope exit による write-back / unlock / close 相当は host resource finalization の実例になる。
- server API も request / response resource lifetime を scope で閉じる方向と相性がよい。

## Open questions

- FFI 宣言構文。
- library loading を package / realm / release artifact とどう結びつけるか。
- static link / dynamic link / host-provided symbol の区別。
- error handling: error effect、result、trap の切り分け。
- pointer と buffer の lifetime。
- callback が Yulang effect / continuation を再入させる場合の制限。
- GC / allocator / thread safety。
- wasm / playground / server sandbox policy。
- native backend 再開時に FFI declaration をどう lower するか。
