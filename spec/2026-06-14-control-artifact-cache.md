# Control Artifact Cache

## 目的

`yulang run` / `yulang build` は、実ファイルから source set を集めたあとに
infer / specialize / control-vm lowering を通る。この区間は重いので、同じ source set
に対して生成された control-vm artifact をユーザー cache に保存し、次回以降はそこから再利用する。

cache は実行結果や source collection の cache ではない。対象は control-vm `Program` と、
その program に付随する lowering error 表示情報だけである。

## 境界

cache の前段で必ず次を通常どおり行う。

- entry path の解釈
- std root の探索または `--std-root` の適用
- implicit prelude の注入
- `mod` / `use mod` を辿る source collection
- source file の読み込み

このため、cache hit しても「どの source が program を構成するか」は毎回確認される。
in-memory source を扱う LSP / analyze route はこの cache を使わない。

cache の後段で省略される可能性があるのは次だけである。

- `sources::load`
- `infer`
- `specialize`
- `control-vm` lowering

## キー

control-vm cache key は、収集済み source set 全体から作る。

- cache format version / salt
- file count
- 各 file の path
- 各 file の module path
- 各 file の source text

どれかが変われば別 key になる。key は CLI の安定したバイト列 hash であり、
`std::collections::DefaultHasher` のような process / toolchain 依存 hash は使わない。

## 値

cache value は JSON envelope である。

- format version
- control-vm `Program`
- file count
- lowering error 表示文字列

通常の `build --out` が書く `YULANG-CONTROL-VM 1` artifact 形式は、ユーザーが明示的に
読み書きするための形式として残す。cache envelope はそれとは別の内部形式である。

## CLI semantics

`yulang run` は既定の control-vm route で cache を使う。`--interpreter` を指定した場合は
mono runtime route なので使わない。

`yulang build` は出力 artifact を書く前に cache を参照し、hit した場合は保存済み
control-vm `Program` から通常 artifact を生成する。

`--no-cache` は cache の read/write の両方を無効にする。

cache hit / miss は stdout と stderr の通常出力を変えない。壊れた cache entry や書き込み失敗は
警告に留め、通常どおり新しく build する。cache が壊れているだけで program の build / run を
失敗させない。

`yulang cache path` はユーザー cache root を表示し、`yulang cache clear` はその root 全体を削除する。
control-vm artifact cache はその配下の `artifacts/control-vm/` を使う。
