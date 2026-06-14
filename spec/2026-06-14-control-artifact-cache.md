# Pipeline Artifact Cache

## 目的

`yulang run` / `yulang build` は、実ファイルから source set を集めたあとに
infer / specialize / control-vm lowering を通る。この区間は重いので、同じ source set
に対して生成された artifact をユーザー cache に保存し、次回以降はそこから再利用する。

cache は実行結果や source collection の cache ではない。対象は次の2段である。

- `.yuir`: principal poly artifact
- `.yuvm`: control-vm artifact

`.yuir` は infer を飛ばすための cache であり、性能上の本命である。`.yuvm` は
specialize / control lowering まで済んだ最終 VM 用 cache である。

## 境界

cache の前段で必ず次を通常どおり行う。

- entry path の解釈
- std root の探索または `--std-root` の適用
- implicit prelude の注入
- `mod` / `use mod` を辿る source collection
- source file の読み込み

このため、cache hit しても「どの source が program を構成するか」は毎回確認される。
in-memory source を扱う LSP / analyze route はこの cache を使わない。

`.yuir` hit で省略されるのは次である。

- `sources::load`
- `infer`

`.yuvm` hit で省略されるのは次である。

- `sources::load`
- `infer`
- `specialize`
- `control-vm` lowering

## キー

cache key は、収集済み source set 全体から作る。`.yuir` と `.yuvm` は同じ source key を使い、
stage ごとの format version は value 側 envelope で判定する。

- source key version / salt
- file count
- 各 file の path
- 各 file の module path
- 各 file の source text

どれかが変われば別 key になる。key は CLI の安定したバイト列 hash であり、
`std::collections::DefaultHasher` のような process / toolchain 依存 hash は使わない。

## 値

cache value は bincode envelope である。cache は内部形式なので、人間が直接読むための
JSON にはしない。壊れたら捨てて作り直せるものとして扱う。

`.yuir` envelope:

- format version
- `poly::expr::Arena`
- file count
- lowering error 表示文字列

`.yuvm` envelope:

- format version
- control-vm `Program`
- file count
- lowering error 表示文字列

通常の `build --out` が書く `YULANG-CONTROL-VM 1` artifact 形式は、ユーザーが明示的に
読み書きするための形式として残す。cache envelope はそれとは別の内部形式である。

`poly::expr::Arena` 内の `DefId` / `ExprId` / `PatId` / `RefId` / `SelectId` は、artifact
内部でだけ有効な arena-local ID である。外部安定名として扱ってはいけない。whole-program
source key と同時に保存・復元されるため、同じ envelope の中でだけ参照関係が保たれる。

infer の mutable graph、constraint machine、SCC work queue、selection probe の作業状態は
保存しない。保存するのは推論済み principal poly IR と、後段に必要な解決結果だけである。

## CLI semantics

`yulang run` は既定の control-vm route で cache を使う。`--interpreter` を指定した場合は
mono runtime route なので使わない。

`yulang build` / `yulang run` は、まず `.yuvm` を見る。hit した場合は保存済み
control-vm `Program` を使う。

`.yuvm` が miss した場合は `.yuir` を見る。hit した場合は保存済み `poly::Arena` を
specialize / control lowering へ渡し、得られた `.yuvm` も保存する。

両方 miss した場合は source set から fresh に infer を走らせ、得られた `.yuir` と
`.yuvm` を保存する。

`--no-cache` は cache の read/write の両方を無効にする。

cache hit / miss は stdout と stderr の通常出力を変えない。壊れた cache entry や書き込み失敗は
警告に留め、通常どおり新しく build する。cache が壊れているだけで program の build / run を
失敗させない。

`yulang cache path` はユーザー cache root を表示し、`yulang cache clear` はその root 全体を削除する。
poly artifact cache は `artifacts/poly/`、control-vm artifact cache は
`artifacts/control-vm/` を使う。
