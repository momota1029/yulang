# Pipeline Artifact Cache

## 目的

`yulang run` / `yulang build` は、実ファイルから source set を集めたあとに
infer / specialize / control-vm lowering を通る。この区間は重いので、同じ source set
に対して生成された artifact をユーザー cache に保存し、次回以降はそこから再利用する。

cache は実行結果や source collection の cache ではない。対象は次の3段である。

- `.yucu`: compiled-unit artifact
- `.yuir`: principal poly artifact
- `.yuvm`: control-vm artifact

`.yucu` は syntax / namespace / lowering / typed / runtime surface を保存する。
exact full-source artifact としても、source-unit / std prefix artifact としても使う。
source-unit prefix hit では、prefix 側の parse / lowering / infer を飛ばし、変更された
suffix だけを fresh に処理する。

`.yuir` は infer 後の principal poly IR を保存する exact full-source cache である。
`.yuvm` は specialize / control lowering まで済んだ exact full-source VM 用 cache である。

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

full-source `.yucu` hit で省略されるのは次である。

- `sources::load`
- `infer`

source-unit / std prefix `.yucu` hit で省略されるのは、prefix として import された
source file 群に対する次の処理である。

- syntax / namespace / lowering surface の再構築
- typed scheme / runtime surface の再生成
- prefix 分の infer

suffix file は通常どおり parse / lower / infer される。prefix import は最適化であり、
失敗した場合は fresh compile に戻る。

`.yuvm` hit で省略されるのは次である。

- `sources::load`
- `infer`
- `specialize`
- `control-vm` lowering

## キー

exact full-source cache key は、収集済み source set 全体から作る。`.yuir`、`.yuvm`、
full-source `.yucu` は同じ source key を使い、stage ごとの format version は
value 側 envelope で判定する。

- source key version / salt
- file count
- 各 file の path
- 各 file の module path
- 各 file の source text

どれかが変われば別 key になる。key は CLI の安定したバイト列 hash であり、
`std::collections::DefaultHasher` のような process / toolchain 依存 hash は使わない。

source-unit `.yucu` は source dependency graph の unit ごとの key を使う。unit key は
unit 自身の source file と dependency unit key を含む。dependency-bearing unit は現在、
その transitive dependency closure を含む conservative artifact として保存する。

merged prefix `.yucu` は選択された source-unit artifact 群の manifest / surface hash から
key を作る。異なる unit の arena-local ID は key として使わず、merge 時に fresh target ID へ
remap する。

## 値

cache value は bincode envelope である。cache は内部形式なので、人間が直接読むための
JSON にはしない。壊れたら捨てて作り直せるものとして扱う。

`.yuir` envelope:

- format version
- `poly::expr::Arena`
- file count
- lowering error 表示文字列

`.yucu` envelope:

- format version
- manifest
- syntax surface
- namespace surface
- lowering surface
- typed surface
- runtime surface
- external runtime reference table
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
source key と同時に保存・復元される場合は、同じ envelope の中でだけ参照関係が保たれる。
source-unit `.yucu` が prefix arena の def を参照する場合は、raw arena-local ID ではなく
serialized external runtime reference table で説明できる範囲だけを import する。

infer の mutable graph、constraint machine、SCC work queue、selection probe の作業状態は
保存しない。保存するのは推論済み principal poly IR と、後段に必要な解決結果だけである。

## CLI semantics

`yulang run` は既定の control-vm route で cache を使う。`--interpreter` を指定した場合は
mono runtime route なので使わない。

`yulang build` / `yulang run` は、まず `.yuvm` を見る。hit した場合は保存済み
control-vm `Program` を使う。

`.yuvm` が miss した場合は `.yuir` を見る。hit した場合は保存済み `poly::Arena` を
specialize / control lowering へ渡し、得られた `.yuvm` も保存する。

`.yuir` が miss した場合は、同じ exact source key の full-source `.yucu` を見る。
hit した場合は compiled surfaces から `poly::Arena` を復元し、得られた `.yuir` と `.yuvm`
も保存する。

full-source `.yucu` が miss した場合は、source-unit / std prefix `.yucu` を探す。
hit した場合は prefix artifact を import し、prefix に含まれない suffix source だけを
fresh に処理する。結果として exact full-source `.yucu` と `.yuir` を保存し、`run` では
`.yuvm` も保存する。

全て miss した場合は source set から fresh に infer を走らせ、得られた `.yucu`、`.yuir`、
`.yuvm` を保存する。fresh miss 時には source-unit closure `.yucu` も保存する。

`--no-cache` は cache の read/write の両方を無効にする。

cache hit / miss は stdout と stderr の通常出力を変えない。壊れた cache entry や書き込み失敗は
警告に留め、通常どおり新しく build する。cache が壊れているだけで program の build / run を
失敗させない。

`yulang cache path` はユーザー cache root を表示し、`yulang cache clear` はその root 全体を削除する。
compiled-unit artifact cache は `artifacts/compiled-unit/`、poly artifact cache は
`artifacts/poly/`、control-vm artifact cache は `artifacts/control-vm/` を使う。

`--runtime-phase-timings` の `run.cache` は、使われた route を表示する。

- `control-hit`: exact `.yuvm` hit
- `poly-hit`: exact `.yuir` hit
- `compiled-unit-hit`: exact full-source `.yucu` hit
- `std-prefix-hit`: std prefix `.yucu` hit
- `std-prefix-build`: std prefix `.yucu` を作ってから suffix を処理
- `source-unit-prefix-hit`: single source-unit prefix `.yucu` hit
- `merged-source-unit-prefix-hit`: merged source-unit prefix `.yucu` hit
- `full-miss`: fresh compile
