# キャッシュ

Yulang はコンパイラの artifact をキャッシュします。プログラムの実行結果はキャッシュしません。
各 `run` は、必要な artifact を見つけるか作り直したあとで、通常どおりプログラムを実行します。

realm は version 付きの解決空間であり、band は realm 内の import / build の島です。
module は band の中にあり、bare path は band 境界を越えません。

local file では、`realm.toml` が explicit editable realm を示します。`realm.toml`
が見つからない場合、entry file の親 directory が implicit editable realm になります。
entry file は root module のままですが、`main.yu` なら `main` のように、source path
由来の band path も持ちます。

## artifact の種類

| Artifact | 保存するもの | 効く場面 |
| --- | --- | --- |
| `.yucu` | 構文、名前空間、型、runtime surface | 標準ライブラリや変更していない依存モジュールの再利用 |
| `.yuir` | 推論済み principal poly IR | 完全に同じ source set を、推論なしで再実行する |
| `.yumo` | specialize 済み mono IR | mono command の再実行や、同じ source set から control VM を作り直す |
| `.yuvm` | lower 済み control-VM program | 完全に同じ source set を、specialize / VM lowering なしで再実行する |
| `.yures` | realm / band の解決結果 | source-site の realm import を、cached target fingerprint で確認する |

増分コンパイルで重要なのは `.yucu` です。これは "Yulang compiled unit" の略です。
キャッシュ済み `.yucu` は prefix として import できるため、Yulang はその prefix に含まれない
source file だけを再コンパイルできます。`.yucu` の syntax surface は band path を記録するため、
cached prefix から `realm/main::*` や `band::inner` のような route-aware import を解決できます。

`.yumo` は exact source key の cache です。realm 全体に対する mono cache ではありません。
Yulang は同じ source / resolution context に対してだけ再利用します。

`.yures` は解決結果の記録で、compiled code ではありません。local な `realm/...::...` import では、
cached entry が deterministic な local `<realm>/<band>.yu` path を指し、source fingerprint も一致する
場合だけ使われます。そうでない場合は通常の filesystem resolver に戻ります。
install 済み local realm の `local/<name>/<band>::...` import では、resolved snapshot の
realm/version と target source fingerprint を記録し、installed snapshot が一致する場合だけ使います。

## route label

どの経路を使ったかは `--runtime-phase-timings` で見られます。

```sh
yulang run --runtime-phase-timings path/to/file.yu
```

`run.cache` には次のような値が出ます。

| Route | 意味 |
| --- | --- |
| `control-hit` | exact `.yuvm` hit |
| `poly-hit` | exact `.yuir` hit |
| `compiled-unit-hit` | exact full-source `.yucu` hit |
| `std-prefix-hit` | 標準ライブラリの `.yucu` prefix を再利用 |
| `std-prefix-build` | 標準ライブラリ prefix を作ってから再利用 |
| `source-unit-prefix-hit` | 1つの依存 prefix を再利用 |
| `merged-source-unit-prefix-hit` | 複数の独立 prefix を merge して再利用 |
| `full-miss` | source から fresh compile |

ローカル編集で重要なのは `std-prefix-hit`、`source-unit-prefix-hit`、
`merged-source-unit-prefix-hit` です。これらは、変更していない prefix を飛ばして、
残りの suffix だけを compile したことを表します。

## cache command

```sh
yulang cache path
yulang cache stats
yulang cache clear
```

1回だけ cache を使わずに実行する場合は `--no-cache` を付けます。

```sh
yulang run --no-cache path/to/file.yu
```

古い cache や壊れた cache は、言語エラーではありません。Yulang はその artifact を飛ばし、
source から compile し直します。

`--no-cache` は source collection 中の checked realm-resolution cache lookup も無効にします。

release installer は embedded std source を install したあと、最終 install path を使って
standard-library `.yucu` prefix を一度 seed します。これにより、その後の CLI run と
cache key が一致します。install 時の cache warmup を省く場合は
`YULANG_NO_SEED_CACHE=1` を設定します。

## 現在の制限

cache は保守的です。繰り返し実行やローカル編集では速くなりますが、clean build では
parser、lowering、型推論、runtime lowering の費用をすべて払います。

local editable realm/band identity route は有効です。`realm/...::...` import、entry-band alias、
`yulang realm install` で作る installed local `local/<name>/<band>::...` import も含みます。
global package workflow はまだ実験段階です。remote provider、version-family solving、
`yulang.lock`、registry/git source policy は stable な user workflow ではありません。
