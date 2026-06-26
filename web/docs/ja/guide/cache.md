# キャッシュ

Yulang はコンパイラの artifact をキャッシュします。プログラムの実行結果はキャッシュしません。
各 `run` は、必要な artifact を見つけるか作り直したあとで、通常どおりプログラムを実行します。

## artifact の種類

| Artifact | 保存するもの | 効く場面 |
| --- | --- | --- |
| `.yucu` | 構文、名前空間、型、runtime surface | 標準ライブラリや変更していない依存モジュールの再利用 |
| `.yuir` | 推論済み principal poly IR | 完全に同じ source set を、推論なしで再実行する |
| `.yuvm` | lower 済み control-VM program | 完全に同じ source set を、specialize / VM lowering なしで再実行する |

増分コンパイルで重要なのは `.yucu` です。これは "Yulang compiled unit" の略です。
キャッシュ済み `.yucu` は prefix として import できるため、Yulang はその prefix に含まれない
source file だけを再コンパイルできます。

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

## 現在の制限

cache は保守的です。繰り返し実行やローカル編集では速くなりますが、clean build では
parser、lowering、型推論、runtime lowering の費用をすべて払います。

package-level の `realm.toml` / `yulang.lock` workflow はまだ実験段階です。将来は realm と
band の identity を使って、dependency cache key をより精密にする予定です。
