# CLI リファレンス

`yulang` CLI は Yulang プログラムの検査、build、実行、test、調査を行う。
このページでは、サポート対象の command surface と option を扱う。

## 起動形式と help

一般形は `yulang [共通 option] <command> [command option]` である。
共通 option は command の前後どちらにも置ける。

現在の CLI には `--help`、`--version`、command ごとの help がない。
`yulang` または `yulang --help` を実行すると、標準エラーに usage を出し、status 2 で終了する。
command の失敗は通常 status 1 で終了する。

## 共通 option

共通 option が作用する command は、表の右列に挙げたものに限られる。

| Option | 作用 | Command |
| --- | --- | --- |
| `--std-root <path>` | `<path>` を標準ライブラリ root として使う | `check`、`contract`、`test`、`build`、`run`、`dump`、`install std`、`server` |
| `--no-prelude` | implicit prelude を追加しない | `check`、`test`、`build`、`run`、`dump` |
| `--cst` | command の結果より前に具象構文木を出す | `check`、`build`、`run`、`dump` |
| `--no-cache` | compiler キャッシュの read と write を無効にする | `test`、`build`、`run`、`dump` |
| `--infer-phase-timings` | 型推論の phase と統計を出す | `check` |
| `--runtime-phase-timings` | compile、キャッシュ route、runtime の phase と統計を出す | `run` |

`YULANG_LIB_DIR` はユーザーライブラリ root を変更する。
この root は `install std` と local realm の install が使う。
`YULANG_CACHE_DIR` は、compile と `cache` command が使う compiler キャッシュ root を変更する。

## source の検査

`check <path>` は entry ファイルを parse し、型を検査する。
成功時は、`--cst` または `--infer-phase-timings` がなければ何も出さない。
検査に失敗すると diagnostic を出す。

```sh
yulang check hello.yu
```

## プログラムの実行

`run` は default で evidence VM を使う。
入力には 1 個のファイル path、`-e` または `--eval` で渡す source、標準入力を使える。
標準入力は `-` で明示でき、非 interactive な場合は暗黙にも選ばれる。
interactive な `yulang run` に入力を付けない場合は、入力待ちにならず usage を出す。

```sh
yulang run hello.yu
yulang run --print-roots hello.yu
yulang run -e "1 + 2" --print-roots
echo "1 + 2" | yulang run --print-roots
```

`say`、`println`、ほかの host operation によるプログラム出力は常に表示する。
root 式の値は `--print-roots` を付けた場合だけ表示する。

| Option | 作用 |
| --- | --- |
| `-e <source>`、`--eval <source>` | command line で渡した source を実行する |
| `--evidence-vm` | default の evidence VM backend を選ぶ |
| `--interpreter` | 単相 interpreter oracle を選ぶ |
| `--host <native\|unsupported\|mock-server>` | native host capability、host capability なし、in-process server host のいずれかを選ぶ |
| `--print-roots` | プログラム出力のあとに root 式の値を出す |
| `--print-nth` | 各出力結果に `Out N:` を付け、未処理の非決定分岐を駆動する |
| `--runtime-evidence-profile-deep` | runtime evidence の詳細な profiling counter を収集する |

`--print-nth` は、未処理の非決定分岐が作る各結果を表示する。

```sh
yulang run --print-nth -e '(each [1, 2]).say'
```

この command は `Out 1: 1` と `Out 2: 2` を出す。
`--print-nth` には evidence VM が必要である。
interpreter には native host mode も必要である。

## artifact の build

`build <path>` は entry ファイルを encoded control-IR artifact へ compile する。
`--out` がなければ、出力先は `target/yulang/yuir/<entry-stem>.yuir` になる。

| Option | 作用 |
| --- | --- |
| `--out <path>` | artifact を `<path>` へ書く |

```sh
yulang build --out app.yuir hello.yu
```

## test の実行

`test <path>` は、`mod test` module の binding と documentation test を検出する。
成功数と失敗数を出し、選択した test に失敗があれば status 1 で終了する。

| Option | 作用 |
| --- | --- |
| `--module <name>` | 指定した test module の test を実行する。複数回指定できる |
| `--binding <name>` | 指定した binding 名の test を実行する。複数回指定できる |
| `--show-passes` | 成功した test ごとに `PASS` 行を出す |

module filter と binding filter は組み合わせて適用する。
両方がある場合、module test は両方の集合に一致しなければならない。

```sh
yulang test --show-passes tests.yu
```

## contract manifest の実行

`contract <cases.toml>` は executable contract manifest の case を実行する。
この command はプロジェクトと release の検証に使う。

| Option | 作用 |
| --- | --- |
| `--repo-root <path>` | manifest の case path を `<path>` から解決する |
| `--case <name>` | 指定した case を実行する。複数回指定できる |
| `--contract <tag>` | 指定した contract tag を持つ case を実行する。複数回指定できる |

case filter と contract filter は組み合わせて適用する。
一致する case がない場合、または選択した case が失敗した場合は status 1 で終了する。

## compiler 出力の調査

サポート対象の調査 command は、compiler IR と parser event tree を出す。
出力形式は診断用であり、compiler とともに変わることがある。

### IR の dump

`dump <path> <selector>...` は 1 個以上の compiler 表現を出す。
selector が 1 個以上必要であり、複数指定した場合は次の表の順に出す。

| Selector | 出力 |
| --- | --- |
| `--core-ir`、`--poly` | principal な polymorphic IR |
| `--poly-raw` | raw polymorphic IR |
| `--runtime-ir`、`--mono`、`--runtime-finalize-ir`、`--finalized-ir` | specialize 済み monomorphic IR |
| `--control-evidence`、`--evidence-ir` | control evidence と、それに続く runtime-evidence surface |

```sh
yulang dump hello.yu --core-ir --runtime-ir
```

### 構文の parse

`parse [path] --as <mode>` はファイルの parser event tree を出す。
path がなければ標準入力を読む。

| Mode | 入力 |
| --- | --- |
| `expr` | 式 |
| `pat` | pattern |
| `stmt` | statement の列 |
| `type` | 型の式 |
| `mark` | Yumark ドキュメント |

```sh
echo "1 + 2" | yulang parse --as expr
```

## 標準ライブラリの install

`install std` は embedded 標準ライブラリを version 付きのユーザーライブラリ directory へ書く。
`--std-root <path>` を付けると、明示した root へ書く。
install した root は標準エラーに出す。

```sh
yulang install std
```

## キャッシュの管理

`cache` は選択した compiler キャッシュを調べるか削除する。
選択順は `YULANG_CACHE_DIR`、`XDG_CACHE_HOME`、platform default である。

```sh
yulang cache path
yulang cache stats
yulang cache clear
```

`path` はキャッシュ root を出す。
`stats` は compiler stage ごとの artifact と realm-resolution record を数える。
`clear` は選択したキャッシュ root 全体を削除し、root が既にない場合も成功する。

## realm の管理

realm command は `realm.toml` で記述した editable realm に作用する。
path を省略すると current directory を使う。

### realm の freeze

`realm freeze [path] --version <version>` は realm を immutable snapshot にする。
snapshot は `<path>/.yulang/versions/<version>` に作られる。
`realm.toml` に version がある場合、指定した version と一致しなければならない。

```sh
yulang realm freeze . --version 1.0.0
```

### local realm の install

`realm install [path] [--version <version>]` は editable realm を freeze する。
その snapshot をユーザーライブラリ root に install する。
manifest には local realm 名が必要である。
version は `--version` または `realm.toml` から取得できる。

```sh
yulang realm install .
```

## language server の起動

`server` は標準入力と標準出力を使う language server を起動する。
通常は editor integration がこの process を起動して監視する。

```sh
yulang server
```

## 非サポート surface と内部 surface

`debug` 以下の command と hidden test worker は compiler 開発用 surface である。
standalone IR compatibility command と low-level な `*-std` 表記は互換用 surface である。
これらはサポート対象の CLI リファレンスから意図して除外している。
代わりに `run`、`dump`、`install std` と、ここに記載した option を使う。
