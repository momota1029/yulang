# インストール

Yulang はまだ実験段階の言語です。ガイドをローカルで追う場合は、
まず release CLI を入れて、小さい `.yu` ファイルが動くことを確認します。
インストールせずに例だけ試すなら Playground が一番早いです。

## Binary release

OS ごとの release archive を入れます。binary には embedded standard library が入り、
初回にユーザー library directory へ配置されます。

```sh
curl -fsSL https://yulang.momota.pw/install.sh | sh
```

installer は `~/.yulang/bin` が `PATH` に無い場合、shell profile へ追加します。
反映には terminal の再起動が必要です。自分で `PATH` を管理したい場合は
`--no-modify-path` を渡します。

version 指定なしでは、prerelease を含む最新の公開 GitHub release を入れます。
この release に固定する場合は次のようにします。

```sh
curl -fsSL https://yulang.momota.pw/install.sh | sh -s -- --version v0.1.0-alpha.10
```

Windows では次の形です。

```powershell
Invoke-WebRequest https://yulang.momota.pw/install.ps1 -OutFile install.ps1
powershell -ExecutionPolicy Bypass -File .\install.ps1
```

PowerShell installer は install 先の `bin` directory を user `PATH` に追加します。
この処理を省く場合は `-NoModifyPath` を渡します。

現在の release に固定する場合は `-Version v0.1.0-alpha.10` を渡します。

## ファイルが動くか確認する

`hello.yu` を作ります。

```sh
cat > hello.yu <<'YU'
println "hello from Yulang"
1 + 2
YU
yulang run --print-roots hello.yu
```

期待する出力は次の形です。

```text
hello from Yulang
run roots [(), 3]
```

`yulang run` が標準で出すのは `say` / `println` など program 自身の出力だけです。
CLI で root 式の値を確認したいときは `yulang run --print-roots ...` を使います。
`yulang check hello.yu` は file を検査します。
成功時は何も出力せず、失敗時だけ diagnostic を出します。

```sh
yulang check hello.yu
```

推論された binding 型を含む compiler IR を見る場合は `yulang dump hello.yu --poly` を使います。

一行で試したい場合は、`-e`、明示 stdin の `-`、または pipe 入力も使えます。

```sh
yulang run -e "(each 1..20 + each 1..20).list.say"
echo "1 + 2" | yulang run --print-roots
echo "1" | yulang run --print-roots -
```

interactive terminal 上で引数なしの `yulang run` を実行した場合は、入力待ちにはならず usage を表示します。

## アンインストール

release install を消す場合は uninstaller を使います。

```sh
curl -fsSL https://yulang.momota.pw/uninstall.sh | sh
```

Windows では次の形です。

```powershell
Invoke-WebRequest https://yulang.momota.pw/uninstall.ps1 -OutFile uninstall.ps1
powershell -ExecutionPolicy Bypass -File .\uninstall.ps1
```

## Playground

<a href="/" target="_self">Playground</a> を開くと、ブラウザ上で Yulang を実行できます。
標準ライブラリとドキュメントの例も同じ経路で動きます。

## ソースから動かす

repository を clone し、Cargo で実行します。

```sh
git clone https://github.com/momota1029/yulang.git
cd yulang
cargo test
cargo run -p yulang -- run path/to/file.yu
```

source tree から試す場合に重要なのは `cargo run -p yulang -- run path/to/file.yu` です。
下の web deploy は、hosted playground / docs を更新する場合だけ必要です。

CLI はユーザー cache root にコンパイラ artifact を保存します。`.yucu`、`.yuir`、`.yuvm`
と、`--runtime-phase-timings` が出す route label については
[キャッシュ](./cache) にまとめています。

### language server

language server も同じ binary に入っています。

```sh
yulang server
```

Zed extension は install 済み `yulang` binary から `yulang server` を起動します。
active worktree environment から `yulang` を解決します。
そこに binary がない場合は、Zed settings の `lsp.yulang.binary.path` に `/home/me/.yulang/bin/yulang` のような絶対 path を設定します。
source copy は `yulang-zed/` に置き、別 repository の extension と同期して管理します。

### Zed development extension

repository の submodule から extension source を取得します。

```sh
git submodule update --init yulang-zed
```

Zed で command palette を開き、`zed: install dev extension` を実行して、
`yulang-zed/` directory を選びます。

extension から `yulang server` を起動するには、`yulang` が `PATH` から見える必要があります。
binary が別の場所にある場合は、[extension README](https://github.com/momota1029/yulang-zed#language-server)
に従って Zed settings の `lsp.yulang.binary.path` を設定します。

### compiler workspace

repository は Rust workspace です。現在の compiler と runtime の主経路は次の通りです。

`source files → sources/parser → infer/poly → specialize/mono → control-ir → evidence-vm`

主な crate は次の通りです。

| Crate | 役割 |
|-------|------|
| `sources`, `parser` | source file を集め、concrete syntax と operator table を作る |
| `infer`, `poly` | 型を推論し、多相 IR を作る |
| `specialize`, `mono` | program を specialize して単相 IR にする |
| `control-ir`, `evidence-vm` | control IR へ lower し、CLI default backend で実行する |
| `mono-runtime` | `mono` program を直接読み、`--interpreter` oracle として動かす |
| `wasm` | playground が使う browser 向け WebAssembly API を出す |
| `yulang`, `yulang-editor` | CLI/source pipeline と editor 向け integration を担う |

## Web build

```sh
npm --prefix web install
npm --prefix web run build
```

任意のディレクトリへ配置する場合は次のようにします。

```sh
YULANG_DEPLOY_DIR=/path/to/site npm --prefix web run deploy:dir
```

生成されたサイトでは `/` が playground、`/guide/` と `/reference/` が英語 docs、
`/ja/guide/` と `/ja/reference/` が日本語 docs になります。

## 現在の制限

- 言語仕様と標準ライブラリはまだ変わります。
- filesystem API は native host 向けで、playground では unresolved request のまま残ります。
- wasm bundle は標準ライブラリ artifact を埋め込みますが、保守的に source compile fallback も持っています。
