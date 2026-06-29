# インストール

Yulang はまだ実験段階の言語です。ガイドをローカルで追う場合は、
まず release CLI を入れて、小さい `.yu` ファイルが動くことを確認します。
インストールせずに例だけ試すなら Playground が一番早いです。

## Binary release

OS ごとの release archive を入れます。binary には embedded standard library が入り、
初回にユーザー library directory へ配置されます。

```sh
curl -fsSL https://yulang.momota.pw/install.sh | sh -s -- --version v0.1.0-alpha.5
```

installer は `~/.yulang/bin` が `PATH` に無い場合、shell profile へ追加します。
反映には terminal の再起動が必要です。自分で `PATH` を管理したい場合は
`--no-modify-path` を渡します。

Windows では次の形です。

```powershell
Invoke-WebRequest https://yulang.momota.pw/install.ps1 -OutFile install.ps1
powershell -ExecutionPolicy Bypass -File .\install.ps1 -Version v0.1.0-alpha.5
```

PowerShell installer は install 先の `bin` directory を user `PATH` に追加します。
この処理を省く場合は `-NoModifyPath` を渡します。

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
推論型を見る場合は `run` の代わりに `check` を使います。

```sh
yulang check hello.yu
```

一行で試したい場合は、`-e`、明示 stdin の `-`、または pipe 入力も使えます。

```sh
yulang run -e "(each 1..20 + each 1..20).list.say"
echo "1 + 2" | yulang run --print-roots
echo "1" | yulang run --print-roots -
```

interactive terminal 上で引数なしの `yulang run` を実行した場合は、入力待ちにはならず usage を表示します。

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

language server も同じ binary に入っています。

```sh
yulang server
```

Zed extension は install 済み `yulang` binary から `yulang server` を起動します。
探索先は worktree environment、`~/.yulang/bin`、`~/.cargo/bin` です。source copy は
`yulang-zed/` に置き、別 repository の extension と同期して管理します。

主な crate は次の通りです。

| Crate | 役割 |
|-------|------|
| `yulang-parser` | 構文解析と operator parsing |
| `yulang-infer` | lowering、名前解決、型推論、core export |
| `yulang-runtime-ir` | runtime IR data structures と RuntimeType |
| `yulang-runtime-types` | runtime type 表現と type-system helpers |
| `yulang-runtime-refine` | refine / validate / invariant / hygiene |
| `yulang-runtime-lower` | core IR → runtime IR の lower pass |
| `yulang-monomorphize` | type graph 解決と monomorphize pass |
| `yulang-vm` | VM compile / evaluation |
| `yulang-wasm` | playground から呼ぶ wasm API |

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
