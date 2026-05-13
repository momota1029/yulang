# インストール

Yulang はまだ実験段階の言語です。まず触るだけなら Playground が一番早いです。
ローカル CLI は、今のところ開発と回帰テスト向けの位置付けが強いです。

## Playground

<a href="/" target="_self">Playground</a> を開くと、ブラウザ上で Yulang を実行できます。
標準ライブラリとドキュメントの例も同じ経路で動きます。

## ソースから動かす

```sh
git clone https://github.com/momota1029/yulang.git
cd yulang
cargo test
cargo run -p yulang -- path/to/file.yu
```

ローカルで試す場合に重要なのは `cargo run -p yulang -- path/to/file.yu` です。
下の web deploy は、hosted playground / docs を更新する場合だけ必要です。

## 公開 CLI

Cargo で main CLI を入れ、embedded standard library を配置します。

```sh
cargo install yulang
yulang install std
```

その後は、そのまま program を実行したり、型を表示したりできます。

```sh
yulang run examples/06_undet_once.yu
yulang check examples/08_types.yu
```

language server も同じ binary に入っています。

```sh
yulang server
```

Zed extension はまだ public registry には出していません。現時点では、この repository の
`yulang-zed/` を Zed dev extension として読み込むと使えます。worktree environment か
`~/.cargo/bin` に `yulang` binary があれば、extension が `yulang server` を起動します。

主な crate は次の通りです。

| Crate | 役割 |
|-------|------|
| `yulang-parser` | 構文解析と operator parsing |
| `yulang-infer` | lowering、名前解決、型推論、core export |
| `yulang-runtime` | runtime lowering、monomorphize、VM compile/eval |
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
