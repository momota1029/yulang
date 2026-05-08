# インストール

Yulang はまだ実験段階の言語です。まず触るだけなら Playground が一番早いです。
ローカル CLI は、今のところ開発と回帰テスト向けの位置付けが強いです。

## Playground

<a href="/" target="_self">Playground</a> を開くと、ブラウザ上で Yulang を実行できる。
標準ライブラリとドキュメントの例も同じ経路で動く。

## ソースから動かす

```sh
git clone https://github.com/momota1029/yulang.git
cd yulang
cargo test
cargo run -p yulang -- path/to/file.yu
```

ローカルで試す場合に重要なのは `cargo run -p yulang -- path/to/file.yu` です。
下の web deploy は、hosted playground / docs を更新する場合だけ必要です。

主な crate は次の通り。

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

任意のディレクトリへ配置する場合:

```sh
YULANG_DEPLOY_DIR=/path/to/site npm --prefix web run deploy:dir
```

生成されたサイトでは `/` が playground、`/guide/` と `/reference/` が英語 docs、
`/ja/guide/` と `/ja/reference/` が日本語 docs になる。

## 現在の制限

- 言語仕様と標準ライブラリはまだ変わる。
- filesystem API は native host 向けで、playground では unresolved request のまま残る。
- wasm bundle は標準ライブラリ artifact を埋め込むが、保守的に source compile fallback も持つ。
