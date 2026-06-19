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
cargo run -p yulang -- run path/to/file.yu
```

ローカルで試す場合に重要なのは `cargo run -p yulang -- run path/to/file.yu` です（`run` の代わりに `check` を渡すと推論型を表示します）。
下の web deploy は、hosted playground / docs を更新する場合だけ必要です。

## Binary release

OS ごとの release archive を入れます。binary には embedded standard library が入り、
初回にユーザー library directory へ配置されます。

```sh
curl -fsSL https://raw.githubusercontent.com/momota1029/yulang/main/scripts/install.sh | sh -s -- --version v0.1.0-alpha.1
```

その後は、そのまま program を実行したり、型を表示したりできます。

```sh
yulang run examples/06_undet_once.yu
yulang check examples/08_types.yu
```

`yulang run` が標準で出すのは `say` / `println` など program 自身の出力だけです。CLI で root 式の値を確認したいときは `yulang run --print-roots ...` を使います。

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
