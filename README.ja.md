# Yulang

Yulang は、代数的 effect と handler をふつうの制御構文として使えるようにする
実験的なプログラミング言語です。

見た目は小さな式指向のスクリプト言語に近く、method 呼び出し、compact な block
記法、struct、enum、role、ユーザー定義 operator、loop、early return、参照を持ちます。
特徴的なのは、通常なら言語コアに固定されがちな制御の多くを、effect、handler、
role、標準ライブラリの組み合わせとして扱う点です。

現在の Yulang は alpha 段階の研究言語です。interpreter、playground、標準
ライブラリ、language server は実例を試せる程度に動きますが、構文、型表示、effect
semantics、native backend、標準ライブラリ API はまだ変わります。

English: [README.md](README.md)

## すぐ試す

ブラウザで試すなら playground が一番早い入口です。

<https://yulang.momota.pw>

手元で CLI を使う場合は、まず binary と標準ライブラリを入れます。

```bash
cargo install yulang
yulang install std
```

ファイルを interpreter で実行します。

```bash
yulang run examples/06_undet_once.yu
```

型検査と public type の表示だけ行う場合は `check` を使います。

```bash
yulang check examples/08_types.yu
```

native backend を試す場合は `--native` を付けます。

```bash
yulang run --native examples/06_undet_once.yu
```

標準ライブラリは通常 `~/.yulang/lib/yulang-0.1.0/std` に入ります。
`yulang run`、`yulang check`、`yulang server` は、`YULANG_STD` や近くの
`lib/std` が見つからない場合、同梱標準ライブラリを初回に自動で配置します。

別 checkout の標準ライブラリを使いたい場合は `YULANG_STD` を指定します。

```bash
export YULANG_STD=/path/to/yulang/lib/std
```

## 最初の例

```yulang
use std::undet::*

struct point { x: int, y: int } with:
    our p.norm2 = p.x * p.x + p.y * p.y

if all [1, 2, 3] < any [2, 3, 4]:
    point { x: 3, y: 4 } .norm2
else:
    0
```

`all [1, 2, 3] < any [2, 3, 4]` は特別な構文ではありません。`all` と
`any` は、非決定性を表す値を作る標準ライブラリ関数です。lowering が
`junction::junction` を挿入し、周囲の `if` が要求する `bool` へつなぎます。

可変状態、early return、loop、effectful な条件式も、同じ考え方で扱います。
見た目はふつうの制御構文に寄せつつ、内部では型付き effect と小さなライブラリに
分けて表現します。

## 次に読むもの

- [docs/language/overview.ja.md](docs/language/overview.ja.md):
  日本語の言語概要。
- [docs/language/overview.md](docs/language/overview.md):
  英語の言語概要。
- [docs/status.md](docs/status.md):
  parser、型推論、interpreter、playground、native backend ごとの対応状況。
- [docs/native-backend.md](docs/native-backend.md):
  native backend の対応範囲、CLI、現在の制限。
- [web/docs/ja/reference/type-theory.md](web/docs/ja/reference/type-theory.md):
  effect row、handler hygiene、hidden handler evidence の公開仕様側の説明。
- [docs/hidden-effect-evidence.ja.md](docs/hidden-effect-evidence.ja.md):
  hidden effect evidence の実装メモ。
- [examples/](examples):
  実行できる小さなサンプル集。
- [lib/std/](lib/std):
  Yulang で書かれた標準ライブラリ。

まず動かすなら、このあたりの example が読みやすいです。

- `examples/showcase.yu`: 構文とライブラリの広めの tour。
- `examples/06_undet_once.yu`: ライブラリ effect による非決定性。
- `examples/10_effect_handler.yu`: 代数的 effect handler。
- `examples/04_sub_return.yu`: `sub:` による局所 early return。
- `examples/11_attached_impl.yu`: role implementation の attached form。

## Language Server

language server は `yulang server` で起動します。

```bash
yulang server
```

現在の主な機能は次の通りです。

- inferred value、local、method、多くの type reference の hover
- semantic token
- document symbol
- parser / lowering / type error の diagnostic
- 多くの type error に対する `relatedInformation`

Zed 用 extension は [yulang-zed/](yulang-zed) にあります。まだ Zed extension
registry には公開していないため、Zed の dev extension として `yulang-zed`
directory を指定します。worktree の環境または `~/.cargo/bin` に `yulang`
binary があれば、extension は `yulang server` を自動起動します。

古い `yulang-ls` binary は deprecated stub で、現在は `yulang server` に委譲します。

## Native Backend

native backend は prototype です。通常の入口は次の command です。

```bash
yulang run --native path/to/file.yu
```

artifact 生成や backend の debug には `yulang native` も使えます。interpreter が
現在の意味論の基準で、native backend は対応 subset を広げている途中です。
対応済みの feature、既知の制限、CLI の詳細は
[docs/native-backend.md](docs/native-backend.md) にまとめています。

## 開発

代表的な Rust test suite を走らせる例です。

```bash
cargo test -p yulang-monomorphize -p yulang-infer --lib
```

playground を手元で build します。

```bash
cd web/playground
npm ci
npm run build
```

inline program も実行できます。

```bash
yulang run <<'YU'
use std::undet::*

(each [1, 2, 3] + each [4, 5, 6]).once
YU
```

## Repository Layout

- `crates/yulang`: CLI。
- `crates/yulang-parser`: parser と syntax tree。
- `crates/yulang-sources`: source set、realm、compilation unit、syntax artifact。
- `crates/yulang-typed-ir`: typed intermediate representation と principal-type evidence。
- `crates/yulang-infer`: 型推論と principal type export。
- `crates/yulang-runtime-ir`: runtime IR data structures と `RuntimeType` 定義。
- `crates/yulang-runtime-types`: runtime type 表現と type-system helpers。
- `crates/yulang-runtime-refine`: refine / validate / invariant / hygiene pass。
- `crates/yulang-runtime-lower`: core IR → runtime IR の lower pass。
- `crates/yulang-monomorphize`: type graph 解決と monomorphize pass。
- `crates/yulang-vm`: VM compile と evaluation。
- `crates/yulang-wasm`: playground から使う WebAssembly API。
- `examples`: 現在の実装で動く example。
- `lib/std`: Yulang で書かれた標準ライブラリ。
- `web/playground`: Vite based browser playground。
- `web/docs`: reference documentation。
- `notes`: bug、refactor、作業メモ。

## Status

Yulang は pre-release research software です。構文、型表示、runtime IR、
interpreter、標準ライブラリには互換性の約束がありません。

今の対応状況は [docs/status.md](docs/status.md) にあります。native backend の
詳しい制限は [docs/native-backend.md](docs/native-backend.md) を読んでください。

## License

Licensed under either of:

- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE))
- MIT License ([LICENSE-MIT](LICENSE-MIT))

at your option.
