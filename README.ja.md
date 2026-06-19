# Yulang

Yulang は、代数的 effect と handler をふつうの制御構文として使えるようにする
実験的なプログラミング言語です。

見た目は小さな式指向のスクリプト言語に近く、method 呼び出し、compact な block
記法、struct、enum、role、ユーザー定義 operator、loop、early return、参照を持ちます。
特徴的なのは、通常なら言語コアに固定されがちな制御の多くを、effect、handler、
role、標準ライブラリの組み合わせとして扱う点です。

現在の Yulang は alpha 段階の研究言語です。現行実装は `yulang` pipeline にあり、
構文、型表示、effect semantics、runtime IR、標準ライブラリ API はまだ変わります。

English: [README.md](README.md)

## すぐ試す

release build の CLI を使う場合は、OS ごとの binary archive を入れます。binary には
embedded standard library が入っていて、初回にユーザー library directory へ配置されます。

```bash
curl -fsSL https://yulang.momota.pw/install.sh | sh -s -- --version v0.1.0-alpha.1
```

installer は `~/.yulang/bin` が `PATH` に無い場合、shell profile へ追加します。
反映には terminal の再起動が必要です。自分で `PATH` を管理したい場合は
`--no-modify-path` を付けます。

今開いている terminal でそのまま動かす場合は、install 先を直接指定します。

```bash
~/.yulang/bin/yulang run examples/06_undet_once.yu
```

Windows では PowerShell installer を使います。

```powershell
Invoke-WebRequest https://yulang.momota.pw/install.ps1 -OutFile install.ps1
powershell -ExecutionPolicy Bypass -File .\install.ps1 -Version v0.1.0-alpha.1
```

PowerShell installer は install 先の `bin` directory を user `PATH` に追加します。
不要な場合は `-NoModifyPath` を付けます。

release install を消す場合は uninstaller を使います。

```bash
curl -fsSL https://yulang.momota.pw/uninstall.sh | sh
```

Windows では次の形です。

```powershell
Invoke-WebRequest https://yulang.momota.pw/uninstall.ps1 -OutFile uninstall.ps1
powershell -ExecutionPolicy Bypass -File .\uninstall.ps1
```

開発 checkout で CLI を使う場合は、`yulang` を build します。ユーザー cache に標準ライブラリを
置きたい場合は `install std` も使えます。

```bash
cargo build -p yulang
./target/debug/yulang install std
```

ファイルを実行します。

```bash
./target/debug/yulang run examples/06_undet_once.yu
```

最小の完全な program は、`say` でユーザー向け文字列を出す形です。

```yulang
say "Hello, World"
```

`run` は現行 control VM を通じてプログラムを実行し、`say` / `println` のように
プログラム側が出した出力だけを表示します。途中の root 値も覗きたいときは
`--print-roots` を付けます。control VM ではなく mono runtime で動かしたい場合は
`--interpreter` を付けます。

型検査と public type の表示だけ行う場合は `check` を使います。

```bash
./target/debug/yulang check examples/08_types.yu
```

標準ライブラリは通常 `~/.yulang/lib/yulang-0.1.4/std` に入ります。
`yulang run`、`yulang check`、`yulang server` は、`YULANG_STD` や近くの
`lib/std` が見つからない場合、同梱標準ライブラリを初回に自動で配置します。

別 checkout の標準ライブラリを使いたい場合は `YULANG_STD` を指定します。

```bash
export YULANG_STD=/path/to/yulang/lib/std
```

## 最初の例

```yulang
// 非決定性で探索: 15 未満のピタゴラス数の組
{
    my a = each 1..15
    my b = each a..15
    my c = each b..15
    guard: a * a + b * b == c * c
    (a, b, c)
}.list  // => [(3, 4, 5), (5, 12, 13), (6, 8, 10), (9, 12, 15)]
```

`each` は非決定性の値を返し、`guard:` は条件を満たさない枝を切り、
`.list` は探索結果を具体的なリストに畳みます。block 全体は `undet`
effect を持つただの式で、構文として特別扱いされている部分はありません。

同じ仕組みで、比較を「いくつもの選択肢」へ持ち上げることもできます。

```yulang
// junction は比較を選択肢の組すべてに広げる
if all [1, 2, 3] < any [3, 4, 5]:
    "every left dominated"
else:
    "no"
```

`all` と `any` は非決定性の値を作る標準ライブラリ関数です。lowering が
`junction::junction` を挿入し、左右のすべての組を試したうえで周囲の
`if` には `bool` が渡ります。

可変状態、early return、loop、effectful な条件式も、同じ考え方で扱います。
見た目はふつうの制御構文に寄せつつ、内部では型付き effect と小さなライブラリに
分けて表現します。

## 次に読むもの

- [docs/language/overview.ja.md](docs/language/overview.ja.md):
  日本語の言語概要。
- [docs/language/overview.md](docs/language/overview.md):
  英語の言語概要。
- [docs/status.md](docs/status.md):
  parser、型推論、runtime、archive 済み surface ごとの対応状況。
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
./target/debug/yulang server
```

現在の主な機能は次の通りです。

- semantic token
- full-document sync
- 現行 lowering diagnostic

Zed 用 extension は [yulang-zed/](yulang-zed) にあります。extension は install 済み
`yulang` binary から `yulang server` を起動します。この repository 内の source copy は、
別 repository の `momota1029/yulang-zed` と同期して管理する対象です。

## 実行 backend

Yulang は現在、specialize 後の mono IR を読む mono runtime と、そこから軽量表現へ
落とした control VM で実行されます。以前は Cranelift/MMTk ベースの native backend も
旧実装側で試していましたが、現在は退役済みです。

当時の実験ログや、そこから派生した optimizer の方針はこのあたりに残しています。

- [docs/native-experimental-release.md](docs/native-experimental-release.md):
  封印した opt-in native subset の release-gate メモ。
- [docs/native-backend.md](docs/native-backend.md):
  native backend の対応範囲と当時の制限のアーカイブ。
- [archive/notes/design/cps-optimization-pass-plan.md](archive/notes/design/cps-optimization-pass-plan.md):
  CPS optimizer と代数的 effect の rewrite 計画。

## 開発

代表的な Rust test suite を走らせる例です。

```bash
cargo test -p sources -p infer -p poly -p specialize -p yulang
```

inline program も実行できます。

```bash
printf '1\n' >/tmp/yulang-main.yu
./target/debug/yulang run --print-roots /tmp/yulang-main.yu
```

## Repository Layout

- `crates/yulang`: 現行 CLI と language server の入口。
- `crates/sources`: source collection、CST input、std install support、realm freeze。
- `crates/infer`: CST → `poly` lowering と型推論。
- `crates/poly`: 推論済み polymorphic program 表現。
- `crates/specialize`: principal monomorphization。
- `crates/mono`: monomorphic IR。
- `crates/mono-runtime`: oracle-style mono interpreter。
- `crates/control-vm`: 軽量 control VM IR と runtime。
- `crates/parser`: parser と syntax tree。
- `crates/list-tree`: 共有 persistent list 実装。
- `archive/crates`: 旧 `yulang` 実装。workspace 外の参照用 code。
- `examples`: 現在の実装で動く example。
- `lib/std`: Yulang で書かれた標準ライブラリ。
- `web/playground`: legacy Vite based browser playground source。現行 workspace の build 対象ではない。
- `web/docs`: reference documentation。
- `notes`: bug、refactor、作業メモ。

## Status

Yulang は pre-release research software です。構文、型表示、runtime IR、runtime、
標準ライブラリには互換性の約束がありません。
今の対応状況は [docs/status.md](docs/status.md) にあります。

## License

Licensed under either of:

- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE))
- MIT License ([LICENSE-MIT](LICENSE-MIT))

at your option.
