# Yulang

**制御フローが型システムから見える。それでいて、スクリプトの気軽さで書ける言語。**

Yulang は、代数的 effect と全域の型推論を土台にした式指向の言語です。
ふつうの言語ならコアに溶接されているもの — early return、loop、可変状態、
例外、さらには非決定性の探索まで — を、型の付いたただの effect として扱い、
その大部分を標準ライブラリで定義しています。この設計から同時に二つのものが
手に入ります。ふつうは持てない制御フローと、「それがどこで使われているか」を
正確に教えてくれるコンパイラです。

**[ブラウザですぐ試せます](https://yulang.momota.pw/)** — インストール不要。
English: [README.md](README.md)

```yulang
// 15 未満のピタゴラス数をすべて — ただの式
{
    my a = each 1..15
    my b = each a..15
    my c = each b..15
    guard: a * a + b * b == c * c
    (a, b, c)
}.list  // => [(3, 4, 5), (5, 12, 13), (6, 8, 10), (9, 12, 15)]
```

`each` は要素を一つ選び、`guard:` は条件を満たさない枝を刈り、`.list` は
すべての結果を集めます。マクロでもクエリ DSL でもありません。この block は
`undet` effect を持つただの式で、型システムは他の型と同じようにそれを追跡します。

Yulang は alpha 段階の研究言語です。構文、型表示、effect semantics、
ライブラリ API はまだ変わります。それでも「入れて一晩遊ぶ」段階にはすでに
届いていて、このページの残りは、その一晩が何に値するかを見せるためにあります。

## 面白さ: effect はふつうのコード

effect の呼び出しは、見た目はふつうの関数呼び出しです。それを effect たらしめて
いるのは、*スタックの上にいる誰かがその意味を決める*という一点です。

```yulang
act flip:
    our coin: () -> bool

our all_paths(action: [flip] _) = catch action:
    flip::coin(), k -> all_paths(k true) + all_paths(k false)
    v -> [v]

all_paths:
    my a = if flip::coin(): 1 else: 0
    my b = if flip::coin(): 10 else: 0
    my c = if flip::coin(): 100 else: 0
    a + b + c
// => [111, 11, 101, 1, 110, 10, 100, 0]
```

この handler は継続 `k` を二回呼びます — 一度は `true` で、もう一度は `false` で。
だから直線的に書いたコードの一回の実行が、8 本の経路をすべて探索します。
これを多くの言語で書こうとするとプログラムを手で CPS 変換することになりますが、
ここでは 8 行です。そして型に現れる `[flip]` が、どのコードがコインを投げられる
のかを正確に示します。

標準ライブラリ自身も、同じ仕組みの上に自分の機能を組み立てています。

- `sub:` + `return` — early return は関数に溶接されたキーワードではなく、
  ライブラリの effect
- `for` と `last` / `next` / `redo` — loop は `Fold` role と loop effect に
  展開される
- `my $x` / `&x = v` — 可変参照は局所的な `var` effect にコンパイルされる
- `all` / `any` — `if` の条件が、多数の値をまとめて量化できる:

```yulang
if all [1, 2, 3] < any [3, 4, 5]:
    "every left dominated"
else:
    "no"
```

Raku の junction をご存じなら、まさにあれです — ただしここでは `all` と `any` は
非決定性の値を作るただのライブラリ関数で、左右のすべての組を試し終えたうえで、
外側の `if` には本物の `bool` が渡ります。

## 保証: 型がすべてを語る

すべての式は、値の型と *effect row* の両方を持ちます。失敗しうる、状態を変えうる、
探索しうる関数は、型にそう書いてあります — そして row が空なら、できません。

```yulang
pub error fs_err:
    not_found str
    denied str

our read_config(path: str): [fs_err] str =
    if path == "/etc/app.conf": "port = 8080"
    else: fail fs_err::not_found path
```

エラーは具体的な型を持つ代数的 effect で、名前を挙げて処理します。

```yulang
catch read_config "/missing":
    fs_err::not_found p, _ -> "(missing) %{p}"
    fs_err::denied p, _ -> "(denied) %{p}"
    value -> value
// => "(missing) /missing"
```

これが実際にもたらすもの:

- **見えない例外がない。** `anyhow` 流の、型を消した catch-all は意図的に
  ありません。すべてのエラーは effect row の中で具体的な型を保つので、
  どのエラーがどこで生まれ、どこで処理されるかが型だけから読めます。
  より広いエラー族は明示的に組み立て（`error io_err: fs from fs_err`）、
  effect を値として閉じたいときは一呼び出しです（`fs_err::wrap` が
  `result` を返します）。
- **状態は漏れない。** `my $x` は、その束縛のスコープに閉じた読み書きの口を
  開きます。ヒープのセルではなく effect なので、スコープの外へ参照が逃げると
  「たまに壊れるバグ」ではなく型エラーになります。
- **不意の暗黙変換がない。** 暗黙変換は宣言した場所にだけ存在します:
  `cast(x: user_id): int = x.raw`。
- **handler は書いたとおりのスコープで働く。** effect の伝播は静的にスコープ
  され、handler hygiene がライブラリの handler に「渡していない operation」を
  横取りさせません。規則の詳細は
  [type-theory notes](web/docs/ja/reference/type-theory.md) にあります。

そして、型を書く機会はほとんどありません。推論は Simple-sub 系で、subtyping、
構造的な record / tuple、effect row、role 制約まで含めて推論します。

```yulang
our twice x = x + x
// 推論結果: twice : Add<α> => α -> α
```

`+` は `int` に固定されていません。`twice` は `Add` role の実装を持つ任意の型で
動きます — そしてそれを、コンパイラが自分で突き止めます。

## 日常遣い: それでいて軽い

ここまでの仕組みは、頼まない限り姿を見せません。ふだんの Yulang は、
コンパクトなスクリプト言語のように読めます。

```yulang
say "Hello, World"
```

メソッドは型の宣言のすぐ隣に付き、チェーンできます。

```yulang
struct point { x: int, y: int } with:
    our p.norm2 = p.x * p.x + p.y * p.y

point { x: 3, y: 4 } .norm2  // => 25
```

デフォルト値付きの record パターンは、そのまま名前付きオプショナル引数に
なります。

```yulang
my area {width = 1, height = 2} = width * height

area { width: 3 }   // => 6
area {}             // => 2
```

symbol を使えば、enum を宣言せずにタグ付きの選択肢が書けます。payload の型は
タグごとに別でかまいません。

```yulang
my describe x = case x:
    :hello name -> "Hello, " + name
    :bye n -> "Bye %{n}"
// describe : :{ hello str, bye int } -> str
```

CLI はワンライナーとパイプに向いています。

```bash
yulang run -e "(each 1..20 + each 1..20).list.say"
echo "(each 1..3 + each 1..3).list.say" | yulang run
```

性能も「研究プロトタイプの罠」ではなく「日常のスクリプトなら十分」の域に
あります。warm cache なら、effect を多用する `examples/showcase.yu` が
default の evidence VM で 25ms 前後で実行され、標準ライブラリの `for` loop と
非決定性探索は、どちらも effect runtime を通ったうえで、直接再帰から一桁以内に
収まります。

## すぐ試す

いちばん速いのはブラウザの playground です:
**https://yulang.momota.pw/** — WebAssembly にコンパイルされた本物の
コンパイラと evidence VM が動きます。

Linux / macOS に CLI を入れる場合（binary は標準ライブラリを同梱していて、
初回に `~/.yulang` 以下へ配置します）:

```bash
curl -fsSL https://yulang.momota.pw/install.sh | sh -s -- --version v0.1.0-alpha.8
```

installer は `~/.yulang/bin` が `PATH` に無ければ shell profile へ追加します
（不要なら `--no-modify-path`）。terminal を開き直すか、今の terminal では
`~/.yulang/bin/yulang` を直接呼んでください。

Windows では:

```powershell
Invoke-WebRequest https://yulang.momota.pw/install.ps1 -OutFile install.ps1
powershell -ExecutionPolicy Bypass -File .\install.ps1 -Version v0.1.0-alpha.8
```

ファイルの実行と型検査:

```bash
yulang run examples/06_undet_once.yu
yulang check examples/08_types.yu
```

`run` は evidence VM でプログラムを実行し、`say` / `println` のように
プログラム側が出した出力だけを表示します。実験中に top-level 式の値も
覗きたいときは `--print-roots` を付けます。コンパイル成果物はユーザー cache
に保存されます（`yulang cache path|stats|clear`、一度だけ避けるなら
`--no-cache`）。cache の構成は [docs/cache.md](docs/cache.md) にあります。
別 checkout の標準ライブラリを使う場合は `YULANG_STD=/path/to/lib/std` を
指定します。

release install を消す場合:

```bash
curl -fsSL https://yulang.momota.pw/uninstall.sh | sh
```

```powershell
Invoke-WebRequest https://yulang.momota.pw/uninstall.ps1 -OutFile uninstall.ps1
powershell -ExecutionPolicy Bypass -File .\uninstall.ps1
```

repository の checkout から使う場合:

```bash
cargo build -p yulang
./target/debug/yulang run examples/06_undet_once.yu
```

## 次に読むもの

- [web/docs/ja/guide/tour.md](web/docs/ja/guide/tour.md): ガイド付きツアー。
  例はすべて playground でそのまま動きます。
- [docs/language/overview.ja.md](docs/language/overview.ja.md): 言語概要
  （[English](docs/language/overview.md)）。
- [web/docs/ja/reference/type-theory.md](web/docs/ja/reference/type-theory.md):
  effect row、handler hygiene、hidden handler evidence。
- [docs/status.md](docs/status.md): 推論・runtime・diagnostics・release
  artifact にわたる対応状況と公開契約。
- [examples/](examples): 実行できる example 集。[lib/std/](lib/std):
  Yulang 自身で書かれた標準ライブラリ。

まず動かすなら、このあたりが読みやすいです。

- `examples/showcase.yu`: 構文とライブラリの広めの tour。
- `examples/06_undet_once.yu`: ライブラリ effect による非決定性。
- `examples/10_effect_handler.yu`: 代数的 effect handler。
- `examples/04_sub_return.yu`: `sub:` による局所 early return。
- `examples/11_attached_impl.yu`: role implementation の attached form。

`rule { ... }` や `~"..."` のような parser-combinator まわりの糖衣構文は
実験段階です。言語の方向性を試すには使えますが、互換性の約束はありません。

## Tooling

`yulang server` で language server が起動します（semantic tokens、
full-document sync、現行 lowering diagnostics）。Zed 対応は
[yulang-zed/](yulang-zed) にあり、extension は install 済み binary から
`yulang server` を起動するので、release archive とエディタ統合が同じ実行
ファイルを共有します。この repository 内の source copy は、別 repository の
`momota1029/yulang-zed` と同期して管理する対象です。

## 内部構成

Yulang には現在 3 つの runtime surface があります。evidence VM（default の
`run` 経路で、effect の重いプログラムでは最速）、control VM（`run
--control-vm` で使える fallback 経路）、mono runtime（oracle として残している
単純な interpreter、`run --interpreter`）です。ブラウザ playground は wasm
crate 経由で evidence VM を使います。evidence VM は control VM と突き合わせて
検査できます。

```bash
target/release/yulang --std-root lib debug evidence-vm-run --compare-control examples/showcase.yu
```

evidence VM は、証明済みの direct-tail handler 経路では permission-native な
handler visibility を使い、generic request machinery を fallback surface として
残しています。以前 旧実装で試した Cranelift/MMTk native backend は退役済みで、
メモは [docs/native-backend.md](docs/native-backend.md) と
[docs/native-experimental-release.md](docs/native-experimental-release.md) に
残っています。

## 開発

代表的な Rust test suite:

```bash
cargo test -p sources -p infer -p poly -p specialize -p yulang
```

release 相当の変更を push する前には、ローカルの release gate を回します。
formatting、test suite、release build、hardening smoke、docs build までを
まとめて確認します（環境変数による切り替えは script 本体を参照）。

```bash
scripts/release-gate.sh
```

公開契約の manifest は `tests/yulang/cases.toml` にあり、公開 `yulang` CLI の
テストから検査されます。

Repository layout:

- `crates/yulang`: CLI と language server の入口。
- `crates/sources`: source collection、CST input、std install、realm freeze。
- `crates/infer`: CST → `poly` lowering と型推論。
- `crates/poly`: 推論済み polymorphic program 表現。
- `crates/specialize`: principal monomorphization。
- `crates/mono` / `crates/mono-runtime`: monomorphic IR と oracle interpreter。
- `crates/control-vm` / `crates/evidence-vm`: 2 つの VM runtime。
- `crates/parser`: parser と syntax tree。
- `lib/std`: Yulang で書かれた標準ライブラリ。
- `examples`, `web/`, `docs/`, `notes/`: example、playground / docs の
  source、ドキュメント、作業メモ。
- `archive/crates`: 旧実装。参照専用。

## Status

Yulang は pre-release の研究言語です。構文、型表示、runtime IR、VM、
標準ライブラリには互換性の約束がありません。今の対応状況は
[docs/status.md](docs/status.md) にあります。

## License

Licensed under either of:

- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE))
- MIT License ([LICENSE-MIT](LICENSE-MIT))

at your option.
