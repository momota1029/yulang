見たよ〜。かなり育っているので、いちばん大きい改善方針は **「実験言語としての奥行き」よりも「使う人が迷わない契約」を前に出す** ことだと思うねぇ。

Yulangの核はもう強いよ。READMEでも「普通の制御機構を algebraic effects / handlers / roles / std で組み、見た目は普通の軽量言語に寄せる」とかなり明確に打ち出せているし、overviewでも型推論・role・effect・`sub`・`for`・参照・非決定性まで一通り説明されているねぇ。
なので、今は新しい大技を増やすより、**どこまで安定していて、どこから研究中なのか** を切り分けると、全体がかなり強く見えると思うよ〜。

## まず一番おすすめ：機能ごとの「安定度表」を作る

Yulangは、parserにはあるけど意味がまだ固まっていないもの、推論はできるけど runtime では限定的なもの、playground と CLI で host capability の扱いが違うものがあるねぇ。overviewにも rule / mark syntax は parse できるが通常の式としての意味は未実装、と書かれているし、runtime lowering / monomorphization の制限にも触れている。

ここを隠さず、むしろ表にするとよさそう。

```text
Feature                Parse  Infer  VM Run  Playground  Archived Native  Docs
struct / enum          ✅     ✅     ✅      ✅          historical       ✅
roles / operators      ✅     ✅     ✅      ✅          historical       △
effects / handlers     ✅     ✅     ✅      ✅          historical       △
sub / return           ✅     ✅     ✅      ✅          historical       ✅
for / last / next      ✅     ✅     ✅      ✅          historical       △
references             ✅     ✅     ✅      ✅          historical       △
rule / mark expr       ✅     ?      ❌      ❌          ❌              ⚠️
filesystem             ✅     △      △      ❌          ❌              ⚠️
```

これは単なるREADME表でもいいけれど、できれば `docs/status.md` みたいな場所に置くのがよさそうだよ〜。
Yulangは実験的だからこそ、「未完成」が弱点というより、**研究対象が整理されている** ように見せられるのが大事だと思うねぇ。

## 次に効きそう：diagnostics を仕様の一部にする

`notes/todo/diagnostics-docs.md` に、parser errors、type errors、role/method errors、effect errors、runtime/lowering errors をユーザー向けに整える方針がすでに書かれているねぇ。特に「内部実装詳細ではなく、言語レベルの原因を説明する」という目的はかなり正しいと思う。

ここは優先度高めでよさそう。

おすすめは、最初から全部きれいにするより、**代表的な失敗例を10個だけ固定する**こと。

たとえば：

```text
diagnostics/
  parser/
    unexpected-token.yu
    bad-indent.yu
  type/
    int-plus-string.yu
    missing-field.yu
  role/
    missing-add-impl.yu
    ambiguous-method.yu
  effect/
    unhandled-console-read.yu
    handler-arm-mismatch.yu
  runtime/
    residual-polymorphic-runtime-ir.yu
```

それぞれに期待出力をつける。

```text
expected:
  error: cannot use + here
  expected: Add<str> or numeric-compatible value
  actual: int and str
```

ポイントは、全文 golden をガチガチに固定しすぎないことだねぇ。`testing.md` でも diagnostics 全文を広く固定しすぎない、と書かれているから、方向は合っていると思う。

## Yulang-facing test API を早めに作る

これもすでにTODOにあって、かなり良いと思う。`testing.md` では「Yulang test file -> compile / infer / run -> assertion result -> compact diagnostics」という形が目標になっているねぇ。

今のYulangは機能が多いので、Rust側の回帰テストだけだと、言語としての体験が見えにくくなると思う。最初は専用構文を増やさず、標準ライブラリに小さいテストAPIを置くのがよさそう。

```yulang
use std::test::*

test "list update":
    my $xs = [2, 3, 4]
    &xs[1] = 6
    assert_eq $xs [2, 6, 4]
```

ただ、`test` 構文を急いで入れる必要はなくて、最初は CLI 側で

```text
--test tests/yulang/*.yu
```

を読み、各ファイルの root results を見てもいいかも。
最小ならこういうコメントメタデータでも足りるねぇ。

```yulang
// expect-run: [2, 6, 4]

my $xs = [2, 3, 4]
&xs[1] = 6
$xs
```

これは地味だけど、Yulangみたいに parser / infer / runtime / wasm が分かれている言語では、かなり効くと思うよ〜。

## READMEは少し短くして、「入口」と「現状」を分ける

READMEは情報量が多くて、今の開発状況を追うには便利。でも初見の人には、archived native progress の長い記録がやや重いかもしれないねぇ。READMEには repository layout、commands、archive links まで入っている。

おすすめはこんな分割。

```text
README.md
  - Yulangとは
  - 30秒で動かす
  - 代表例 1つ
  - Playground
  - 次に読む場所

docs/status.md
  - Feature support matrix
  - VM / archived native / wasm status
  - Known limitations

docs/native-backend.md
  - archived native backend summary
  - historical release-gate subset
  - links to deeper design notes

docs/language/overview.ja.md
docs/language/overview.md
  - 今の通り、ユーザー向け説明
```

READMEの「Native Backend Progress」は、今は `docs/native-backend.md` 側の archived note に逃がした状態として扱う。

## CLIは `clap` か小さい command 分割に寄せると楽そう

`crates/yulang/src/main.rs` を見ると、CLI option が手書きでかなり増えているねぇ。`--infer`、`--core-ir`、`--runtime-ir`、`--hygiene-ir`、`--run`、profile 系、parse 系などが同じ `CliOptions` に入っている。

今後さらに `--test`、diagnostics golden、package/cache、debug subcommands が増えるなら、手書き parser はちょっと重くなりそう。

候補は2つ。

### 1. `clap` に移す

```text
yulang run file.yu
yulang infer file.yu
yulang parse expr
yulang debug core-ir file.yu
yulang debug control-vm file.yu
yulang cache path
```

### 2. 今のままでも、内部だけ command enum にする

```rust
enum Command {
    Infer,
    RunVm,
    CoreIr,
    RuntimeIr,
    Parse(ParserMode),
    Debug(DebugCommand),
    Cache(CacheCommand),
    Test,
}
```

外向きCLIを急に変える必要はないけど、内部構造だけでも分けると読みやすくなると思うよ〜。

## error handling を filesystem より先に固める

これはTODOの方向そのままで良さそう。`host-filesystem.md` では、`std::fs` の `read_text: str -> opt str` や `write_text: (str, str) -> bool` は暫定で、error handling を先に固める、と書かれているねぇ。
`language-surface.md` でも `error` sugar、generated `fail`、`from`、`raise`、`result` との関係がまだTODOになっている。

ここは順番が大事そう。

おすすめの順番は：

1. `result` の value-level API を最低限固める
2. `error E:` が何を生成するか固定する
3. `fail err` の解決規則を固定する
4. `E::wrap` で effect を `result` に閉じる形を固定する
5. その後に `std::fs` を `opt` / `bool` から typed error に移す

特に `fail` は、data constructor と effect operation の同名解決が絡むので、ここを曖昧にしたまま filesystem を広げると、後で直す面積が大きくなりそうだねぇ。

## archived native backend は current roadmap から外す

native backend は 2026-05-25 に active workspace から外れたので、このメモ内の
native support 表や CLI 案は historical として扱う。今は VM を user-facing 実行面にし、
control VM / compiled-unit cache / monomorphize strictness を current roadmap に置く方がよい。

将来 execution backend を再開するなら、古い TODO をそのまま戻すのではなく、VM/runtime
semantics と type surface audit が落ち着いた後に新しい track として切り直す。

## playground はかなり良いので、次は「共有」と「縮小再現」

playground は日本語/英語切り替え、examples、型表示、timings、worker retry、std cache warmup まで入っていて、かなり作り込まれているねぇ。
wasm側も run / colorize / warm_std_cache / std artifact status など、デバッグ情報がちゃんと出るようになっている。

ここからの改善なら、UIの派手さよりも：

* URLに source を埋め込んで共有
* examples を docs とテストから同じデータで生成
* エラー時に「最小再現としてコピー」ボタン
* timings を開発者向け折りたたみ表示
* 「VMで動く」「playgroundではhost未対応」などの status badge

このあたりが良さそう。

特に Yulang は研究的な機能が多いから、playgroundでバグや制限に当たったときに、そのまま issue / test fixture に移せると強いねぇ。今はopen issueがないようだったので、逆に playground から小さい repro を貯める導線があると開発ログにもなりそう。

## parser combinators は急がなくてよさそう

`parser-combinators.md` は面白いし、Yulangらしい方向だと思う。parser value、structured parse error、cut/commit、error merging などがTODOにあるねぇ。

ただ、これは `result` / `error` / string slicing / byte-text の方針が固まる前に広げると、あとでAPIが揺れそう。TODOにも「error handling の方向が安定する前に広い parser API を固定しない」とあるので、これはその通りだと思う。

先にやるなら、公開APIではなく `std::parser::experimental` くらいで、

```yulang
parse_int "123abc"
-- ok (123, "abc")
```

くらいの小さい例に閉じるのが安全かなぁ。

## 言語表面で少し気になるところ

ここは好みもあるけど、初見の混乱を減らせそうなところ。

### `my` / `our` / `pub` の差

language report でも、`our` と `pub` の差は現状かなり近く、公開仕様にするなら意図を明文化する必要がある、と整理されているねぇ。

これは早めに決めたほうが良さそう。

候補：

```text
my   lexical/private
our  module-visible / infer-visible / extension member
pub  exported API
```

もし `our` が「companion method や impl member を外へ出すが、package publicとは違う」なら、その名前はかなり良いと思う。ただ、READMEだけ読む人には差が分かりにくいかも。

### `$x` / `&x` は魅力的なので、もっと前面に出していい

参照が通常の mutable slot ではなく synthetic effect として実装される、というのはかなりYulangらしい強みだよねぇ。overviewにも説明がある。

これは単なる機能紹介ではなく、

```text
mutable state is local control, not hidden global impurity
```

みたいな見せ方ができると思う。
Yulangの「普通っぽい構文、でも中身は effect system」というテーマにぴったり。

### `effectful condition` は強いデモになる

`if all [1,2,3] < any [2,3,4]` はかなり印象がいい。overviewでも、pure condition なら普通の bool、effectful なら lowerer が `junction::junction` を挿入すると説明されているねぇ。

これはREADMEの代表例を少し短くして、この機能を主役にしてもいいかも。

```yulang
if all [1, 2, 3] < any [2, 3, 4]:
    "yes"
else:
    "no"
```

この短さで「普通の構文に effect が入っている」が伝わるのはかなり良いよ〜。

## 優先順位をつけるなら

今の状態なら、りな的にはこの順がよさそう。

| 優先 | 改善                          | 理由                                               |
| -: | --------------------------- | ------------------------------------------------ |
|  1 | feature/status matrix       | 実験中の広さを、混乱ではなく整理として見せられる                         |
|  2 | diagnostics corpus          | 使う人の体験が一気に良くなる                                   |
|  3 | Yulang-facing test fixtures | 機能追加が安心になる                                       |
|  4 | error / fail / result の契約   | filesystem / parser combinator / host API の土台になる |
|  5 | README短縮 + docs分離           | 初見の印象が締まる                                        |
|  6 | CLI command整理               | debug/test/cache が増えても壊れにくい                       |
|  7 | playground共有URL + repro導線   | 遊びやすさと開発効率が両方上がる                                 |
|  8 | archived native summary     | 研究の蓄積を current user path と混ぜずに残せる                |

## ひとことで言うと

Yulangはもう「変なことをやっている言語」ではなくて、**変な中身を普通の表面に落とし込む言語** になってきていると思うねぇ。
だから次の改善は、機能追加よりも、

> この構文は何を保証するのか
> どの backend で動くのか
> 壊れたらどう説明されるのか
> 小さい例でどう確かめるのか

を整えるのが、いちばん伸びしろ大きそうだよ〜。
