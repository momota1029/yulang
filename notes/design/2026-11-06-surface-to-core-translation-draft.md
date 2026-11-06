# 表の構文から核への翻訳表 (下書き, 2026-11-06)

Rust 実装の中心になる desugar / elaboration の一覧。**下書き**で、ユーザーが 1 つずつ確かめる。
署名: Claude (Sonnet 5.5), 2026-11-06。仕様の正本は `spec/`。この表は仕様を置き換えない。

## 核の式(ターゲット)

Lean の `Inference.Expr` と `RecursiveEffects.Expr` が持つ形だけを使う。

```text
var i        lit b        lam e        app f a       let v b
branch c t e              pair a b     fst e         snd e
{}  (emptyRecord)         record l h t               field l e
variant l e               request op e               boundary(protect|release, mask) e
handler op action ret arm
```

`lit` の `b` は base 型の印だけで、整数や文字列の中身を持たない。再帰束縛は核の式の外側(`RecursiveInference` の SCC ブロック)にある。

## 状態の印

- **確定**: 仕様で翻訳まで決まっている
- **下書き**: 仕様の方針から私が組んだ。ユーザーの確認待ち
- **欠**: 核に対応する形が無い。核を拡張する必要がある(ChatGPT への依頼になる)

## A. 式の骨格

| 表の構文 | 核 | 状態 | 出典・備考 |
| --- | --- | --- | --- |
| 名前 `x`、path `a::b` | `var i`(束縛済み)、またはモジュールの宣言への参照 | 確定 | 名前解決は核の前。章3.2 |
| `f x y` / `f(x, y)` / `x.m y` / `f: body` | `app (app f x) y` | 確定 | 章3.3。どれも同じカリー化 |
| `f()` | `app f unit` | 確定 | `unit` は `lit unit` |
| `\x y -> e` | `lam (lam e)` | 確定 | 章3.4 |
| `\(a, b) -> e` | `lam (let a = fst #0 in let b = snd #0 in e)` | 下書き | irrefutable な pattern だけ。pattern の分解は E |
| `a; b`(block の文の列) | `let _ = a in b` | 下書き | 値を使わない式も評価される(決定 43) |
| `my x = e; rest` | `let e rest`(`x` を束縛) | 確定 | 値制限の規則は章4.7 |
| `my f x = e`(再帰しうる) | SCC ブロックの member | 確定 | 核の外。`RecursiveInference` |
| `x with: our h = ...` | `let h ... x` | 下書き | `our` 同士の順不同・値制限の順序は章3.5・2.1 |
| `(a, b)` | `pair a b` | 確定 | |
| `(a, b, c)` | `pair a (pair b c)` | 下書き | 右ネストの pair。`.0` `.1` `.2` は `fst` と `snd` の連鎖 |
| `{x: 1, y: 2}` | `record x 1 (record y 2 {})` | 確定 | 先頭が勝つ(決定 40) |
| `{x: 1, ..rest}` | `record x 1 rest` | 確定 | |
| `{..base, x: 3}` | (新しい形が要る) | **欠** | 決定 44。`x?` と union で型付け |
| `{x, y}` | `{x: x, y: y}` と同じ | 確定 | 章3.1 |
| `p.x`(field) | `field x p` | 確定 | field か method かは 6.4 の解決で決まる |
| `:tag e` / `enum::v e` | `variant l e` | 確定 | |
| `if c: a else: b` | `branch c a b` | 確定 | |
| `if c: a`(else なし) | `branch c (variant just a) (variant nil ())` | 確定 | 章3.6。`opt` |
| `elsif` | 入れ子の `branch` | 確定 | |
| `x | f` | `app f x` | 確定 | 章3.9 |
| `a + b` | 宣言された本体の展開: `app (app (lam (lam x.add y)) a) b` | 確定 | 章1.5。演算子は `infix` 宣言で決まる |
| `a and b` / `a or b` | `lazy infix` の本体に両辺を thunk として渡す | 確定 | 章1.5。短絡評価 |
| `-x`、`not x` | prefix 宣言の本体の展開 | 確定 | |
| `0..10` / `0..` | suffix/infix 宣言の本体(`std::data::range::...`) | 確定 | 閉区間 |
| `xs[i]` | `app (app (method index) xs) i` | 確定 | 章3.2。`Index` role |
| `"a %{x} b"` | `Display` で `x` を文字列にして連結 | 下書き | 書式指定付きは `fmt` 相当の呼び出し。std 側 |
| `do` | 後続の文を継続 lambda にして、最も内側の呼び出しの引数にする | 確定 | 章3c.7。純粋に構文 |

## B. pattern と case

| 表の構文 | 核 | 状態 | 備考 |
| --- | --- | --- | --- |
| `case e: p1 -> a; p2 -> b` | 決定木(`branch` と分解の連鎖) | **欠** | variant を分解する式が核に無い。`case` に対応する核の形が要る |
| guard `p if g -> a` | guard が偽なら次の arm に進む | 下書き | 網羅性の検査では guard 付き arm を数えない(章3b.4) |
| or pattern、`as` | 分岐の複製、束縛の追加 | 下書き | |
| record pattern の既定値 `{x = 1}` | `x?` と union(決定 44 と同じ道具) | 下書き | 章3b.3 |
| 範囲 pattern `0..10` | 比較の連鎖 | 下書き | |
| list pattern `[x, ..rest]` | `Fold`/list の分解 | **欠** | list が核に無い |
| `~"GET :resource"` | parser 値を入力文字列に適用し、capture を束縛 | 下書き | 章9。後で詳しく |

## C. effect と制御

| 表の構文 | 核 | 状態 | 備考 |
| --- | --- | --- | --- |
| `op args`(operation の呼び出し) | `request op args` | 確定 | 普通の関数呼び出しに見える(章5.1) |
| `catch e: op p, k -> body; v -> ret` | `handler op e (lam ret) (lam (lam body))` | **欠** | 核の `handler` は operation を 1 つしか取れない。複数 arm の handler が要る |
| `catch` の value arm 省略 | `v -> v` と同じ | 確定 | 章5.2 |
| 高階の境界の保護・解除 | `boundary(protect/release, mask) e` | 下書き | 型から elaboration が挿入する。利用者は書かない |
| `for x in xs: body` | `loop::for_in xs (\x -> body)` | 確定 | std の `for_in`(`main:lib/std/control/flow.yu`)。`last`/`next`/`redo` は `loop` の operation。値は常に `()` |
| `last` / `next` / `redo` | `request loop::last ()` など | 確定 | 章3c.2 |
| `for 'outer x in xs: body` | `label_loop::for_in xs (\'outer x -> body)`。label は `last`/`next`/`redo` を field に持つ struct の値 | 確定 | std。label は値として本体に渡される |
| `'outer.last` / `last 'outer` | label の値のメソッド `last` / `next` / `redo`(role `LoopLabel`) | 確定 | 衛生性(callback の effect は内側の handler から守られる)で外側へ届く |
| (旧)`'outer.last` の instance | label で指名した `loop` の操作 | 取消 | label は値(handler の instance を指す)。核に instance の同一性が無い |
| `sub: body` | `sub::sub body`(computation 引数) | 下書き | `sub` は std の `act`。`pub sub(x: [_] 'a) = catch x: return a, _ -> a; a -> a` |
| `return v` | `request sub::return v` | 確定 | |
| `'done.return v` / `sub 'done:` | label 付き `sub` | **欠** | label と同じ |
| `case 'count n: ... 'count.again (n - 1)` | arm 集合全体への再帰 | 下書き | `again` は label の操作。arm 集合を再帰関数にする |
| `my $a = e; rest` | `&a::run e (\&a -> rest)` | 確定 | 章3c.6 |
| `$a` | `&a` の読み出し operation | 確定 | `var` effect |
| `&a = v` | `&a` の更新 operation | 確定 | |
| `x.method`(effect 行の method) | effect 行から選ぶ | 確定 | 章5.8 |
| `if c`(c の行に `junction`) | `if junction::junction c: ...` | 確定 | 章5.9。型に依存して挿入(条件が pure なら何もしない) |

## D. 宣言

| 表の構文 | 核 | 状態 | 備考 |
| --- | --- | --- | --- |
| `struct p {x: int, y: int}` | nominal 型と constructor | **欠** | 核に nominal 型が無い(Lean は構造型だけ) |
| `enum e = a | b x` | nominal 型と variant constructor | **欠** | |
| `type t = int`(alias) | 展開 | 確定 | 章4.4 |
| `role R 'a: ...` / `impl R T: ...` | 辞書(dictionary)の型と値 | 確定 | 辞書渡しは `RoleDictionaries` に証明がある |
| `where 'a: R` | 辞書引数 | 確定 | 具体化した場所で解く(決定 30) |
| `act a: our op: P -> Q` | operation の署名 | 確定 | `PolySignature` |
| `error e: v1 p; v2 q` | 下の「`error` 宣言の展開」 | 確定 | 章5.7。`wrap` は error effect → `result`、`up` は error effect → 別の error effect(2026-11-06 ユーザー説明)。型は私の読み |
| `cast(x: A): B = body` | cast 規則の登録 | 確定 | 本体は純粋。境界で挿入 |
| `act copy = source` | 新しい effect family | 確定 | 章5.6 |

## E. 型を見て挿入するもの(elaboration)

| 挿入するもの | 状態 | 備考 |
| --- | --- | --- |
| cast | 確定 | 型が合わないときだけ。関数・tuple・record・payload に通る(決定 16〜25) |
| 辞書引数 | 確定 | `where` の制約ごと |
| 保護・解除の境界 | 下書き | 高階の callback の境界。型から決まる |
| 保留された cast 境界 | 確定 | 不変の型引数を持つ nominal 型の構築(決定 25) |
| `junction::junction` | 確定 | `if` の条件の行に `junction` が出るとき(章5.9) |

## `error` 宣言の展開 (下書き)

```yulang
error path_err:
    not_found path
    denied path
```

作られるもの:

1. `enum path_err = not_found path | denied path` と、同名の operation を持つ `act`(`not_found: path -> never`、`denied: path -> never`)。variant は値の constructor であり operation でもある。期待型が error なら値、effect の位置なら operation
2. `impl Throw path_err`(`e.throw` で、variant に対応する operation を呼ぶ)
3. `impl Display path_err`(variant 名と payload を文字列にする)
4. `path_err::wrap : [path_err] 'a -> result 'a path_err`(確定) — error effect を handle して `result` に戻す。`ok v` か `err e`

`from` 付き(`enum app_err: path from path_err`)では、さらに次が作られる。

5. `app_err::up : [path_err] 'a -> [app_err] 'a`(確定) — `path_err` の operation を handle して、`app_err::path e` として投げ直す(error effect を cast する。継続は再開しない: error の operation は `never` を返す)
6. `app_err::wrap` は、`app_err` と `from` で結んだ `path_err`・`parse_err` の両方を handle する(狭いエラーを同時に捕まえる。章5.7)。狭いエラーは `err (app_err::path e)` のように `app_err` に包まれて `result` に入る(確定, 2026-11-06)

## 核に足りない形(まとめ)

ChatGPT に依頼する核の拡張の候補。

1. variant・literal・list を分解する `case` 相当の形(網羅性と残余の型付けを含む。決定 4)
2. 複数 operation を持つ handler(shallow・value arm は 1 つ)
3. label(handler の instance の同一性)
4. nominal 型の構築子(struct・enum・list)
5. 整数・文字列などの literal の中身(今は base の印だけ)
6. `{..base, x: 3}`(決定 44)

## 確認したいこと(ユーザーへ)

- `for` の `redo` の意味(同じ反復のやり直し)の実装方針
- 書式付き文字列の `fmt` の境界(std 側。`main:web/docs/ja/reference/strings.md` が素材。言語としては `Display` を呼ぶところまで)
