# spec の例を Lean の具体例にする: 適合例の一覧 (2026-11-08)

目的: 一般論の証明が通っても、ユーザーが書く型の話をしていなければ意味がない
（B4 の点モデルで、数百 M トークンを使って気づいた）。そこで、`spec/` に書かれた Yulang の例を、
**Lean の具体的な定理（その式・その goal・その宣言に対する結果）**として置き、Audit と一緒に必ず通す。
一般論の証明より先に、この例が通ることを確かめる。通らない例が出たら、モデルがずれている合図なので、
一般論の証明を積む前に定義を直す（または `notes/questions/` に 1 問積む）。

規則:
- 各例は、spec の確定した記述から取る。出典の節を書く。判定（通る／拒否／曖昧／単純化）は spec に書かれたもの。
- Lean では、`example` または `theorem` で、元の式（核の項や宣言）に対し、推論・解決の公開入口から結果を導く形にする。
  部品の局所補題の適用だけで済ませない（公開入口が無い間は、最も外側の定義を通す）。
- この一覧は増やしてよい。ユーザーの決定が増えるたびに、例を足す。

## 一覧

| ID | 出典 | 入力 | 期待 | 関係する目標 |
| --- | --- | --- | --- | --- |
| X1 | 6.3 停止 | `impl Display (list 'a)` where `'a: Display` | 受理 | B4 |
| X2 | 6.3 停止 | `impl Foo 'a` where `(list 'a): Foo` | 宣言で拒否（条件が head より大きい） | B4 |
| X3 | 6.3 隠れた同名 field | `impl R {x: int, x: int}` where `{x: int}: R` | 宣言で拒否（2 つ目の `x` は数えない） | B4 |
| X4 | 6.3 tail | goal `R {x: int, ..'a}`（`'a` 未解決） | 解かずに保留。具体的な record が来て先頭の field が引かれたら決める | B4 |
| X5 | 6.3 合流 | `impl R 'a (:{tick (int, 'a), tick ('a, int)})` where `'a: R (:{tick ('a, 'a)})` | 宣言で拒否（`'a := int` で head と where が同じ大きさ） | B4 |
| X6 | 6.3 合流 | `impl R (:{tick 'a, tick 'b})` と goal `R :{tick int}` | 合流後の payload を丸ごと捕捉して候補になる。`impl R (:{tick int})` も候補なら曖昧 | B4 |
| X7 | 6.3 関連型 | `impl R ({x: int, x: 'a}): type value = 'a` | 宣言で拒否（head から関連型が決まらない） | B4 |
| X8 | 6.3 K2 | `impl Len (list 'a)` に `len [loop 1]` | 通る | B4 |
| X9 | 6.3 K2 | `impl Show (list 'a) where Show 'a` に `show [loop 1]` | `Show μ`（μ は再帰型）で拒否 | B4 |
| X10 | 6.3 K2 | `impl Check {box: {tick: 'a}} where Check {box: 'a}` に `Check {box: μ}`（μ = {tick: μ}） | 拒否（再帰型の中身を照合しようとする） | B4 |
| X11 | 6.3 K2 | `impl Check ({box: 'a})` と `impl Check ({box: {next: 'b}})` が見え、`check {box: loop 0}` | 拒否（曖昧より先に拒否） | B4 |
| X12 | 6.3 名前付き再帰型 | `enum tree` に対する `impl Show tree` | 名前で当たり通常どおり解決 | B4 |
| X13 | 6.5 併合 | `'a <: box 'b` と `'a <: box 'c` | `'a <: box ('b \| 'c, 'c & 'b)`。共起分析で通常 `'b = 'c` | B4 |
| X14 | 6.5 入れ子 | 端点が `list (list int)` と `list (list float)` | 外側の交差条件を解く途中で内側の `list` の区間がまた併合される。深さの上限なし | B4 |
| X15 | 6.5 単純化 | `list` の区間が `(box A, box B)` | `list (box (A, B))` に単純化 | B4/B5 |
| X16 | 6.5 単純化 | `list` の区間の下界 `box A`、上界 `list B`（頭が違う） | 区間のまま残る | B4/B5 |
| X17 | 6.5 不変の中の向き | `list (int \| 'a & float -> int)` | 戻り値（共変）も引数（反変）も、`list` の内側では不変な区間 | B5 |
| X18 | 6.5 variance | `box 'a`, `box2 'a`, `reset 'a`（再帰枝が `int`）, `stream 'a` | 共変 | B5 |
| X19 | 6.5 variance | `chain 'a`, `left 'a` / `right 'a` | 不変 | B5 |
| X20 | 6.5 variance | `phantom 'a` | `unused` | B5 |
| X21 | 4.6 rank 2 | `ref 'e 'a` の `run: ('a -> ['f] 'a) -> ['e, 'f] ()` と `sub: r.run \a -> { return a; ... }` | `'f` は run の中で全称。作成時 rigid、使用ごとに具体化 | B3 |
| X22 | 3b.3 | 入力で optional の field に default なしの `{port: p}` | 照合は合法。field が無ければ miss して次の arm へ | B2 |
| X23 | 3.7 | 到達しない arm の effect | case の静的 effect 行は全 arm を合流（到達不能な arm も含める） | B2 |
| X24 | 3.9 | `x \| catch: ...` | 左辺は計算のまま渡り handler に届く。`catch x: ...` と同じ | B2/B3 |

## 運用

- 上の表の各行を、Lean では `lean/SpecExamples.lean`（新規）に、一つの theorem または example として置き、`Audit.lean` に登録する。
- 公開入口（`Core.infer`）が未統合の例（B6 待ち）は、現在最も外側にある定義で通し、「統合後に公開入口へ付け替える」と各例に注記する。
- 通らない例が出たら、その例の ID を挙げて `notes/questions/` に積む（定義のずれか、spec の書き漏れか、どちらかを示す）。
