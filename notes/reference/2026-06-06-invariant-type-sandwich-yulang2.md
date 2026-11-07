# 不変型と sandwich（InvariantType = CompactBounds enum 化）

2026-06-06 決定。`crates/yulang-infer` の compact 表現を作り直す方針。

## 問題

simple-sub の不変型変数（invariant type variable）は「共変部分と反変部分の2つ組 `(+,-)`」で、
主型に現れるときは lower/upper に共通する型変数を表示上の中心として `int|α&float` のように見せる
（`spec/2026-06-02-role-system.md#L9-13`）。
中心は保存しない。したがって `int|α&float` は表示上の略記であり、内部表現は lower=`int|α`、
upper=`α&float` の区間である。
区間同士を同じ実引数として併合するときは、両側の lower / upper を単に足す。
必要な変数等式は、併合後の lower/upper の両側に現れる変数から区間由来の等式併合で導く。
この併合では、両区間が同じ実引数を持てるための交差条件として `loA <: upB` と `loB <: upA` も生成する。

当初「表示上の中心は必ず生き残る」と考えていたが **これは誤り**。共通変数は **sandwich** によって消えうる。

- sandwich =「具体コンストラクタまたは型変数」と「区間両側に共通する型変数」の共起分析。**主型全体で**、変数 α の
  全出現が例外なく**同じ単一コンストラクタ K と共起**しているなら、K を型コンストラクタとして
  引き上げ（lift）、α を捨てる。同じ型変数 β と正負両方で共起しているなら、Simple-sub 4.3.1 の
  variable sandwich として α を β へ併合する。1箇所でも α が裸／別コンストラクタで出たら lift しない。

今の `CompactType` では表せない。理由：tuple 成分・fun の arg/ret は `CompactType`（片極性）で
持っており、tuple を lift して各成分を `(+,-)` 区間にする箱が無い（con の args だけ `CompactBounds`）。
→ round-trip 不可。表現自体を作り直すしかない。

## 解（InvariantType ＝ `CompactBounds` を enum 化）

名前は `CompactBounds` のまま enum にする（「具体型を伴った bounds」）。案A：

```rust
enum CompactBounds {
    Interval { lower: CompactType, upper: CompactType }, // 中心を保存しない (+,-) 区間の葉
    Con(Path, Vec<CompactBounds>),   // lift 済みの具体コンストラクタ
    Tuple(Vec<CompactBounds>),
    Fun { arg, arg_eff, ret_eff, ret },  // 反変は変換時に極性反転
    Record(...) | Variant(...) | Row(...),
}
```

- con args は元々 `Vec<CompactBounds>` なので lift 済みの子もそのまま同じ箱に入る → 配管はほぼ無傷。
- `CompactType`（vars + shape の union）は `Interval` の lower/upper の中に残す。sandwich が
  `CompactType.tuples` 等から shape を `CompactBounds::Tuple` 等へ引き上げる。
- 触るのは **sandwich・比較(Eq/型等価)・変換(display / freeze / solver の Pos/Neg 戻し)** だけ。

### CompactType の nominal / row 成分

`CompactType` の concrete nominal 成分は、同じ path の候補を `Vec` に重ねない。
次の正規形で持つ。

```rust
CompactType.cons: FxHashMap<Vec<String>, Vec<CompactBounds>>
```

同じ path が再度入る場合は、新しい entry を追加せず、既存の `args` と新しい `args` を同じ
不変実引数として併合する。併合では lower / upper をそれぞれ足す。あわせて、同じ実引数が両区間を満たすために `loA <: upB` と `loB <: upA`
の交差条件を生成する。

この交差条件は compact 表現の局所 rewrite ではなく、通常の `ConstraintMachine` へ戻す制約である。
compact collect は同じ slot に落ちた `CompactBounds` のペアを記録し、制約が新規に記録された場合だけ
collect をやり直す。毎回固定で不動点を回すのではなく、同一 slot merge から新しい制約候補が出た
ときだけ再 collect する。

同じ制約生成レーンで、区間内の足場変数が実型になれない場合の片方向制約も扱う。
区間の片側で代表変数`α`を除く同側変数が、その区間自身を除いた場所では反対極性に現れないなら、
その足場変数は代入される実型として観測されない。
この場合、反対側境界から足場変数を取り除いた型へ `α <: ...`（反対向きの位置なら `... <: α`）を
`ConstraintMachine` へ戻し、再 collect 後の共起分析へ渡す。
これは sandwich 後の表示整理ではなく、co-occurrence の燃料を増やすための制約生成である。

再 collect の停止判定では、merge 後に合算された lower / upper 全体を key にしない。
`Interval` や constructor path とその子 slot からなる「同じ場所に来た原因」だけを key にする。
合算後の bounds を key にすると、前回 merge で足した制約を再展開した結果同士がまた別 key として
merge され、制約生成が止まらない。

effect row の concrete item も同じ形で持つ。

```rust
CompactRow.items: FxHashMap<Vec<String>, Vec<CompactBounds>>
```

row item は任意の `CompactType` ではなく、effect family `path(args...)` だけを表す。
row の tail や nested row に出る変数は `CompactRow.tail` 側の `CompactType` に残す。
この正規形により、同じ effect path の item が collect 中に複数現れても、共起分析へ渡る前に
args をすり合わせた1 entryへ畳まれる。

stack weight に載る effect family も concrete row item と同じ slot に来ることがある。
たとえば `α@push[K(args)]` と `K(args')` が同じ effect row に同居するなら、`K` の実引数は
`CompactRow.items` 同士の merge と同じ規則で交差条件を生成する。

`pop` によって `push[K(args)]` が surface weight から消える場合も、展開時に同じ row slot へ
同居することが確定していれば、`pop` で消す前に `K(args)` と row item 側 `K(args')` を
merge 済みとして扱う。実装では、constraint machine が `Pos::Stack` を weight へ移す時点で
pop 前の effect family を root 変数ごとの side table に残し、compact collect が同じ root の
row item と照合して交差条件へ戻す。この side table は表示・極性消去・共起保護には使わない。

function の effect slot を freeze するときも、bare `Con(K,args)` は通常の nominal type ではなく
effect row item として扱う。したがって effect slot に `K(args)` と `[K(args)]` が同居しても、
最終 `Pos::Row` では同じ item に dedup される。裸の effect 変数だけがある場合は従来どおり
裸変数として残し、不要に `Row([α])` へ包まない。

### Role 引数

compact 後の role 引数は専用の lower/upper ペアではなく、`CompactBounds` そのもので持つ。
生の `RoleConstraintArg { lower, upper }` は lowering / annotation から来る制約入力の形であり、
compact collect の入口で、同一具体構造なら lift 済み bounds、それ以外は中心なし interval へ変換する。

role coalesce で同じ通常引数位置、または同じ関連型名の値が合流した場合は、constructor 引数や
effect family 引数と同じ `CompactBounds` merge を使う。merge は見た目の正規化ではなく、
同じ実引数が両方の demand を満たすための交差条件 `loA <: upB` / `loB <: upA` を生成する。
この制約候補も merge constraint key に入れ、未適用の制約が出たときだけ再 collect する。

### 二次変数

compact collect で型変数の bounds を展開したとき、その bound 自体が裸の別型変数だった場合、
その変数を二次変数（secondary variable）として記録する。`α` の bound が `β` なら `β` は
二次変数である。一方、`α` の bound が `list β` や `β -> γ` のような構造を持つ場合、その中の
`β` / `γ` は構造の payload / field / slot であり、二次変数ではない。

二次変数は compact 表現には残すが、再 collect でそれ自身の bounds を展開しない。

これは「展開された変数を再 collect で再展開する」循環を避けるための表現上の規則であり、
極性消去を止める保護集合ではない。主型から直接見えている変数は従来通り primary variable
として collect される。

### sandwich の1ステップ（例）

```
Leaf( α|(β,γ) , α&(δ,ε) )            -- 両側に tuple/2 が共起、α を捨てる
  → Tuple( Leaf(β,δ) , Leaf(γ,ε) )  -- 子をさらに sandwich（さらに潰れうる）
```
共変位置は lower成分↔lower成分。反変位置（fun arg, effect の一部）は極性反転して組む。

## opt の手計算（合わせ込み対象テスト）

ソース共通：`x = if true { nil_pair } else { opt::just (1, 2) }`

- **注釈アリ** `nil_pair: opt (int,int)` → x payload = `Leaf( α|(int,int) , α&(int,int) )`
  両側に tuple → lift、α 捨て → `Tuple(Leaf(int,int),Leaf(int,int))` → 各 `int` con も lift
  → `(int,int)` → **`opt<(int,int)>`**
- **注釈ナシ** `nil_pair = opt::nil` → x payload = `Leaf( α|(int,int) , α )`
  upper が裸 α でコンストラクタ無し → lift 不可 → **`opt<(int,int) | α>`**（表示上の共通変数 α が残る）
- 全体観の注意例：`(int,int)|α&(int,int) -> α` は arg だけ見れば lift できそうだが、ret に
  裸 α がいる → α は全出現で K と共起しないので lift 不可。arg も ret もそのまま残る。

対象テスト：`source::tests::{lowers_opt_if_join_keeps_invariant_payload_interval,
lowers_opt_if_join_without_annotation_keeps_open_payload_interval,
compact_scheme_keeps_invariant_payload_interval}`、`display::dump::render_compact_results_handles_ref_update_effect`。
期待値は旧・分配形 `opt<(α|int,β|int)>` で **stale**。注釈アリ→`opt<(int,int)>`、
注釈ナシ→`opt<(int,int) | α>` に直す（Codex のテスト改竄癖に注意、手計算で裏取り済み）。

## 実装段取り

1. struct のまま `lower()`/`upper()`/`lower_mut()`/`upper_mut()` メソッド追加。読みアクセス
   `.lower`/`.upper`（~631箇所）をメソッドへ寄せる。フィールドとメソッドは別名前空間なので両立、緑のまま。
2. `CompactBounds` を enum 化。`lower()`/`upper()` は `Interval` はフィールド返し、lift 変種は
   等価な `CompactType` を合成して返す（既存読みコードは変種を意識しなくて済む）。書き込み(47)・
   構築(126)を `match`/コンストラクタへ。compiler 主導で潰す。
3. グローバル sandwich を enum 上に実装。`apply_sandwich_flattening`（今はトップ変数だけ）をこちらへ寄せる。
4. finalize の暫定 crutch（`finalize_expansive_compact_scheme` の var-clear / polarity-aware keep）を
   sandwich へ置換。cooccur → sandwich → freeze/display のパイプラインに乗せる。
5. 失敗テストで合わせ込み・期待値修正。

## 既に入れた暫定変更（この改修で整理）

- 残す：packing 無効化（`scc/close.rs`、値制限の context packing を切って level0 解析へ）、
  display は lower/upper から共通変数を導いて中心表示する。中心そのものは freeze しない。
- 捨てる：polarity-aware crutch（`compact.rs` finalize の keep 引数）は sandwich が本実装。
