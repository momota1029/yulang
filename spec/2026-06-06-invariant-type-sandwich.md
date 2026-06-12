# 不変型と sandwich（InvariantType = CompactBounds enum 化）

2026-06-06 決定。`crates/yulang-infer` の compact 表現を作り直す方針。

## 問題

simple-sub の不変型変数（invariant type variable）は「共変部分と反変部分の2つ組 `(+,-)`」で、
主型に現れるときは共有された中心変数を1つ選んで `int|α&float` のように中心づけて見せる
（`spec/2026-06-02-role-system.md#L9-13`）。
内部表現では、この中心変数は lower 側と upper 側の両方に現れる。
したがって `int|α&float` は表示上の略記であり、意味は `int|α <: α <: α&float` である。
表示だけが中心変数の重複を隠す。
区間同士を同じ実引数として併合するときは、片方の中心変数を選び、両側の lower / upper を単に足す。
選ばなかった中心変数も両側に残るため、区間由来の等式併合で中心同士を合わせられる。
この併合では、両区間が同じ実引数を持てるための交差条件として `loA <: upB` と `loB <: upA` も生成する。

当初「中心は必ず生き残る」と考えていたが **これは誤り**。中心は **sandwich** によって消えうる。

- sandwich =「具体コンストラクタ」と「中心型変数」の共起分析。**主型全体で**、中心変数 α の
  全出現が例外なく**同じ単一コンストラクタ K と共起**しているなら、K を型コンストラクタとして
  引き上げ（lift）、α を捨てる。1箇所でも α が裸／別コンストラクタで出たら lift しない。

今の `CompactType` では表せない。理由：tuple 成分・fun の arg/ret は `CompactType`（片極性）で
持っており、tuple を lift して各成分を `(+,-)` 区間にする箱が無い（con の args だけ `CompactBounds`）。
→ round-trip 不可。表現自体を作り直すしかない。

## 解（InvariantType ＝ `CompactBounds` を enum 化）

名前は `CompactBounds` のまま enum にする（「具体型を伴った bounds」）。案A：

```rust
enum CompactBounds {
    Interval { self_var, lower: CompactType, upper: CompactType }, // 中心が残った (+,-) 区間の葉
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
  upper が裸 α でコンストラクタ無し → lift 不可 → **`opt<(int,int) | α>`**（中心 α 残る）
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
  display の中心保持 fix（`display/{dump,format}.rs` の `format_compact_bounds_with_center` で
  lower==upper でも中心を落とさない）。
- 捨てる：polarity-aware crutch（`compact.rs` finalize の keep 引数）は sandwich が本実装。
