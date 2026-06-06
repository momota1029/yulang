# Step7 sandwich 実装の現状（2026-06-06、Claude）

設計: `spec/2026-06-06-invariant-type-sandwich.md`。enum 移行（Step6, Codex）は完了済み。

## ★★ 追記（2026-06-06）— collapse 拡張で nested_list `pick` 解決（485/12）

`pick(xs: list (list int))` が `list<list<int>> -> α|int`（戻り α 残り）だったのを **`-> int`** に修正。

**病因**: `int` は `CompactType.prims` ではなく **nullary `Con(int,0)`**（dump で確認：`cons:[CompactCon{path:[int],args:[]}]`,
`prims:{}`）。旧 sandwich は `Single(Con(int,0))` を **lift 経路**に送っていた。lift は不変区間（con-arg）だけを
`Con`/`Tuple` 変種に畳むので、**param の要素区間 `(int|α,int|α)` は int 化される**が、**fun.ret の共変位置 `{α}|int` に
出る同一 α は区間でないため lift が届かず残った**。

**修正**: sandwich に **collapse**（中心 var を主型全体から削除）を追加。`compute_sandwich_verdicts` が
`VerdictAcc{verdicts, centers}` を集め、**atomic（nullary `Con(_,0)` / `Prim`）かつ「不変区間の中心」**
（`lower.vars ∩ upper.vars` or `self_var` に出た var）を `collapse` 集合に。`remove_vars_from_bounds/type` で
cty・rec_vars 全体の `vars`／`self_var` から除去。引数つき Con/Tuple は従来どおり lift。

**区別の核心（ユーザ指摘）**: render は同じ `int|α` 顔でも `(-,+)`（=`(upper,lower)`）組が違う：
- **xs（値束縛）= `(α, α|int)`**：負側(upper) に **裸 α** → NoLift → 残す（`list<int|α>`）。
- **pick 要素 = `(α&int, int|α)`**：両側とも int 共起・裸なし → 中心 collapse → 消える。
- **pl3 等の値束縛残差 `α|int`**：α は **cty.lower の共変位置のみ**（cty.upper 空）に出て**不変区間の中心ではない**
  → `centers` に入らず collapse されない → 残る。これが「関数は消える／値束縛は残る」を**構造で**分ける鍵
  （level 情報なしで display 段に判定できる）。

**検証**: `--skip compiled` で **485 pass / 12 fail**（baseline 484/13 から nested_list を解消、新規回帰ゼロ。
残12は baseline16 の既存失敗）。compiled_typed×7 緑（再帰型 overflow なし＝collapse も rec_vars キーを除外）。
diff は `simplify/sandwich.rs` のみ（+194/-59）。

## ★ 着地（2026-06-06）— sandwich Step7/8 完了・クリーン

**結果**: `cargo test -p yulang-infer --lib --skip compiled` = **484 passed / 13 failed**
（baseline は enum 移行直後で 481/16）。compiled_* も緑（export/import 1件で確認）。
**残る13件は全部 baseline16 の既存失敗**（cooccur/role/cast/effect の継続作業＝Task#2/#3/#4）。
baseline16 リストは `notes/refactors/2026-06-06-compactbounds-enum-migration.md:97-114` にある。
**私が baseline から消したのは opt×3 の3件。新規回帰ゼロ**（sandwich/crutch撤去で
一旦壊した pl3・list-payload×4・panic×2 は全て (b) で回収済み）。

**注意（分類の落とし穴）**: `lowers_nested_list_pattern_wildcards`（`pick`）は **関数**だから一般化されて
戻り値 α は消え `int` になるべき（ユーザ指摘）。`α|int` は honest 残差では**なく cooccur polar-removal の
既存バグ**（正極性のみの戻り var が除去されてない）。pl3（**値束縛**＋計算で量化不可）の `α|int` とは別物。
→ nested_list の期待値は `int` のまま（既存 failing）。pl3 は値束縛なので `α|int` で確定。
**判定基準: 関数 = 一般化されるので残差 α は消えるべき（消えなきゃ cooccur バグ）／値束縛＝量化不可なら残る**。

**(b) 方針採用（ユーザ決定）**: crutch（level-0 変数を全消し）は撤去し**戻さない**。値制限トップレベルの
残差 var は「正直な主型」としてそのまま出し、monomorphize 段の畳み込みに任せる。よって：
- list-payload `list<int|α>` / opt `opt<(int,int)|α>`（不変 con 内の中心が両極性で残る）→ そのまま表示。
- 裸 union `α|int`（pl3=`Add::add 1: ...`, nested_list `pick` 戻り）→ トップレベルで計算が挟まると
  量化できず残る、避けられない形（ユーザ「気にしなくていい」）。期待値を `α|int` に更新済み。
- 注釈アリ opt（両側 pin）は sandwich が lift して `opt<(int,int)>`（α 消える）。

**残13件（既存・本作業の管轄外）**: nested_list_pattern_wildcards(`pick`戻り α 未除去),
ref_update_effect, record_pattern_spread, std_list_helpers(take_map),
std_var_ref×2, string_role_impls, branch_join(cast), choice_effect_residual,
function/row_effect subtractability, non_through_lower, handler_continuation。
→ solve段/cooccurドライバの別件。手は付けない（cooccur §4.3.1 polar removal = Task#2 で直る筋）。

---
（以下、実装途中メモの記録。最終形は上記＋下の「実装サマリ」を参照）

## 完了済み

1. `CompactBounds` enum に lift 変種 **`Con { path, args: Vec<CompactBounds> }`** と
   **`Tuple { items: Vec<CompactBounds> }`** を追加（compact.rs:22 付近）。
2. アクセサ（compact.rs:40 付近）：`lower()/upper()/lower_mut()/upper_mut()/self_var_mut()` は
   lift 変種で `unreachable!()`（**lift 変種は display の read パスしか触らない不変条件**）。
   `self_var()` は lift で `None`。`is_lifted()` 追加。
3. refutable 3箇所を let-else 化（compact.rs:227 merge_compact_bounds、compact.rs:1385
   expand_instantiated_compact_bounds_vars、effect_row.rs:76 は `else { return }`）。
4. **sandwich アルゴリズム本体** = `crates/yulang-infer/src/simplify/sandwich.rs`（新規、`pub mod sandwich;`）。
   - `compute_lift_verdicts(scheme)`: 主型全体で各変数を走査。全出現で同じ単一 liftable kind
     （`Con(path,arity)`/`Tuple(arity)`）と共起し、**一度も裸（コンストラクタ無し CompactType）で
     出ない**変数のみ lift 可。NonLiftable(prim/fun/record/variant/row) と共起 or 複数 kind or
     裸 → NoLift。
   - `sandwich_scheme(&mut scheme)`: verdict→`sandwich_bounds` を cty と rec_vars に適用、fixpoint。
   - `try_lift_interval`: 中心 = lower.vars∩upper.vars or self_var で verdict 持ち。lower/upper
     双方に同種 con がちょうど1つ → lift し中心を捨てる。Tuple は lower/upper のタプル成分を区間に、
     Con は `merge_arg_bounds`（lower 側 con arg と upper 側 con arg を区間マージ）。
5. **display 結線**：`format.rs:compact_scheme_to_type_with_observed_vars_and_hidden_effects` の
   `normalize_compact_scheme_rows` 直後に `sandwich::sandwich_scheme(&mut scheme)` を1行挿入
   （display 直前・破壊的正規化パスは Interval 前提なので、それらの後で lift する方針）。
6. **format_compact_bounds**（dump.rs:807 と format.rs:2722）の先頭に Con/Tuple アームを追加
   （`path<args>` / `(items)` を再帰描画）。coalesce_type_body は `Type::Con(path, con.args)` で
   args を CompactBounds のまま Type に載せ、後段の format_compact_bounds が描画 → ここは対応済み。
7. **commit 段の crutch を撤去**（close.rs:328 付近、`finalize_expansive_compact_scheme` 呼び出し削除）。
   理由: commit 段で lower/upper を潰すと注釈有無の区別が消え sandwich が誤判定するため。
   `finalize_expansive_compact_scheme` 関数自体と import は**未使用警告が出てるはず**（後で削除可）。

## 更新（2026-06-06 続き）— opt 緑・無限再帰修正・perf 確認済み

**display パス lift 対応 完了**（panic-driven option1 を実施）。format.rs に lift アームを足した関数:
- `collect_bounds_lower_witnesses`（先頭で Con/Tuple は子へ再帰し return）
- `compact_bounds_key`（Con→`Bcon[..]` / Tuple→`Btup[..]` キー）
- `collect_compact_bounds_generated_local_effect_tail_vars`・`collect_compact_bounds_vars`
  （match で Con/Tuple は子再帰、Interval は従来）

**opt テスト×3 緑**（実出力＝手計算目標）。期待値も手計算値へ修正済み（tests.rs）:
- 注釈アリ `lowers_opt_if_join_keeps` / `compact_scheme_keeps` → `opt<(int, int)>`
- 注釈ナシ `lowers_opt_if_join_without_annotation` → `opt<(int, int) | α>`（`nil_pair` は `opt<α>` 据置）

**無限再帰バグ修正（重要）**: compiled_* 系（full std を読む）が **再帰型の μ束縛変数を lift して
無限展開**しスタックオーバーフロー。`compute_lift_verdicts` で **`scheme.rec_vars` のキー（μ束縛変数）を
lift 対象から除外**して解決（sandwich.rs）。再帰型は Interval のまま残す。

**perf 切り分け済み**: compiled_* テストは **sandwich off で 174.95s / on で 192.89s**＝元から重い
（debug + full std compile + large stack）。sandwich の上乗せは ~18s(10%)のみで主犯ではない。
fixpoint の `scheme.clone()`＋等価比較を **`changed: &mut bool` フラグ化**して clone/compare を撤去
（その 18s も縮む）。反復上限 `MAX_SANDWICH_PASSES=64` も防御で追加。

**今ここ**: full suite 実行中（`/tmp/sw_full.txt`、~15-20min 見込み）。結果待ち→残失敗を個別対応。

### 次にやること（full suite 結果後）
- pl2（`render_compact_results_resolves_role_methods`, top-level role-orphan `α|int`→int）回帰の有無確認。
  回帰なら sandwich 管轄外＝別対応（top-level クリア再導入 or role 解決改善）。
- その他 stale 型テストを手計算で個別判定（Codex 改竄注意＝自分で手計算して直す）。
- 未使用関数掃除: compact.rs の `finalize_expansive_compact_bounds`/`finalized_expansive_bounds_type`/
  `finalize_expansive_compact_type`/`finalize_expansive_compact_scheme`、close.rs:19 の import。

## 検証

```fish
cd /home/momota1029/rust/yulang/crates/yulang-infer
env RUSTC_WRAPPER= cargo build -p yulang-infer
env RUSTC_WRAPPER= cargo test -p yulang-infer --lib compact_scheme_keeps_invariant_payload_interval lowers_opt_if_join -- --nocapture
```

**手計算の目標値**（既存期待値 `opt<(α|int, β|int)>` は stale、Step8 で直す）:
- 注釈アリ（compact_scheme_keeps / lowers_opt_if_join_keeps）→ `opt<(int, int)>`
- 注釈ナシ（lowers_opt_if_join_without_annotation）→ `opt<(int, int) | α>`

ベースライン全体は **481 passed / 16 failed**。sandwich が効くと opt×3＋ref が動くはず。
**注意: crutch 撤去で pl2（role orphan, `render_compact_results_resolves_role_methods`）が
`α|int`→int に戻らず回帰する可能性**。opt が緑になったら full suite で増減を確認し、pl2 等の
回帰は別途（top-level role-orphan は sandwich の管轄外。最小の top-level クリア再導入 or
role 解決の改善で対応）。

## 重要な不変条件（壊さない）

- sandwich は **ネスト不変位置だけ lift**。root（cty）は Interval のまま（top-level value の cty は
  `opt<...>` の con で var 無し→中心無し→lift されない）。なので `scheme.cty.lower()` は安全。
- sandwich は **display 段でのみ実行**（compact_scheme_to_type 内）。stored compact scheme は
  Interval のまま → instantiate/freeze/role_finalize は lift 変種を見ない。
- `lower()/upper()` が lift で `unreachable!()` なのは「pre-sandwich/非 display のコードは Interval
  だけを見る」契約の番人。display の read パスは変種を直接 match して回避する。

## 触ったファイル（uncommitted）

compact.rs（enum 変種＋アクセサ）, simplify/mod.rs（mod sandwich）, simplify/sandwich.rs（新規）,
display/dump.rs・display/format.rs（format_compact_bounds lift アーム＋ sandwich 結線）,
scc/close.rs（crutch 撤去）, solve/effect_row.rs（let-else）。
あと Codex の enum 移行差分（31ファイル、検証済み）。
