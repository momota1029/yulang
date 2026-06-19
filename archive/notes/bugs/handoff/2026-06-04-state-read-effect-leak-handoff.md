# 引き継ぎ: state read (`$a`) で effect 変数が値型に漏れるバグ（2026-06-04）

## TL;DR
`my $a = 0; $a` のような **state read** が `α | β | … | ω | t24 … | int`（37個の型変数 + int）という型になる。期待は `int`。
**effect 由来の変数が値型の位置に union されている**＝設計上ありえない＝純粋なバグ。
これが `render_compact_results_lowers_for_in_ref_push_body`（`for x in [1,2,3]: &xs.push(x)` が `std::list::list<…200変数…>` に膨れる）の根本原因。

設計者の見立て:「effect を値側に混ぜる経路は（バグを除いて）存在しない。一番怪しいのは関数型の比較だが、そこにあるとは思えない」→ 関数型の比較（make_app/neg_fun）は実際に**無罪と確認済み**。これは想定外の場所のバグ。

## 最小再現
`crates/yulang-infer/src/display/dump.rs` に一時テスト `dbg_once_type` を追加済み（**要・最終削除**）。現在のソース:
```rust
"my read_only =\n  my $a = 0\n  $a\n"
```
→ `read_only: α | β | … | ω | t24 … t36 | int`（37変数 + int、期待は `int`）

実行:
```
env RUSTC_WRAPPER= cargo test -p yulang-infer dbg_once_type -- --nocapture 2>&1 | grep once-dbg
```
（`env RUSTC_WRAPPER=` を付けないと sccache がタイムアウトする。**全 cargo test はハングするので必ず名指し**）

## 物差し（本来直したいテスト）
- `render_compact_results_lowers_for_in_ref_push_body`（期待 `std::list::list<int | α>`）。state read leak が直ればこれも直るはず。
- 全体物差し: `env RUSTC_WRAPPER= cargo test -p yulang-infer display::dump::tests::render`（44 passed / 9 failed が現状ベースライン）。

## state の仕組み（背景）
- `my $a = v` は `var` synthetic act を `lib/std/var.yu` から materialize し、`act::run v body` に desugar（`lower/stmt/var/binding.rs`）。
- `$a`（read）= `act::get ()`（var act の get effect op を適用）。`lower/expr/var.rs:30-34`。
- `&a = w`（write）= `act::set w`。
- `var.yu` の run は**再帰ハンドラ**:
  ```
  my run(v: 't, x: [_] 'r): 'r = catch x:
      get(), k -> run v: k v
      set v, k -> run v: k()
  ```

## 確定した事実（究明済み・再調査するな）
切り分けで以下は**全部無罪**と確認した。同じ場所を再び疑って時間を溶かさないこと。

1. **read が源、write は正常**: `my $a=0; $a`（read）= 37変数 / `my $a=0; &a=1; ()`（write）= `unit`。get が膨張、set は正常。
2. **ref struct 作成は正常**: `my $a=0; &a`（ref を返す）= `std::var::ref<&a#…<int|β>|α, int|β>`（47 chars、膨張なし）。effect 部と値部は分離できている。
3. **膨張は「適用後」**: var act の get/set/run/var_ref を materialize した直後の生制約は少数（`[tmpl-scheme]` ログで run: raw_lowers=4/uppers=6、get/set: 1/1、var_ref: 4/2）。`var::run 0 (act::get())` の**適用後**に37変数になる。
4. **compact 展開は無罪**: `compact_var_bounds`（`simplify/compact.rs`）は `raw_lowers ≈ expanded_vars`（`[var_bounds]` ログで 210→202 等）。推移展開していない＝設計「展開して出てきた変数の上界は展開しない」は守られている。膨張は生の下界が最初から多いだけ。
5. **value copy（get/set の materialize）は衛生的**: `try_copy_lowered_act_body`（`lower/stmt/act/copy_lower.rs`）の non_generic は空（`[copy-ng] non_generic(n=0)`）。全 fresh コピー。`copy_tv`（copy_transform.rs:740）の `fixed` にも prelude は入っていない。
6. **make_app / neg_fun / pos_fun は正常**: 引数順 `(arg, arg_eff, ret_eff, ret)` は `Neg::Fun`/`Pos::Fun` の field と一致（state.rs:1110-1126）。apply.rs:165-219 で effect は `result_ty.effect`、値は `result_ty.value` に正しく分離。
7. **catch の継続 k 型付けは正常**: `k: resume -> [scrutinee.eff] scrutinee.value`（catch.rs:212-226）。effect（`k_ret_eff = scrutinee.eff_tv`、これは設計者が「変えるな」と明記）と値（`scrutinee.value_tv`）は別 tv に分離。
8. **`can_coalesce_role_constraints` の AND 化は設計 §簡約2 の正しい修正**（`simplify/role_constraints.rs`）だが、このバグとは無関係。Fold が複数くっつく緩い融合判定の修正で、それ自体は正しいので**残すこと**。

## 残った容疑
`var::run 0 (act::get())` の biunify のどこかで、All-subtractable な effect 変数（scrutinee effect / prelude 由来の効果変数）が**値型 tv** に流れている。静的読解では全箇所正常に見えるのに、結果に37変数が乗る。候補:

- **(A)** `run` の引数注釈 `x: [_] 'r` の lower（`lower/ann.rs`）。`[_]` = Opaque → All-subtractable（`record_effect_annotation_subtractability`、ann.rs:100-108）。設計（subtractable §新規導入変数 項2）では `x: [β] 'r`（β に All-subtractable、**値 'r には情報を付けない**）。effect β と値 'r の取り違え／同一視が起きていないか。
- **(B)** All-subtractable な effect 変数が、catch の handled discharge や `run v: k v` の再帰適用の過程で、値 tv に biunify される経路。
- **(C)** `run(…): 'r` の戻り型 `'r` と scrutinee の value の同一視が、effect を巻き込んでいないか。

## 次の一手（推奨・静的読解は尽きた）
**動的 instrumentation で「`read_only` の最終 value tv に effect 変数が lower として入る最初の `constrain`」を捕まえる**のが決定的。

1. `dbg_once_type` で `read_only` の def の最終 value tv を特定（`lowered.state` から引ける）。
2. `Infer::constrain`（`solve/` 配下）に instrumentation を入れ、`constrain(pos, neg)` で **pos が effect atom/row を含む（または `effect_subtractability` を持つ変数）かつ neg がその value tv（に縮約される変数）** という組み合わせをログ＋発生箇所を出す。
3. その constrain の呼び出し元が漏れ口。そこが (A)(B)(C) のどれかを確定し、effect と値を分離するよう直す。

補助: `record_effect_subtractability` が**値 tv に対して**呼ばれていないか（effect 変数と値変数の取り違え）も確認すると早い。

## 絶対にやってはいけないこと
- **テスト期待値を改竄して通すな。** `render_compact_results_*` の期待値（`std::list::list<int | α>` 等）は設計者が確認した正しい値。型が変わって落ちたら、まず実装を疑う。期待値をいじって誤魔化すのは厳禁（このリポジトリで再発している悪癖）。混在ファイルのテスト部だけ `git checkout` で却下し、実装は温存するのが正しい却下法。
- **cooccur に「守るべき変数集合 / rigid / non_generic 注入」を足すな。** effect が値に混ざるのは cooccur の手前のバグ。cooccur で押さえつけるのは論文外の対症療法で、過去に剥がした罠の再来になる。simplify は論文 §4.3.1（polar removal / indistinguishable unification / sandwich flattening）だけに保つ。
- **「effect が値に混ざるのは仕様」で片付けるな。** 設計上その経路は存在しない（設計者確認済み）。純粋なバグ。

## 現在の working tree の状態（git diff の読み方）
このバグ調査より前から入っている正しい変更（残す）:
- `lower/role_finalize/finalize.rs`: role システム実装の (a) boundary 0 グローバル simplify ＋ (b1) §決定1 具体型確定。
- `scc/close.rs`: invalidate 機構の撤去（through_helper 修正、別件の正しい修正）。
- `display/dump.rs`: pl2/pl3 期待値を `int` に更新（承認済み）。

このバグ調査で入れた変更:
- `simplify/role_constraints.rs`: `can_coalesce_role_constraints` を §簡約2（全引数 AND）に修正＋`bounds_vars` 追加＋`role_constraint_vars` を `#[cfg(test)]` 化（**設計修正、残す**）。`merge_role_constraint_component` の `[merge]` ログ（調査用、削除）。
- 調査用デバッグ eprintln（`YL_DBG_FOLD` ガード、**全部削除**）: `scc/close.rs` `[raw role]` / `simplify/compact.rs` `[var_bounds]` / `lower/stmt/act/copy_lower.rs` `[copy-ng]` / `lower/stmt/synthetic_act.rs` `[tmpl-scheme]`。
- `display/dump.rs`: `dbg_once_type` 一時テスト（**丸ごと削除**）。

デバッグ出力の全リストは `grep -rn YL_DBG_FOLD crates/yulang-infer/src` で出る。

## 参照すべき設計ドキュメント
- `archive/notes/design/2026-05-31-effect-variable-subtractable.md` — subtractable effect 変数。特に「# 新規導入変数について」項2（注釈 `[handled] α` は `x: [β] α`、β に handled を subtractable 登録、**出力型には情報を付けない**）。`[_]` は All-subtractable。
- `lib/std/var.yu` — state の実装（run 再帰ハンドラ / ref struct / ref_update）。
- `lib/std/flow.yu` — for の実装（同型の再帰ハンドラ + Fold role）。
- メモ（`~/.claude/projects/-home-momota1029-rust-yulang/memory/`）: `struct-method-pure-effect-leak`（pure selection に effect 変数を生やす類似病）、`level-polarity-protection`（再帰ハンドラの極性消去）、`project-infer-residual-regression`（cooccur を論文準拠に保つ方針・Codex の悪癖）。
