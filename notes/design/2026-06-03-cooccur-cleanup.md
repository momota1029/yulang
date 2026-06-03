# タスク: cooccur simplification を論文準拠に掃除する

## 目的
`crates/yulang-infer/src/simplify/cooccur.rs` と `cooccur/passes.rs` の
co-occurrence simplification を、**論文 4.3.1 の3つだけ**に絞る。
歴史的に積み上がった「論文外の影武者処理」を全部削除する。

## 根拠（必ず読むこと）
- 論文: `papers/md/[v1.9] simple-essence-algebraic-subtyping_Marker.md` の §4.3.1
  （simplification は本来 3 つ: polar variable removal / indistinguishable
  unification / variable sandwich flattening のみ。polar removal は
  sandwich の τ=⊥/⊤ 特殊形）
- メモ: `~/.claude/projects/-home-momota1029-rust-yulang/memory/` の
  `project_infer_residual_regression.md`
  （病名: Codex が共起分析＋極性消去を理解せず「守るべき変数集合」を後付けした。
  正しい cooccur に戻せば影武者が連鎖除去され、実装はむしろ減る）
- 設計ノート: `notes/design/2026-05-31-effect-variable-subtractable.md`
  （effect 変数の subtractable 登録・変数展開・shallow/deep の極性判定。
  `# 実際の表現について`＝compact の共変/反変表現、`# 変数展開について`＝簡約の正解手順。
  特に「展開して出てきた変数の上界は展開しない」は**推移律の非成立を保つ要点**で、ここを壊すと
  影武者が増える。`# outer/local/repeat の衛生性`は local 漏れの正解推論手順そのもの）
- 設計ノート: `notes/design/2026-06-02-role-system.md`
  （role の引数(不変=共変+反変の2つ組)・level 共有・簡約・決定。`# 簡約について`で role 引数も
  極性消去/共起分析の対象になる（不変なので中心変数は消えない）。`# roleとlevelについて`で level の
  動きが規定。**掃除で role 関連の簡約を巻き込んで消さないこと**）

## 残すもの（論文準拠の本体・絶対に消すな）
- `apply_polar_variable_removal`（極性消去）
- `apply_indistinguishable_unification`（判別不可の統合）
- `apply_sandwich_flattening`（サンドイッチ平坦化）
- `merge_equiv_vars` / `resolve_subst_var`（統合の向き正規化。大きい番号→小さい番号で循環防止）
- level フィルタ `all_vars.retain(|tv| var_levels.get(tv) >= boundary)`
  （量化候補を絞る。極性消去は level と密接なので外すな）
- `rewrite_*`（subst を型に適用する配管）

## 削除するもの（論文外の影武者・全部消す）
- `rigid_vars`（「守るべき変数集合」という発想自体が論文外。全廃。`HashSet::new()` で
  渡してる箇所も含め、引数から消す）
- `apply_row_residual_unifications` + `expose_positive_row_residual_tails`
- `apply_effect_pairwise_co_occurrence_substitutions`
- `apply_group_co_occurrence_substitutions` + `analyze_group_co_occurrences*`
- `apply_exact_row_unifications` / `apply_exact_sandwich_removal`
- `apply_shadow_var_collapse`
- `apply_one_sided_exact_alias_collapse`
- `guarded_row_recursion_representatives` とその補助（`guarded_row_*`）
- `ExactInfo` / `exact_center_var` / `projection_target_var` など exact 系の補助
- これらに引きずられて不要になる import / private fn は連鎖的に削除

メモにある通り「影武者が連鎖除去され実装が減る」のが正しい結果。
**追加するな。減らせ。** 迷ったら「論文 §4.3.1 に書いてあるか」で判断する。

## テストの扱い（ここが肝心）
削除と残すを取り違えないこと。

### 消してよいテスト（昔の不変条件）
論文外処理の「内部挙動」だけを検証してるもの。例:
- `coalesce_by_co_occurrence_removes_exact_row_sandwich`
- `coalesce_by_co_occurrence_removes_record_spread_sandwich`
- `coalesce_by_co_occurrence_removes_function_sandwich` のうち exact/shadow/group 依存のもの
- shadow / group / effect_pairwise / row_residual の挙動を直接 assert してるもの
- `analyze_group_co_occurrences_*` 系
判断基準: 「削除する処理が無いと成立しない期待値」なら、そのテストごと消す。

### 残すテスト（本質）
最終的な型の正しさを見てるもの。例:
- `render_compact_results_*`（型がちゃんとつく）
- 型エラーになるべきものが型エラーになる系
- principal な型（`α & β` のような正しい残差）を確認する系
- polar removal / indistinguishable / sandwich そのものの基本テスト

### 禁止事項（重要・再発防止）
- **本質テストの期待値を改竄して通すのは厳禁。**
  Codex には「残差表記を握り潰してテストを通す」癖がある。
  型が変わって落ちたら、まず実装が正しいか疑う。期待値をいじって誤魔化さない。
- 「型がつくはずが型エラー」「型エラーのはずが型がつく」に変わったら、それは退行。実装を直す。

## 検証
- `env RUSTC_WRAPPER= cargo test -p yulang-infer -- render_compact_results 2>&1 | grep "test result"`
  （ただし全件は重い。落ちたものを名指しで個別確認する）
- **全 cargo test はハングする。** 必ず名指し or クレート単位で。
- `env RUSTC_WRAPPER=` を付けないと sccache がタイムアウトする。

## 補足
現在 cooccur.rs にデバッグ出力（`[prefilter]` `[subst]` `[polar]` `dbg_dump_scheme`）が
残っている。掃除のついでに消してよい。state.rs の `[enter_let]` ログも調査用なので消してよい。
