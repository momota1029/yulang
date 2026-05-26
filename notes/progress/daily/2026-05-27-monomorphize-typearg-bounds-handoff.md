2026-05-27 monomorphize TypeArg Bounds subtyping handoff

# 引き継ぎ概要

[2026-05-26 の handoff メモ](2026-05-26-vm-ref-update-handoff.md) の続き。
そちらでは canary `vm_host_flushes_file_handle_string_edits` 1 本だけが落ちている
前提で書かれていたが、実際には clean な再現で `vm_runs_source_ref_*` のほぼ全部が
落ちる状態だった（`IncompleteGraph { binding: ... &x#1296::var_ref }` 系）。
今回は VM ハンドラ層ではなく monomorphize の subtyping を直してその系統を
解消した。残る課題を整理して次に渡す。

## 今回の修正

### 1. `constrain_type_arg` に Type vs Bounds / Bounds vs Type を入れた

ファイル: `crates/yulang-monomorphize/src/graph.rs`

これまで `constrain_type_arg` は `Type vs Type` と `Bounds vs Bounds` だけ
処理し、片方が Type で片方が Bounds の組は `_ => Ok(false)` で素通りしていた。
`var_ref` のような open-effect な return 型では：

- principal が `ref<Bounds(lower=Union([t17753#0, ...]), upper=Inter([t17753#0, ...])), Var(t17766#1)>` を返し、
- call-site の evidence は `ref<Bounds(lower=Row[&x, var], upper=Inter([&x; ⊤], [var; ⊤])), Bounds(lower=int, upper=_)>` を渡してくる。

正常に動いた `var_ref` の trace では `apply#2.lower` が principal 由来の
`ref<Type(Union([t17753#0, ...])), Type(Var(t17766#1))>` （`record` 内の
`normalize_bound_form` で Bounds → Type に縮退済）、`apply#2.upper` が
call-site 由来の `ref<Bounds(...), Bounds(...)>` のまま、というミックスに
なるので、`apply#2.lower <: apply#2.upper` の推移律で `(Type vs Bounds)` /
`(Bounds vs Type)` のペアが必ず立つ。これを Ok(false) で潰すと中の
`t17753#0` が永遠に unsolved で `IncompleteGraph` になっていた。

現状の実装は保守的に片方向のみ：

- `Type(t) <: Bounds(L, U)`: `t <: U` のみ（`L <: t` は将来の課題）
- `Bounds(L, U) <: Type(t)`: `L <: t` のみ（`t <: U` は将来の課題）

両方向にすると `vm_runs_source_ref_string_lines_edit_example` の
`ConflictingBounds` が早期に発火する（後述）。片方向だけでもその conflict は
別経路から立つので解決はしていないが、少なくとも `var_ref` 系には十分。

### 2. `constrain_observed_type_bounds` で upper bound の protected を空にした

ファイル: `crates/yulang-monomorphize/src/solver/apply_spine.rs`

`step.constrain_result_bounds(...)` の呼び出し時、`protected_result_vars`
には既に lower bound のついた var（例: `apply#2`）が含まれる。これが原因で
`constrain_observed_bound` の最初の if が `type_contains_any_var(template, protected_vars)`
で true を取ってしまい、`(Var, _) if protected_vars.contains(var) => Ok(false)`
で upper bound 側まで黙って捨てられていた。lower は principal の return 型から
既に来ているので protect する意味があるが、upper は call-site の evidence が
新しく持ち込む情報なので protect は不要。`constrain_observed_upper_bound` に
渡す `protected_vars` を空にした。

### 3. 実験 handler は復元できなかった（事故）

handoff メモ時点で入っていた `crates/yulang-infer/src/export/expr.rs` の
recursive ref-update handler 実験は、状況把握中に `git checkout` で
誤って消してしまった（reflog 復元不可、stash も残らず）。メモの疑似コードから
再構築できるが、今回は monomorphize 側で `IncompleteGraph` が解消されれば
canary 含めて再評価が必要と判断してそのまま進めた。canary はまだ落ちている
ので、復元するか、別アプローチ（`ref::update` 呼び出し化）に切り替えるかは
次の判断。

## 現在のテスト状況

`vm_runs_source_ref_*` の 7 ケース：

- ✅ `vm_runs_source_ref_scalar_assignment_example`
- ✅ `vm_runs_source_ref_field_assignment_example`
- ✅ `vm_runs_source_ref_list_index_assignment_example`
- ✅ `vm_runs_source_ref_string_range_assignment_example`
- ✅ `vm_runs_source_ref_multiple_scalar_assignment_example`
- ✅ `vm_runs_source_ref_nested_projection_assignment_example`
- ❌ `vm_runs_source_ref_string_lines_edit_example` （`ConflictingBounds`、後述）

canary：

- ❌ `vm_host_flushes_file_handle_string_edits` （`unexpected request: ref_update::update`、VM ハンドラ層）

## 残課題 1: `string_lines_edit` の `ConflictingBounds`

落ち方:

```text
ConflictingBounds {
  var: t16718#0,
  previous: Inter([Row[&s#1296; ⊤], Row[var; ⊤],
                   Recursive { var: t17296, body: Row[], tail: Any }]),
  next: Row[&s#1296, var, tail: Never]
}
```

`t16718#0` の Upper slot に 2 つの bound が来る:

- 1 つ目: `Inter([..., Recursive])`（call-site の effect upper、open row の Inter）
- 2 つ目: closed `Row[&s, var, tail: Never]`（同じ effect 集合を closed 表現で渡してきたもの）

意味的には `Row[&s, var, Never] <: Inter[Row[&s; ⊤], Row[var; ⊤], Recursive]`
なので、片方を取捨選択すれば矛盾しないはず。今は `push_bound` の merge ロジックに
Inter ↔ Row を合成する経路がない。

試したこと（採用していない）:

- `push_bound` の末尾で「Upper の conflict は `Inter([previous, ty])` で合成」「Lower の
  conflict は `Union([previous, ty])` で合成」する last-resort merge。`propagate_constraints`
  の fixpoint loop で `Inter` が毎回成長し、`vm_runs_source_ref_string_lines_edit_example`
  が即ハングする（無限に新しい upper bound が生まれて changed=true で抜けない）。
  別 commit で安全に入れたい場合、`bounds_are_equivalent` で「すでに含まれている item は
  再度足さない」normalization を組み合わせる必要がある。
- `constrain_type_arg` の `Type vs Bounds` / `Bounds vs Type` を両方向にする。conflict
  は依然出る（Bounds vs Bounds 経路から来ている）し、両方向にすると別な subtype 制約も
  増えるので問題が広がる。

次に手を入れるなら:

1. `merge_row_bounds` (`graph.rs:1218`) の入力として `Inter` を許容する。
   `Inter([Row1, Row2, ...])` を flatten すると row 集合になるので、その全 member と
   `Row` の merge を試す。今は `flatten_closed_row(Inter)` が `None` を返して即破棄。
2. `push_bound` で `Recursive` を含む bound の扱いを決める。`Recursive { var, body }` を
   `type_contains_var` で var ありと見なせば、conflict ではなく silent drop（`Ok(false)`）
   に落ちる。今は Recursive がパターン match から漏れて `_ => false` 扱いされ、conflict
   まで届く可能性がある（`graph.rs:1766` の `type_contains_var` を確認）。
3. lines_edit の subtype trace を `YULANG_TRACE_SUBTYPE` 相当で再現できるように temp で
   trace を仕込んで（今回消したのと同じパターン）、`t16718#0` の Upper に Row[&s, var]
   が来る経路を特定する。`Bounds vs Bounds` の `lower.lower <: upper.lower` か、
   `apply_subtype_constraint_inner` の `(Var, _)` rule で `Var.lower` を取って upper と
   再帰、のどちらかで来ているはず。

## 残課題 2: canary `vm_host_flushes_file_handle_string_edits`

monomorphize は通り、VM 実行時に `unexpected request: Path { segments:
[Name("std"), Name("var"), Name("ref_update"), Name("update")] }` で落ちる。
2026-05-26 メモにある通り「handler arm body の中で resume 側から次の
`ref_update::update` が出て top まで漏れる」現象。export 側で生成した
`__ref_set_loop` の handler が thunk boundary を作れていない疑いがあったが、
今回その実験コードは消してしまったので、再現 baseline はメモ時点と異なる
（現状は base の単発 handler）。

次の選択肢:

- (a) 2026-05-26 メモの疑似コードから実験 handler を復元してから VM trace を再開
- (b) `&ref = value` を `ref.update (fun _ -> value)` の path call に書き換える方向
  （`std::var::ref::update` は `our r.update f = ...` 由来で companion module に
  登録されているので、`core_standard_ref_member_path("update")` で path 化できる。
  事前に Agent で確認済み）
- (c) source 側 `lib/std/var.yu` の `our r.update f = ...` 実装そのものを直接呼ぶ
  シンプルテストを書いて、source 経由の挙動が現状の monomorphize で通るか確認してから
  判断

個人的には (c) で source の `r.update` が動くか確認 → 動くなら (b) に倒す、が
コストが低そう。

## 監査ドキュメントへの接続

`notes/bugs/yulang-infer-monomorphize-audit-2026-05-26.md` の：

- Issue #4 (Union/Inter half-implementation): 今回は `(Inter(items), upper)` /
  `(lower, Union(items))` の追加 rule は revert したので未対応。`string_lines_edit`
  の conflict と関係する可能性。
- Issue #18 (constructor variance を見ない): `Bounds vs Type` で片方向だけにしたのは
  この問題の symptom 側を回避しているだけ。本来は型コンストラクタの variance を
  見るべき。
- Unresolved の `materialize.rs` thunk-adaptation regression: 今回は触っていない。
  canary の handler 漏れと関係するかもしれないので、(a)(b) を進める前に
  `materialize_thunk_to_value_or_coerce` の force trigger を audit メモの推奨どおりに
  narrow する手も検討。

## コミット履歴

- `f9edd2e` WIP: monomorphize Bounds vs Type subtyping fix snapshot
  - trace 残し版。`Type vs Bounds`・`Bounds vs Type` が両方向、ref テスト 6/7 通過。
- 本コミット（このメモを書いている時点）
  - trace を削除、`Type vs Bounds`・`Bounds vs Type` を片方向に絞る。
  - 結果は同じ 6/7 通過、lines_edit の conflict は依然残る。

## 注意

`Codex がハング fix を入れた `cargo test` テスト群` があるため、進行中の差分を
全部 `git stash` して base HEAD で確かめるとテストが本当にハングする
（再ビルドの遅さの話ではなく、テスト本体）。差分は維持したまま部分検証する。
