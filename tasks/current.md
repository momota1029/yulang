# Current Task: runtime specialization redesign

## Context

`yulang-runtime` の `monomorphize` は、現在は demand-driven に具体的な呼び出し形を集め、`DemandSignature` を作り、必要な specialization を emit している。

ただし、これは runtime 側で型情報を再発見しようとしている面が強い。主型の意味が「単一の代表型を渡し、ML のように素直に単一化し、単一化できない場所にだけ cast を挟む」ものなら、runtime でむやみに単相化する設計は重すぎる。

さらに、infer 側の compact / co-occurrence / polar simplification で得た「この場所では同じ型として見てよい」という情報が、lowering 以降へ明示的に渡っていない。この欠落を runtime の monomorphize が補おうとしている可能性が高い。

## Goal

runtime の高速化を直接進める前に、型情報の責務を整理する。

- infer は、compact / co-occurrence / polar simplification で得た場所ごとの同一視関係を捨てない。
- lower は、主型に基づいて素直に型代入し、必要な場所だけ cast / evidence を明示する。
- runtime は、上流で消えた型変数関係の復元をなるべく背負わない。
- effect / thunk / `bind_here` の配置など、VM の実行形に関わる調整は runtime 側の責務として残してよい。
- 既存の demand-driven monomorphize は、必要なら互換用または未整理ケース用の逃げ道へ縮小する。

## Current Hypothesis

今の `monomorphize` は高速化対象というより、上流から失われた型変数関係を復元する補償パスになっている面が強い。

そのため、単に `monomorphize` を統合・高速化しても効果は限られる。まず infer/lower から runtime へ渡す型変数関係を正しくし、runtime 側が demand-driven に型関係を掘り直す量を減らすほうが筋がよい。

## Initial Findings

- `Infer` は union-find のような全体等価クラスを持っていない。型変数の情報は主に `lower: TypeVar -> PosId[]` と `upper: TypeVar -> NegId[]` に入る。
- `Pos::Var(a) <: Neg::Var(b)` は、`b` の lower に `a` を足し、`a` の upper に `b` を足して伝播する。ここでは `a = b` として代表元を結合していない。
- ready component の commit 時に `compact_type_vars_in_order_profiled` で compact scheme を作り、その後 `coalesce_by_co_occurrence_with_role_constraints` で見た目の型変数を潰している。
- co-occurrence は `HashMap<TypeVar, Option<TypeVar>>` の置換で変数を消す/寄せる後処理で、制約グラフの等価関係そのものとして lower/export へ残っているわけではない。
- 極性消去は `apply_polar_variable_removal` で、片側だけに出る非再帰・非 protected 変数を `None` にする。これはその場所にあった型と同一視できる情報として扱える。
- 共起分析で `Some(to)` になった置換は、その compact/export 対象の中では `from = to` として扱える。ただし、どの変数が消えるか/残るかは対象ごとに違うため、グローバルな union-find ではなく、場所ごとの substitution / relation として扱う必要がある。
- `export_apply_evidence` は callee / arg / result の bounds を式ごとに再 export している。ここに「同じ型である」という関係が明示されないと、runtime 側が evidence から再推測する形になりやすい。

## Current Implementation

- `coalesce_by_co_occurrence_with_role_constraints_report` を追加した。
- 既存の `coalesce_by_co_occurrence_with_role_constraints` は互換のため残し、新しい report API を呼ぶ形にした。
- report は各 round の `subst: HashMap<TypeVar, Option<TypeVar>>` を保持する。
- `Some(to)` は対象内の同一視、`None` は polar / exact removal による吸収として観測できる。
- 単体テストで、共起による `Some(to)` と極性消去による `None` の両方を確認した。
- `CoalesceRound` に `representatives: HashMap<TypeVar, CompactType>` を追加した。
- 代表型は、その round の下界側で型変数と同居していた concrete part から集める。
- `a | int` のような compact type で `a` が消える場合に、`a` の代表型として `int` を取り出せることを単体テストで確認した。
- `core_ir::ApplyEvidence` に `principal_callee: Option<Type>` と `substitutions: Vec<TypeSubstitution>` を追加した。
- `YULANG_EXPORT_APPLY_SUBSTITUTIONS=1` の opt-in で、呼び出し位置に callee の主型と「主型の型変数への代入」を載せる。
- `YULANG_USE_APPLY_SUBSTITUTIONS=1` の opt-in で、runtime monomorphize が evidence の `principal_callee` に `substitutions` を適用した callee 型を hint として読む。
- core-ir の verbose 表示に `principal=...` と `subst=[t := ty]` を出すようにした。
- generic call closure の入口を、opt-in 時は代入済み主型から param/ret hint を作るように変更した。
- これにより `closed_call_signature` は、head の runtime 型だけでなく、`principal_callee + substitutions` から得た引数列を seed hint として受け取れる。
- demand collection の generic / role call でも、opt-in 時は代入済み主型から param/ret hint を作るようにした。
- specialization emit の missing demand key 生成でも、opt-in 時は代入済み主型から param/ret hint を seed として使うようにした。

## Experiment Notes

- `export_relevant_type_bounds_for_tv` で単独 tv ごとに coalesced bounds を使う実験をした。
- `examples/10_effect_handler.yu` と `test.yu` の pass 数は変わらなかったが、`examples/07_junction.yu` は `std::flow::sub::sub` が多相のまま残って失敗した。
- このため、coalesced bounds を per-tv に雑に適用するのは危ない。必要なのは、apply evidence や binding などの export 対象ごとに同じ simplification relation を共有して使うこと。
- 代表型 rewrite は `YULANG_USE_COALESCE_REPRESENTATIVES=1` の opt-in にした。通常の coalesce / 表示 / export は変えない。
- 代表型 rewrite だけを全体の coalesce に入れても、`examples/07_junction.yu`、`examples/10_effect_handler.yu`、`test.yu` の `mono_passes` / `specializations` は変わらなかった。
- `YULANG_COALESCE_APPLY_EVIDENCE=1` を追加し、apply evidence の callee / arg / result を同じ compact 対象で coalesce する実験経路を作った。
- apply evidence の共起共有だけでは pass 数は変わらなかった。
- apply evidence に代表型 rewrite も入れると runtime lower で型不一致になった。代表型がスロットを越えて強く流れ、`arg` 側に関数型の代表が混ざるケースがある。
- 代表型を `Some(to)` ではなく `None` で消える変数だけに絞っても、まだ型不一致は残った。したがって、下界から取った concrete part をそのまま evidence slot へ入れるのは粗すぎる。
- 主型 + 代入表の opt-in 経路は壊れなかった。`examples/07_junction.yu` では `principal=t4448 ... -> ...` と `subst=[t4448 := int]` のような情報が出ている。
- ただし、`YULANG_EXPORT_APPLY_SUBSTITUTIONS=1 YULANG_USE_APPLY_SUBSTITUTIONS=1` でも、`examples/07_junction.yu`、`examples/10_effect_handler.yu`、`test.yu` の `mono_passes` / `specializations` はまだ変わらない。
- generic call closure も代入済み主型の param/ret を読むようにしたが、pass 数はまだ変わらなかった。つまり、今の pass 数は hint の精度だけでなく、demand queue の到達順や specialization emit/refine loop に支配されている可能性が高い。
- collection / check / emit の主要な call-signature 入口を代入済み主型へ寄せても、pass 数はまだ変わらなかった。
- `YULANG_DEBUG_DEMAND_CHECK=1` で見ると、`Fold.fold` の call hint は `list[int]` まで閉じている。一方で `std::list::fold_impl` には別経路から open demand が入り、`list_view[Hole]` と `Thunk[..., list_view[Hole]]` の不一致で一度失敗している。
- つまり、今残っている pass 数は「呼び出し位置の主型代入を読めていない」だけではなく、impl body / missing demand / effect thunk shape の閉じ方が後続 round に持ち越されることが原因になっている。
- `YULANG_DEBUG_DEMAND_SOURCE=1` を追加し、demand source を initial collect / pending missing / checked child に分けて見られるようにした。
- `std::list::fold_impl` の open demand は、主に `fold_impl` 自身を check している途中の再帰 child demand から出ていた。閉じた親 demand を check している self-recursive child は親の demand signature にそろえるようにした。
- 同じ target に閉じた demand がすでに queue にある場合、後から来た open demand は積まないようにした。落とす条件は、既存の closed signature が open demand の具体部分を覆う場合だけに絞った。これで `examples/07_junction.yu` の `fold_impl` / `view_raw` open demand は消えた。
- ただし `mono_passes` はまだ 13 のまま。現在の残りは open demand の check ではなく、pipeline の収束確認 round と、role-specialization の 2 周目で新規 specialization なしに rewrite/refine がもう一度だけ走る構造に寄っている。
- `SpecializationTable::seed_existing` の debug では、最終的な `fold_impl__ddmono13` / `view_raw__ddmono14` は既存 specialization として seed されている。したがって、次の問題は「seed できない」ではなく「role-specialization 1 周目で作った specialization の参照が、その周の後半だけでは安定しきらない」こと。
- role fixpoint に `canonicalize-specializations` を追加する実験では、収束周回は変わらず pass 数が 13 から 15 に増えた。重複名の canonicalize では今回の 2 周目は消えない。
- `YULANG_DEBUG_MONO_CHANGED=1` を追加し、pass ごとに変化した binding/root を見られるようにした。
- `examples/07_junction.yu` の role-specialization 2 周目で変わる binding は `std::junction::junction::{all__ddmono9, any__ddmono10}`、`std::list::&impl#187::fold__ddmono11`、`std::list::fold_impl__ddmono13` の 4 つ。新規 specialization はないため、role call が impl specialization へ置き換わったあと、body 型が refine でもう一段安定する遅延として見てよい。

## Next Steps

1. role-specialization 2 周目の 4 binding について、`demand-specialize` がどの call path を書き換え、`refine-types` がどの type slot を変えるかを式単位で見る。
2. 2 周目が新規 specialization なしの参照安定化だけなら、同じ周の中で rewrite/refine をもう一度だけ局所的に回すほうが安いか測る。
3. `list_view[Hole]` と `Thunk[..., list_view[Hole]]` のずれを、effectful return の shape 問題として閉じられるか確認する。
4. child demand を queue へ積む段階で、代入済み主型から specialization key を直接作れるか試す。
5. 代表型を「変数ごと」ではなく「evidence slot ごと」に決める。callee / arg / result のどの位置で同一視してよいかを、slot の極性と型形状に沿って制限する。
6. 下界 concrete part の候補を、閉じた型を拾うだけでなく、slot の期待形と合うものだけに絞る。関数 slot の代表が value arg slot に流れないようにする。
7. `YULANG_COALESCE_APPLY_EVIDENCE=1` の経路で、代表型なしの共起共有が runtime pass に効かない理由を調べる。
8. report API を使って、実プログラムで `Some(to)` / `None` / concrete representatives がどの程度出ているか数える。
9. `id : a -> a`、`range`、`fold`、record constructor の小さい例で、slot ごとの代表型が期待通りになる単体テストを作る。
10. binding scheme、root expr など、他の export 対象にも別々の simplification relation を持てる形に広げる。
11. 単一化できない境界にだけ cast / evidence を入れる実験を作る。
12. その経路で `DemandEngine` を通さず VM 前段まで進められるか測る。
13. role / associated type / effect / thunk shape の責務を、runtime monomorphize から切り出せるか分類する。

## Notes

- `crates/yulang-runtime/src/monomorphize/` は現在、demand collection、checking、specialization emit、role call 解決、effect hole closure、cleanup をまとめて抱えている。
- このまま大きく最適化するより、まず「runtime が demand-driven に再推測しなくてよい型変数関係」を増やす。
- effect / thunk / `bind_here` は実行形の問題も含むため、infer へ無理に押し込まない。
- 計測は必要だが、先に設計上の責務を分ける。計測対象は pass 単位だけでなく、collect / check / emit / rewrite / validate / refine / prune の内訳まで見る。
