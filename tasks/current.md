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
- これは、代入表を載せるだけでは demand collection / generic call closure の形がまだ変わらないためだと思われる。次は demand signature を「型を再推測する」より「主型へ代入する」流れへ寄せる必要がある。

## Next Steps

1. runtime monomorphize の generic call closure で、callee 主型 + substitutions から直接 demand signature を作る。
2. demand collection で `arg/result` evidence から型を再推測している箇所を、代入済み主型の param/ret 参照へ寄せる。
3. 代表型を「変数ごと」ではなく「evidence slot ごと」に決める。callee / arg / result のどの位置で同一視してよいかを、slot の極性と型形状に沿って制限する。
4. 下界 concrete part の候補を、閉じた型を拾うだけでなく、slot の期待形と合うものだけに絞る。関数 slot の代表が value arg slot に流れないようにする。
5. `YULANG_COALESCE_APPLY_EVIDENCE=1` の経路で、代表型なしの共起共有が runtime pass に効かない理由を調べる。
6. report API を使って、実プログラムで `Some(to)` / `None` / concrete representatives がどの程度出ているか数える。
7. `id : a -> a`、`range`、`fold`、record constructor の小さい例で、slot ごとの代表型が期待通りになる単体テストを作る。
8. binding scheme、root expr など、他の export 対象にも別々の simplification relation を持てる形に広げる。
9. 単一化できない境界にだけ cast / evidence を入れる実験を作る。
10. その経路で `DemandEngine` を通さず VM 前段まで進められるか測る。
11. role / associated type / effect / thunk shape の責務を、runtime monomorphize から切り出せるか分類する。

## Notes

- `crates/yulang-runtime/src/monomorphize/` は現在、demand collection、checking、specialization emit、role call 解決、effect hole closure、cleanup をまとめて抱えている。
- このまま大きく最適化するより、まず「runtime が demand-driven に再推測しなくてよい型変数関係」を増やす。
- effect / thunk / `bind_here` は実行形の問題も含むため、infer へ無理に押し込まない。
- 計測は必要だが、先に設計上の責務を分ける。計測対象は pass 単位だけでなく、collect / check / emit / rewrite / validate / refine / prune の内訳まで見る。
