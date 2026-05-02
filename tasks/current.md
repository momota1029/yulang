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

より根本的には、既存の demand-driven monomorphize を賢くするのではなく、主型に対する型代入だけで specialization を作る新しい pass を用意する必要がある。この pass は「単一化できる場所は素直に同じ型として扱い、単一化できない境界にだけ cast / thunk / bind_here を入れる」ことを目的にする。既存の demand/refine/fixpoint 系は、その新パスが処理できなかった場所の fallback として残し、計測上だんだん使われなくなることを確認する。

最終目標は、古い不動点型の monomorphize を 6-8 回回す構造から、主型代入による 1 pass specialization へ寄せること。

## New Direction: Substitution Specialization

新しく `SubstitutionSpecialize` のような pass を作る。

- 入力は `ApplyEvidence.principal_callee` と `ApplyEvidence.substitutions`、および binding の主型情報。
- specialization key は `DemandSignature` ではなく、`target + normalized type substitutions` に寄せる。
- binding clone は、body / scheme / evidence / runtime type annotation に型代入をそのまま適用して作る。
- call site は、代入済み callee 型と実際の arg / result 型を局所的に合わせる。
- 合う場所は rewrite しない。合わない場所だけ `Coerce`、value-to-thunk wrapper、thunk-to-value `BindHere` を入れる。
- role method は、代入済み receiver / associated type から concrete impl を選べる場合だけこの pass で解く。解けない場合は既存 role-specialization へ落とす。
- effect / thunk / `bind_here` は、型代入だけでは足りない実行形の問題として runtime 側で補う。ただし demand-driven に型を掘り直す理由にはしない。

この pass が存在する場合、pipeline の前半で先に走らせる。後半の `DemandSpecialize` / `RefineTypes` / `RefreshClosedSchemes` / role fixpoint は互換用として残し、`added_specializations` や changed binding 数がどれだけ減るかを測る。

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
- `YULANG_SUBST_SPECIALIZE=1` の opt-in で、`substitution-specialize` pass の最小入口を追加した。
- 最小版は apply spine を `head Var + args[]` として読み、`TypeInstantiation` または `ApplyEvidence` から `target + normalized type substitutions` の key を作る。
- clone した binding body には型代入を適用し、さらに新パスの rewrite を再帰的にかける。これにより wrapper だけでなく、clone 内部の generic call も順に新パスへ移せる。
- `ApplyEvidence.principal_callee` がない call でも、`TypeInstantiation` がある場合は binding の `scheme.body` を主型として使う。
- `examples/07_junction.yu` では新パスが 3 specialization を先に作り、旧 `DemandSpecialize` の初回追加は 8 から 7 に下がった。role-specialization の新規 specialization は 8 から 0 に下がった。
- ただし全体では `substitution-specialize` 自体が 1 pass 増えるため、`mono_passes` は 13 から 14。`specializations` は 10 のまま。
- `examples/10_effect_handler.yu` は 9 passes / 1 specialization から 14 passes / 2 specializations に悪化した。`test.yu` は 37 passes / 23 specializations から 38 passes / 24 specializations に悪化した。現時点では opt-in 実験経路であり、通常経路へは入れない。

## Next Steps

1. `SubstitutionSpecialize` pass の最小入口を作る。まずは opt-in で、`ApplyEvidence.principal_callee + substitutions` がある direct generic call だけを対象にする。
2. `target + normalized type substitutions` から specialization key / path を作る table を用意する。既存 `DemandSignature` table とは別にする。
3. binding body に型代入を適用して clone する最小 emitter を作る。最初は型注釈と apply evidence の substitution だけを置き換える。
4. call site で代入済み param / ret と実際の arg / result が合わないときだけ、`Coerce` / `Thunk` / `BindHere` を挿入する局所 adapter を作る。
5. 新パス後に既存 pipeline を走らせ、`DemandSpecialize` の `added_specializations` と changed binding 数が減るか測る。
6. `examples/07_junction.yu` の `fold_impl` / `view_raw` が新パスで先に作られ、role-specialization 2 周目の 4 binding 変化が消えるか確認する。
7. role method / associated type / effect row / recursive call は、最小経路が動いてから順に新パスへ移す。
8. 旧 demand-driven pass が必要になった call site を debug 出力し、「なぜ型代入だけで足りなかったか」の分類に使う。
9. 代表型を「変数ごと」ではなく「evidence slot ごと」に決める。callee / arg / result のどの位置で同一視してよいかを、slot の極性と型形状に沿って制限する。
10. binding scheme、root expr など、他の export 対象にも別々の simplification relation を持てる形に広げる。
11. role / associated type / effect / thunk shape の責務を、runtime monomorphize から切り出せるか分類する。

## Immediate Next Steps

1. `substitution-specialize` は、既定では self-recursive / leaf specialization と arg shape adaptation をしないように絞った。`examples/10_effect_handler.yu` は 14 passes / 2 specializations から 10 passes / 1 specialization へ戻り、`test.yu` は 38 passes / 23 specializations になった。
2. `examples/07_junction.yu` では `list<int>` と `list<int <: _>` の違いを exact-ish に扱うことで `all__mono0` / `any__mono1` は作れるようになった。ただし旧 demand がそれらを再処理するため、全体はまだ 14 passes / 10 specializations のまま。
3. `YULANG_SUBST_SPECIALIZE=1` の collector では、`__mono` call を元の generic target へ戻さないようにした。これで `all__ddmono` / `any__ddmono` の外側 wrapper は消えたが、`all__mono0` / `any__mono1` の body から `std::junction::junction::{all,any}` 側の demand が出るため、総数はまだ同じ。
4. `substitution-specialize` は、binding の `type_params` だけでなく scheme/body に残る型変数も substitution 対象として見るようにした。さらに evidence がない call でも、すでに生成中の `__mono` body 内なら arg/result から代入を推測するようにした。
5. これで `examples/07_junction.yu` の `std::junction::junction::{all,any}` は `__mono` 化できた。残りは `std::list::&impl#187::fold`、`std::flow::sub::sub`、`std::list::fold_impl`、`std::list::view_raw`、`std::junction::junction::junction` が旧 demand 側に残っている。
6. 空 evidence からの推論は root call には許可しない。これにより `test.yu` の `&p#587::var_ref__mono0` のような余計な root specialization は避け、38 passes / 23 specializations を保っている。
7. role method call について、receiver 型から concrete impl binding を一意に選べる場合は substitution pass で impl 側へ直接向ける実験を入れた。`examples/07_junction.yu` では `std::fold::Fold::fold` が `std::list::&impl#187::fold__mono2` へ寄るようになった。
8. `Fold::fold` の callback effect 変数 `e` を閉じるため、型代入推論に function effect も見る入口を追加した。これで role call は新パス側へ移せたが、`fold_impl` / `view_raw` はまだ旧 demand 側に残る。
9. `fold_impl` が残る理由は、新パス時点の impl body 内 call がまだ `Any` 寄りで、後続 refine 後に `list<int>` へ締まるため。次は `RefineTypes` 後に限定的な `SubstitutionSpecialize` をもう一度走らせる実験、または `substitute_binding` 側で local/pattern 型までより強く置換する実験をする。
10. `YULANG_SUBST_SPECIALIZE_REFINE_RETRY=1` として retry 実験をした。先頭の置換特化後に `RefineTypes -> SubstitutionSpecialize` を挟む形は `test.yu` で polymorphic binding を残して失敗した。initial `DemandSpecialize -> RefineTypes` 後にもう一度だけ走らせる形は通るが、`examples/07_junction.yu` は 15 passes / 10 specializations、`examples/10_effect_handler.yu` は 11 passes / 1 specialization、`test.yu` は 39 passes / 23 specializations で、単に 1 pass 増えた。したがって retry ではなく、`fold_impl` call site が `Any` のまま残る原因を潰すほうへ戻す。
11. `local_refresh` を追加し、型代入で clone した binding body の中だけ、lambda 引数、let/match/handle pattern、resume binding から分かるローカル型を `Var(local_...)` の `ty` へ流し直すようにした。これで `examples/07_junction.yu` の `std::list::fold_impl` は旧 `__ddmono` ではなく `std::list::fold_impl__mono3` として新パス側へ移った。
12. leaf specialization を全開にすると `examples/10_effect_handler.yu` のローカル再帰 `listen` が `unbound variable listen` で壊れた。そのため、既定では単一 segment のローカル leaf は旧 demand 側に残し、`std::...` のような module path を持つ leaf は新パスで扱えるようにした。これで `examples/07_junction.yu` の `std::list::view_raw` も `std::list::view_raw__mono4` へ移った。パス数はまだ `junction` 14、`effect_handler` 10、`types` 10 のままで、残る旧 demand は主に `std::flow::sub::sub`、`std::junction::junction::junction`、role impl の `lt/add`、ローカル再帰系。
13. infer/export 側に `export::complete_principal` module を切った。これは「完全主型付き evidence」を作る責務の置き場で、既存の `principal_callee + substitutions` 生成を `types.rs` から移した。今は挙動を変えない移設だが、次はここに slot ごとの極性消去・共起 relation・代表型選択を足して、runtime が demand で型関係を掘り直さなくてよい形へ寄せる。
14. `complete_principal` で apply evidence の callee/arg/result を同じ slot relation として coalesce し、その arg/result slot から substitution を作るようにした。`examples/07_junction.yu` の pass 数はまだ 14 のまま。なお callee slot 全体を主型と照合する実験は `t4327 := ⊥` のように下界の `Never` を値型代表として拾ってしまうため危険だった。callee はそのまま推測に使わず、今は arg/result slot に限定する。
15. `complete_principal` の substitution 作成を小さな unifier にした。関数型の param/ret だけでなく param effect / ret effect も単一化対象にし、同じ主型変数へ複数の異なる具体候補が出た場合は早い者勝ちにせず、その変数の substitution を落とす。`examples/07_junction.yu` の pass 数はまだ 14 のままだが、代表を無理に選ばない形になった。
16. unifier の候補 merge を少し強めた。`list<int <: _>` と `list<int>` のように bounds と concrete type が同じ形なら concrete 側へ寄せる。値型位置では `Never` を substitution 代表にしないが、effect 位置では空 effect として `Never` を許す。これらは `complete_principal` の単体テストで固定した。`examples/07_junction.yu` はまだ 14 passes / 10 specializations。
17. `complete_principal` が principal scheme の role requirements も見るようにした。式 evidence 側の `principal_callee_scheme` も compact scheme から `export_scheme(..., role_constraints)` で requirements 付きに復元する。現在は保守的に `item` associated + `list<T>` だけを扱い、`Fold<list<int>, item=t>` から `t := int` を出す。`examples/07_junction.yu` の root evidence では `t4144 := list<int <: _>, t4327 := int` と `t4060 := list<int <: _>, t4332 := int` が出るようになった。ただし runtime 側の pass 数はまだ 14 のまま。
18. `substitution-specialize` の role impl index に、型変数を持たない単相 impl も入れるようにした。空代入は clone せず元 binding へ直接向ける。impl receiver 選択では通常の widening 互換を使わず exact/bounds matching に絞ったので、`int` receiver が `float` impl まで拾うことはなくなった。`examples/07_junction.yu` では `std::prelude::&impl#487::lt__ddmono` が消え、`std::prelude::&impl#487::lt` + call site の thunk wrapper になった。`specializations` は 10 から 9 に減ったが、`mono_passes` はまだ 14。残り旧 demand は `std::flow::sub::sub` と `std::junction::junction::junction` が中心で、これは型代入より effect handler/control boundary の問題として見えている。
19. `substitution-specialize` が runtime `Thunk` の effect を見て、関数型の `param_effect` / `ret_effect` へ代入を推測する入口を追加した。これで `std::flow::sub::sub` の欠けていた `t3188` は取れることを確認したが、そのまま clone すると handler body の thunk/row adapter が未整備なため effect row が増殖し、`examples/07_junction.yu` が 38 passes まで悪化した。したがって既知 handler target (`std::flow::sub::sub`, `std::junction::junction::junction`, `std::undet::undet::*`) は新パスから明示的に除外した。現在の opt-in 計測は `junction` 14 passes / 9 specializations に戻っている。次は型代入ではなく、handler body 専用の residual_before/residual_after と return wrapper を一発で作る adapter が必要。

## Notes

- `crates/yulang-runtime/src/monomorphize/` は現在、demand collection、checking、specialization emit、role call 解決、effect hole closure、cleanup をまとめて抱えている。
- このまま大きく最適化するより、まず「runtime が demand-driven に再推測しなくてよい型変数関係」を増やす。
- effect / thunk / `bind_here` は実行形の問題も含むため、infer へ無理に押し込まない。
- 計測は必要だが、先に設計上の責務を分ける。計測対象は pass 単位だけでなく、collect / check / emit / rewrite / validate / refine / prune の内訳まで見る。
