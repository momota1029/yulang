# Current Task: runtime specialization redesign

## Current Decision: direct principal elaboration

The current direction is still the same large goal: move toward a typed IR that
can be elaborated in one syntax-directed pass, with old demand-driven
monomorphize acting as fallback rather than the main route.

The next major runtime step should not be an open-candidate graph solver and
should not be another round of runtime shape inference. `SubstitutionSpecialize`
has proved useful as an experiment, but the target concept is now
`PrincipalElaborate`:

- `complete_principal` should export enough principal elaboration evidence for a
  call site.
- runtime should execute that evidence: clone/rewrite/adapt.
- runtime should not rediscover Simple-Sub relations from runtime IR shapes on
  the main path.
- demand / refine / role fixpoint passes should become measured fallback.

Concrete next design target:

```text
infer/export
  complete principal elaboration evidence
    principal callee
    full-spine substitutions
    source-edge-backed arg/callee/result slots
    explicit adapter holes

PrincipalElaborate
  execute the plan
  clone target binding with normalized substitutions
  rewrite call to specialized binding
  insert only plan adapters

Old DemandSpecialize
  fallback only, with reachable/actionable fallback counters
```

Planned experiment flags:

```text
YULANG_PRINCIPAL_ELABORATE=1
YULANG_PRINCIPAL_ELABORATE_STRICT=1
```

Current implementation status:

- `YULANG_PRINCIPAL_ELABORATE=1` exists.
- It currently runs a `principal-elaborate` monomorphize pass that delegates to
  the old substitution-specialize implementation.
- Core IR now has `PrincipalElaborationPlan` on `ApplyEvidence`.
- `complete_principal` / export now builds a first conservative plan from
  `principal_callee`, closed substitutions, substitution candidates, source
  edges, and apply arg/result slots.
- The initial plan is intentionally observational: adapter holes are empty,
  expected runtime slot types are not executed yet, and incomplete reasons are
  conservative.
- `CoreShape` counts apply sites with principal elaboration plans and splits
  them into complete / incomplete.
- Runtime still delegates plan execution to the old substitution-specialize
  fallback. The next required step is strict plan execution / failure reporting.
- `YULANG_PRINCIPAL_ELABORATE_STRICT=1` is planned but not implemented yet.

Strict mode should fail with explicit incomplete plan reasons instead of silent
fallback. A useful first strict result is a small list like:

```text
std::flow::sub::sub: HandlerBoundaryWithoutPlan
std::range::fold_ints: MissingSubstitution(t1193), OpenCandidate(t1254)
std::list::fold_impl: MissingAdapterHole(ValueToThunk)
```

Important non-goals right now:

- Do not solve `t <= t | u` / `t >= t & u` with a runtime graph solver.
- Do not revive global representative-type rewriting.
- Do not make handler specialization default.
- Do not make runtime infer substitutions from arg/result runtime shapes on the
  principal-elaborate main path; keep those helpers as fallback only.

The `CoreShape` and diagnostic work remains useful, but as observability for the
same typed-IR direction, not as a separate detour.

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

## Elaboration Direction

`SubstitutionSpecialize` は「主型に型代入を入れる」だけでは足りない。subtyping / effect / thunk / handler boundary では、型が合わない位置をあとから探すのではなく、infer/lower の制約生成時点で `CastHole` / `AdapterHole` に相当する evidence を置く必要がある。

この方向では、各式に少なくとも次の 2 種類の型を区別して持たせる。

- intrinsic type: その式が自然に合成した型。
- contextual type: 親の文脈から期待され、cast / adapter 後に使われる型。

`A <= B` が必要な境界では、`CastHole(origin, A, B)` のような evidence を作る。runtime はその hole を見て、値の `Coerce`、value-to-thunk wrapper、thunk-to-value `BindHere`、handler adapter のいずれかを埋める。これにより、主型代入で合う場所は単純に clone し、合わない場所だけを syntax-directed に elaboration できる。

`complete_principal` の責務は、今の `principal_callee + substitutions` 生成から、最終的には「principal elaboration evidence」生成へ広げる。まずは既存の `ApplyEvidence` に近い位置で、callee / arg / result の intrinsic/contextual 型と adapter hole を opt-in で持たせる。infer 全体を bidirectional typing へ一気に書き換えるのではなく、apply evidence と handler boundary から段階的に進める。

`HandlerAdapterPlan` は、この `AdapterHole` の effect/thunk 版として扱う。`std::flow::sub::sub` のように型代入だけでは clone できない binding は、handler boundary に adapter hole が足りないケースと見なし、hole がない間は旧 demand-driven path へ明示的に落とす。

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
19. `substitution-specialize` が runtime `Thunk` の effect を見て、関数型の `param_effect` / `ret_effect` へ代入を推測する入口を追加した。これで `std::flow::sub::sub` の欠けていた `t3188` は取れることを確認したが、そのまま clone すると handler body の thunk/row adapter が未整備なため effect row が増殖し、`examples/07_junction.yu` が 38 passes まで悪化した。したがって `ExprKind::Handle` を含む binding は、新パスから構造的に除外するようにした。`std::flow::sub::sub` と `std::junction::junction::junction` は名前ではなく body の handler boundary によって `handler-binding` と判定される。現在の opt-in 計測は `junction` 14 passes / 9 specializations に戻っている。次は型代入ではなく、handler body 専用の residual_before/residual_after と return wrapper を一発で作る adapter が必要。
20. handler boundary の構造解析を `pipeline::handler_boundary` module に切り出した。`HandlerBindingInfo` は `consumes`、`residual_before_known`、`residual_after_known`、`pure` を持つ。`YULANG_DEBUG_SUBST_SPECIALIZE=1` では `std::flow::sub::sub` が `consumes=[std::flow::sub] residual_before=true residual_after=true pure=true`、`std::junction::junction::junction` が `consumes=[std::junction::junction] ... pure=true` と出る。次の handler adapter はこの情報を入口にして作る。
21. `HandlerCallBoundary` を追加し、handler binding の主型側 input/output effect と、呼び出し地点の runtime thunk input/output effect を同時に見られるようにした。debug では `std::flow::sub::sub` の consumed effect は主型側 input effect に残る一方、呼び出し地点の arg thunk effect には `junction` だけが見えるケースがある。したがって handler adapter は「呼び出し地点だけ」でも「主型だけ」でも足りず、主型側の consumed/residual 情報と call site の残り effect を合わせて一発で `residual_before` / `residual_after` / return wrapper を決める必要がある。
22. `HandlerAdapterPlan` を追加し、`HandlerBindingInfo + HandlerCallBoundary` から `residual_before`、`residual_after`、`return_wrapper_effect` を構造的に計算できるようにした。`std::flow::sub::sub` では plan が `sub + junction + tail` を before、`junction + tail` を after として出す。`std::junction::junction::junction` では before が `junction + tail`、after が `tail` になる。まだ clone は解禁せず、まず adapter の材料を debug と単体テストで固定した。
23. `YULANG_SUBST_SPECIALIZE_HANDLERS=1` の opt-in で、handler binding の substitution clone に `HandlerAdapterPlan` を流せるようにした。clone 側では最初の `Handle` に `residual_before` / `residual_after` を設定し、return wrapper は別 opt-in `YULANG_SUBST_SPECIALIZE_HANDLER_RETURN=1` に分けた。実験では `std::flow::sub::sub` のように consumed effect が call site input から消えていて residual_after が残る handler を clone すると `junction` が 38 passes に悪化する。一方で `std::junction::junction::junction` のように call site input が consumed effect を持ち、residual_after が空になる handler だけに絞ると、挙動は壊れず `junction` は 14 passes / 9 specializations のまま。つまり次の問題は return wrapper 以前に、「消費 effect が主型側にだけ残る handler」を clone 可能な形へ落とすこと。
24. `YULANG_SUBST_SPECIALIZE_HANDLER_CALL_ADAPTER=1` の opt-in で、unsupported handler plan のときに handler clone は作らず、call site の第 1 引数 thunk だけを `plan.residual_before` の effect へ持ち上げる経路を追加した。`std::flow::sub::sub` では `junction` thunk を `sub + junction` へ包み直してから旧 demand 側へ渡す。これは 38 passes には悪化しないが、`junction` は 14 passes / 9 specializations のままで削減にもつながらなかった。したがって call site の thunk shape を合わせるだけでは足りず、旧 demand が handler binding を再処理する構造そのものを減らす必要がある。
25. `examples/02_refs.yu` を計測対象に加えた。直接スカラー参照代入 `&x = ...` は lower 時点で参照を「読む」扱いから除外されていたため `&x` binding が作られず、未定義名になっていた。`VarBindingUsage` を read/write に分け、書き込みでも `var_ref` helper と参照 binding を用意するようにした。元の `02_refs.yu` は `[0] (11, 21)` で通る。通常実行は 37 passes / 39 specializations、置換 opt-in は 38 passes / 41 specializations で、参照系はまだ古い demand-driven 単相化に強く乗っている。
26. ChatGPT Pro への相談結果を方針へ反映した。Simple-sub は主型と subtyping constraint を扱うが、cast/coerce 挿入位置の決定は別の elaboration 問題として見る。今後は「制約解決後に cast 位置を探す」のではなく、型推論・制約生成時に hole を置き、解けた制約と runtime 型から hole を埋める方向へ寄せる。
27. 既存の cast 情報を棚卸しした。infer の `ExprKind::Coerce` は `actual_tv` / `expected_tv` を持っていたが、Core IR へ export すると `Coerce { expr }` だけになり、境界型が失われていた。`core_ir::CoerceEvidence { actual, expected }` を追加し、export 時に `actual_tv` / `expected_tv` の bounds を載せるようにした。runtime lower は閉じた evidence だけを `from` / `to` の補助として使う。未閉じの evidence を inner の期待型へ押し込むと `std::var::ref::update_effect__ddmono*` が多相のまま残るため、今は保守的に使わない。
28. `--core-ir --verbose-ir` で `coerce value :: coerce[actual=..., expected=...]` のように表示できるようにした。これで cast hole の存在は CLI から確認できる。`examples/01_struct_with.yu` の struct constructor / field projection で evidence が出ることを確認した。
29. `CoerceEvidence` は生の推論 bounds ではなく、`complete_principal` 経由で coerce slot 内の actual/expected を一緒に coalesce してから出すようにした。これにより `examples/01_struct_with.yu` の field projection は `coerce[actual=point, expected={x: int, y: int}]` のように主型に近い形で見える。constructor の `actual=_ expected=_` は、その境界だけでは具体型が取れないため空のまま残る。
30. `ExpectedEdge` を infer lowering 側に追加した。これは runtime IR へは渡さない軽い subsumption point の記録で、`actual_tv` / `expected_tv` / optional effect tv / kind / cause を持つ。最初の対象は `if condition`、`if branch`、`case guard`、`case branch`、`catch guard`、`catch branch`。`Coerce` は representation / runtime 的に意味のある境界へ残し、広い expected-type 境界は `ExpectedEdge` で観測する方針にした。application argument は関数 param 用の中間 tv を作ると推論形が変わるため、まだ対象外。
31. `ExpectedEdge` を CLI の `--infer --verbose-ir` で `expected-edges:` として見られるようにした。表示は `LowerState` 内の table を compact bounds で整形するだけで、Core IR / runtime IR にはまだ流さない。これで broad expected-type 境界を runtime に影響させず棚卸しできる。
32. `LowerState::expect_value` / `expect_value_and_effect` を追加し、`ExpectedEdge` 記録と solver constraint 生成を同じ入口にまとめた。if/case/catch の condition / guard / branch はこの helper 経由に置き換えた。bool condition / guard は `expected_bool_tv` を exact bool にし、実際の制約も `actual_tv <= expected_bool_tv` として edge と同じ境界を指すようにした。
33. annotation に `ExpectedEdgeKind::Annotation` を追加で接続した。binding annotation と pattern/header parameter annotation は annotation 用 `ann_tv` を exact に作り、`target_tv <= ann_tv` を `expect_value` 経由で記録・制約化する。既存の双方向 annotation constraint は `ann_tv <= target_tv` を別途張って保つ。bool condition / guard の exact bool tv 生成も cause 付きにそろえた。
34. `ConstraintReason` に match/catch/assignment 用の細かい reason を追加し、case/catch の guard / branch が `IfCondition` / `IfBranch` を流用しないようにした。priority は既存の if/app/field と同じ診断優先度にした。
35. `ExpectedEdgeKind::ApplicationArgument` を apply lowering に接続した。関数側の argument slot として `expected_arg_tv` を作り、`arg.tv <= expected_arg_tv` を `expect_value` で記録し、関数制約は `func.tv <= expected_arg_tv -> result` にした。これにより application argument も solver が実際に見る subsumption 境界として観測できる。
36. direct ref assignment に `ExpectedEdgeKind::AssignmentValue` を接続した。`RefSet` lowering では参照の要素型用 `expected_value_tv` を作り、`value.tv <= expected_value_tv` を `expect_value` で記録してから、reference 側を `std::var::ref<ref_eff, expected_value_tv>` に合わせる。
37. `collect_expected_edges` の表示側で `TypeVar -> CompactTypeScheme` の小さな cache を入れた。表示文字列ではなく compact 結果だけを cache し、edge ごとの `VarNamer` は維持するので、同じ edge 内の型変数名付けは従来通りに保つ。
38. 通常の `ExpectedEdge` について、`actual_tv <= expected_tv` と effect edge の `actual_eff <= expected_eff` が solver に入っていることをテストで固定した。kind と `ConstraintReason` の対応もあわせて見る。
39. `ExprKind::Coerce` を作る synthetic struct / enum constructor と struct field projection で、`ExpectedEdgeKind::RepresentationCoerce` を記録するようにした。これは runtime 表現境界なので、通常の `expect_value` とは分けて制約は追加しない。
40. direct ref assignment の `AssignmentValue` cause に右辺 span を入れるようにした。これで diagnostic / hover で「代入値が期待型へ流れた場所」を辿りやすくなった。
41. CLI の型エラー表示で、`Annotation` / `ApplicationArgument` / `AssignmentValue` の `ExpectedEdge` が直接の error cause と一致する場合に、`context: annotation expected int; expression provides string` のような文脈行を出すようにした。まずは直接 cause が残っている edge だけを使い、伝播後に `Unknown` へ落ちる assignment error の復元は次段階へ残した。

## Notes

- `crates/yulang-runtime/src/monomorphize/` は現在、demand collection、checking、specialization emit、role call 解決、effect hole closure、cleanup をまとめて抱えている。
- このまま大きく最適化するより、まず「runtime が demand-driven に再推測しなくてよい型変数関係」を増やす。
- effect / thunk / `bind_here` は実行形の問題も含むため、infer へ無理に押し込まない。
- 計測は必要だが、先に設計上の責務を分ける。計測対象は pass 単位だけでなく、collect / check / emit / rewrite / validate / refine / prune の内訳まで見る。
- `examples/02_refs.yu` は回帰対象に残す。参照 direct assignment は直ったが、置換 opt-in では通常経路より 1 pass / 2 specializations 増えるので、参照 helper (`run/get/set/var_ref`) を新パスで扱うか、まず旧 demand のまま残すかを分けて見る。
- 最終形は「主型代入だけで全部を解く」ではなく、「主型代入 + constraint 生成時に置いた elaboration hole を埋める」形にする。cast 位置の選択は typing derivation に依存しうるため、実装として正規の elaboration 形をひとつ決める。
- `CoerceEvidence` は IR 上の cast hole として保持できるようになったが、runtime lower が積極的に活用できるのは閉じた型だけ。未閉じの `actual` / `expected` をそのまま期待型として流すと、多相 helper が残る。次は `complete_principal` 側で slot-local に閉じた evidence を作るか、runtime 側で `AdapterHole` として遅延処理するかを分ける。
- `CoerceEvidence.expected` を runtime lower の式型として親の `expected` より優先すると、`std::opt::opt::nil` などの多相 constructor が閉じきらず壊れる。runtime lower では親の文脈を優先し、coerce evidence は補助情報として扱う。
- `ExpectedEdge` は今のところ `LowerState` 内の観測用 table と CLI verbose 表示で、export / runtime には影響しない。次は `ExpectedEdge` を principal elaboration evidence 生成に接続するか、application argument / annotation / assignment value へ広げるかを選ぶ。
- `ExpectedEdge` を増やす場合は、直接 `record_expected_edge*` を呼ぶより先に `expect_*` helper を通す。edge と solver constraint が同じ subsumption 境界を表す、という invariant を崩さない。
- annotation edge は今のところ value type の annotation が対象。effect-only annotation は `ExpectedEdge` が value tv を必須にしているため、別途 `ExpectedEffectEdge` を作るか `ExpectedEdge` を effect-only に対応させるかを決めてから扱う。
- `RecordField` / `VariantPayload` は enum にはあるが、今回は保留。record / variant は現状だと値を組み立てる側の制約が多く、expected subsumption 境界として切る位置を先に決める必要がある。
- `RepresentationCoerce` edge は記録済みだが、通常の expected subsumption edge とは違って solver constraint の副産物ではない。`CoerceEvidence` / future adapter hole との対応を見るための観測点として扱う。
- diagnostic で使う `ExpectedEdge` は、今は direct cause/span が合うものだけ。`&x = "s"` のあと別の annotation で矛盾するような伝播越しの error は、まだ `Unknown` になることがある。ここは edge graph から近い文脈を辿る別 helper が必要。

## ChatGPT Review: ExpectedEdge Follow-up

- 現状の見立ては、ExpectedEdge 基盤と solver constraint 整合は 9割近く、型エラー診断利用は 6.5〜7割、runtime / demand 再推測削減は 4割弱。
- 直近優先は、diagnostic edge selection の安定化と context 表示改善。
  - scoring は TypeVar / effect TypeVar 近さを使う方向でよい。
  - tie-break として span match、reason match、kind priority、span length を入れて、同点選択を安定させる。
  - `error.pos/error.neg` の局所衝突だけでなく、edge の `actual_tv/expected_tv` から compact した contextual type も表示できるようにする。
- `RepresentationCoerce` と `CoerceEvidence` の対応テストは、単純な個数比較からもう少し強める。
  - 短期は representation edge の actual/expected bounds と core `CoerceEvidence` が具体的に出ることを確認する。
  - 中期は `ExpectedEdgeId` / `source_edge` のような対応 ID を検討する。
  - `ExpectedEdgeId` を追加し、`ExprKind::Coerce` から core `CoerceEvidence.source_edge` へ流すようにした。これで `RepresentationCoerce` edge と core evidence の対応をテストで直接確認できる。
- `complete_principal` に ExpectedEdge evidence を足すのが次の本丸。
  - 最初は runtime へ渡さず、debug / verbose / tests で edge kind、actual/expected bounds、effect actual/expected bounds、closed/open を見られる形にする。
  - `collect_expected_edge_evidence(state)` を export し、`--infer --verbose-ir` で `expected-edge-evidence:` として確認できるようにした。
  - 未閉じ evidence は diagnostic/debug 用に留め、runtime 利用は閉じたものから始める。
- act copy の `ExprKind::Coerce` は元の `ExpectedEdgeId` をコピーしない。コピー後は tv が別物になるので、当面は `edge_id: None` にして誤った `source_edge` リンクを避ける。
- `ExpectedEdgeEvidence` に `informative` を追加し、`closed` と「runtime/debug hint として中身があるか」を分けた。`--infer --verbose-ir` の evidence 表示にも出る。
- `ApplicationArgument` edge を通常 `ExprKind::App` と core `ApplyEvidence` へ接続した。`App` は `arg_edge_id` / `expected_arg_tv` を持ち、export 後は `ApplyEvidence.arg_source_edge` / `expected_arg` として見える。
- `ExpectedEdgeEvidence` に `runtime_usable` を追加した。value 側では `Never` / `Any` / `Var` を runtime hint として使わず、effect 側では `Never` を empty effect として使える扱いに分ける。
- type error の `from edge:` は局所的な `error.pos/error.neg` ではなく、選択された edge の coalesced actual/expected bounds と edge id/kind を出すようにした。
- act copy の `ExprKind::App` は元の `ApplicationArgument` edge id をコピーしないことをテストで固定した。`Coerce` と同じく、コピー後の tv と古い edge id がズレる誤リンクを避ける。
- `YULANG_USE_EXPECTED_ARG_EVIDENCE=1` の opt-in で、runtime lower が `ApplyEvidence.expected_arg` を引数 lowering の期待型候補として読めるようにした。通常経路は変えず、`YULANG_DEBUG_EXPECTED_ARG_EVIDENCE=1` で available / used / ignored-unusable の counters を出せる。
- `YULANG_COALESCE_APPLY_EVIDENCE=1` の apply evidence coalesce に `expected_arg_tv` を含めた。coalesced 経路では `callee / actual arg / expected arg / result` が同じ slot-local relation で整う。
- `ApplicationArgument` の source edge が `ExpectedEdgeEvidence` と `ApplyEvidence.expected_arg` の両方へつながることをテストで固定した。
- `ExpectedEdgeKind::ApplicationCallee` を追加した。apply lowering では callee 用の `expected_callee_tv` を作り、`callee.tv <= expected_callee_tv` を `ExpectedEdge` として記録する。core `ApplyEvidence` には `callee_source_edge` / `expected_callee` を追加し、runtime adapter event の `apply.lower-callee` から callee source edge を辿れるようにした。
- `YULANG_USE_EXPECTED_CALLEE_EVIDENCE=1` を追加し、monomorphize の apply parameter hint に `ApplyEvidence.expected_callee` の parameter slot を混ぜられるようにした。`--runtime-phase-timings` の `demand_evidence` に expected callee の present / converted / used / changed-param / same-param / rejected counters を出す。
- runtime adapter event から debug/profile 用の `ObservedAdapterEvidence` を作るようにした。runtime 実装上は `ThunkToValue` と `BindHere` が 2 event で出るが、observed evidence では semantic な `ForceThunkToValue` 1 件として畳み、`ExpectedAdapterEvidence` とは混ぜずに表示する。
- `DerivedExpectedEdgeEvidence` を core `PrincipalEvidence` に追加した。`--core-ir --verbose-ir` では derived expected edges を表示し、runtime timings では derived edge の kind / polarity counts と runtime adapter event の source edge が derived parent を持つかを数える。
- `core_ir::CoreProgram` に `PrincipalEvidence { expected_edges }` table を追加した。`ExpectedEdgeEvidence` は core IR 側にも保存され、`--core-ir --verbose-ir` では `principal-evidence:` として `source_edge` の参照先を読める。
- runtime lower は `PrincipalEvidence` を受け取り、`ApplyEvidence.arg_source_edge` から対応する `ExpectedEdgeEvidence.runtime_usable` を参照できるようにした。table が無い旧入口では従来通り bounds から保守的に判定する。
- runtime lower が `source_edge` 先の `ExpectedEdgeEvidence.runtime_usable=false` を尊重し、`ApplyEvidence.expected_arg` を使わないことをテストで固定した。
- runtime lower の `CoerceEvidence.source_edge` は、`PrincipalEvidence` に対応 edge がある場合、debug invariant として `RepresentationCoerce` kind を指すことを確認する。正しい table 付き coerce はテストで固定した。
- diagnostic 用の `DerivedExpectedEdgeEvidence` を追加した。まずは expected edge の actual/expected が record 同士のとき、共通 field を `RecordField` derived edge として派生する。`--infer --verbose-ir` では `derived-expected-edge-evidence:` として確認できる。
- `DerivedExpectedEdgeEvidence` は tuple item、variant payload、function param/return も派生するようにした。これで構造型 annotation などの expected edge から、より細かい diagnostic context を取り出せる。
- `DerivedExpectedEdgeEvidence` に polarity を持たせた。record / tuple / variant payload / function return は covariant、function param は contravariant として表示できる。
- derived edge は深さ制限付きで再帰的に派生するようにした。nested record / tuple / variant / function の内側 mismatch を diagnostic 用に取り出せる。
- CLI の infer type error context は、選んだ expected edge の子として一致する `DerivedExpectedEdgeEvidence` があれば `detail:` 行に出すようにした。nested record mismatch では `.a.b` のような path が見える。
- runtime lower の expected arg evidence profile は `present` / `converted` / `usable-by-table` / `usable-by-bounds` / `used-as-*` / `ignored-*` に分け、どこで evidence が落ちるかを見られるようにした。
- runtime lower は `PrincipalEvidence.expected_edges` を `id -> edge` の index にして持つようにした。`ApplyEvidence.arg_source_edge` と `CoerceEvidence.source_edge` の kind invariant はこの index 経由で確認する。
- `ExpectedAdapterEdge` / `ExpectedAdapterEdgeEvidence` の最小入口を追加した。まずは effect operation argument を観測対象にし、`ApplicationArgument` edge を source として value/effect の actual/expected bounds を `--infer --verbose-ir` で確認できる。
- `CoreProgram.evidence` に expected adapter edge table も載せるようにした。`--core-ir --verbose-ir` では principal evidence の adapter edges として表示できる。
- runtime lower 側にも `YULANG_DEBUG_RUNTIME_ADAPTERS=1` の profile を追加した。`value-to-thunk` / `thunk-to-value` / `bind-here` / `reused-thunk` / `forced-effect-thunk` を数え、ExpectedAdapterEdge がまだ直接届いていない runtime adapter 挿入点を観測できる。
- `catch` lowering で handler boundary の adapter evidence を置き始めた。handled effect がある `catch` は `HandlerResidual`、各 arm body の result join は source `CatchBranch` edge 付きの `HandlerReturn` として core evidence table まで運ぶ。
- continuation application は `ResumeArgument` adapter edge として記録するようにした。通常の `ApplicationArgument` source edge にリンクし、resume に渡す値/effect の actual/expected slot を core evidence table で見られる。
- `YULANG_USE_EXPECTED_ARG_EVIDENCE=1` のとき、monomorphize の apply evidence arg signature hint も閉じた `ApplyEvidence.expected_arg` を優先するようにした。runtime lower だけでなく DemandEmitter / checker 側の signature hint にも expected arg evidence が届く。
- `--runtime-phase-timings` に expected arg evidence profile と runtime adapter profile を統合した。env var の debug 出力を使わなくても、present / converted / runtime_usable / used / ignored と thunk / `BindHere` 挿入数を比較できる。
- `DemandQueueProfile` を追加し、`--runtime-phase-timings` に attempted / pushed / pushed_open / pushed_closed / skipped_duplicate / skipped_covered_by_closed を出すようにした。expected arg evidence が demand dedup や closed-cover に効いているかを見られる。
- expected arg evidence の unusable 理由を `ignored_table_open` / `ignored_table_uninformative` / `ignored_table_not_runtime_usable` / `ignored_bounds_unusable` に分けた。`examples/10_effect_handler.yu` では ignored_table_open が大半なので、次は edge evidence を閉じる/coalesce する方向が本筋。
- runtime lower の `ApplicationArgument` gate は edge 全体の `runtime_usable` ではなく、expected slot 単体の closed / informative / runtime type usable を見るようにした。actual 側が open でも expected arg が `int` のように閉じていれば利用できる。`examples/10_effect_handler.yu` は `usable_by_table` が 1 から 70 前後へ増え、`YULANG_USE_EXPECTED_ARG_EVIDENCE=1` では arg type hint に 25 回、lowering expected に 63 回使われる。ただし `mono_passes` / `specializations` はまだ 9 / 1 のままなので、次は demand key / specialization rewrite に実際に効く入口を探す。
- `--runtime-phase-timings` に `effective_passes`、pass ごとの progress、追加 binding path、DemandEvidence profile を追加した。`examples/10_effect_handler.yu` では opt-in ありで `expected_arg_used=244` まで行くが、`expected_arg_changed_signature=0` / `expected_arg_same_signature=244` なので、expected arg は demand signature を変えていない。追加 specialization は `listen__ddmono0` の 1 個だけで、残りは handler / adapter 側の形が支配している可能性が高い。
- `--runtime-phase-timings` に expected adapter evidence profile と specialization の target/signature 表示を追加した。`examples/10_effect_handler.yu` では expected adapter edge が total=76、handler_residual=11、handler_return=30、resume_argument=8 あるが runtime_usable=0 / closed=0。runtime adapter は value_to_thunk=3、thunk_to_value=14、bind_here=14 なのに、expected adapter evidence の value_to_thunk / thunk_to_value / bind_here はまだ 0。追加 specialization の正体は `listen__ddmono0 <= listen :: thunk[out]int -> str -> (int, str)`。
- runtime adapter profile を ApplyEvidence 由来で分けた。`examples/10_effect_handler.yu` では apply_evidence_thunk_to_value=10 / apply_evidence_bind_here=10、apply_evidence_value_to_thunk=0。つまり runtime の `BindHere` の多くは apply 境界で thunk を値へ戻すために入っているが、対応する expected adapter evidence はまだ 0。
- `ApplyEvidence.arg_source_edge` 由来の文脈を runtime adapter profile へ伝播した。`examples/10_effect_handler.yu` では apply_evidence_thunk_to_value=10 / apply_evidence_bind_here=10 のうち、arg source edge 文脈まで追えるものは 1 個だけ。残りは final apply argument の evidence ではなく、apply evidence context 内の別経路で発生している。
- runtime adapter profile に apply phase breakdown を追加した。`examples/10_effect_handler.yu` の baseline では apply_evidence_thunk_to_value=10 / apply_evidence_bind_here=10 の内訳が `apply_lower_callee=9`、`apply_lower_argument=1`、final argument / effect operation argument は 0。expected arg opt-in + apply coalesce では `apply_lower_callee=4`、`apply_prepare_final_argument=2`。したがって、この例の残り adapter は final argument edge より callee lowering 側の thunk/function shape に寄っている。
- runtime adapter event table を追加し、phase / owner / apply target / arg source edge / actual / expected を保存するようにした。`--runtime-phase-timings` では target 別集計を出す。`examples/10_effect_handler.yu` の baseline では `std::list::fold_impl`、`std::range::fold_from`、`f`、`std::prelude::Add::add` の callee lowering に `thunk-to-value` / `bind-here` が集中する。expected arg opt-in + apply coalesce では callee 側は `f` と `std::range::fold_from` に減り、`std::list::fold_impl` は final argument 側に移る。
- runtime adapter event summary に owner を追加し、`YULANG_TRACE_RUNTIME_ADAPTER_EVENTS=1` で actual / expected を詳細表示できるようにした。`examples/10_effect_handler.yu` の opt-in では、`std::range::fold_from` body 内の callee lowering が closed / partially-open thunked function を値関数へ戻しており、`std::list::fold_impl` body 内では callback `f` と fold_impl final argument で同種の adapter が出る。追加 specialization `listen__ddmono0` は直接の event target ではなく、handler/listen 側の demand が標準 fold/range helper の adapter を経由している形に見える。
- runtime adapter event と `ExpectedAdapterEvidence` の match rate を追加した。現状の `examples/10_effect_handler.yu` では baseline が matched=0 / unmatched=20、expected arg opt-in + apply coalesce が matched=0 / unmatched=12。unmatched はすべて `ThunkToValue` / `BindHere` なので、handler/resume 系の ExpectedAdapterEdge は実 adapter とまだ対応しておらず、次に backfill すべき候補は fold/range helper の callee / final-argument adapter 文脈。
- `SubstitutionSpecializeProfile` を pipeline profile に追加し、skip reason を target path ごとに集計するようにした。`--runtime-phase-timings` では `substitution-specialize` pass の下に `skip_target ... reasons=[...]` を出す。`examples/10_effect_handler.yu` + `YULANG_SUBST_SPECIALIZE=1` では `listen` が `skip-handler-binding=4`、`std::list::fold_impl` / `std::range::fold_from` / `std::range::fold_ints` が `skip-no-complete-substitution` に寄っており、次に必要なのは handler boundary evidence と fold/range helper の principal substitution 欠落を分けて見ること。
- `skip-no-complete-substitution` について、target ごとの missing type var も profile に出すようにした。`examples/10_effect_handler.yu` では `std::range::fold_ints` が `t1193/t1254`、`std::list::fold_impl` が `t1879/t1924`、`std::range::fold_from` が `t1306/t1355` を毎回欠いている。これで「どの helper が失敗したか」だけでなく「どの主型スロットが閉じていないか」を次に追える。
- `ObservedAdapterEvidence` の source expected edge coverage を追加した。`examples/10_effect_handler.yu` では observed adapter 10 件のすべてが source edge を持ち、9 件が `ApplicationCallee`、1 件が `ApplicationArgument` 由来だった。`source_with_derived_parent` は 7 件。runtime の `ForceThunkToValue` backfill は、apply argument より callee expected edge 側を主対象にすべきことが数字で確認できた。
- `SubstitutionSpecialize` が runtime 型から追加代入を推測した箇所を target ごとに profile するようにした。`examples/10_effect_handler.yu` では `infer_target` が出ないため、失敗の主因は追加推論ではなく initial evidence の欠落。`examples/07_junction.yu` では `std::list::fold_impl` が `infer-ret-structural-substitution=4` / `infer-arg-structural-substitution=2`、`std::fold::Fold::fold` が arg/ret structural に寄る。これらは `complete_principal` 側へ移すべき principal evidence 候補として扱う。
- `skip-no-complete-substitution` の原因を `no_complete_causes` として分けた。`examples/07_junction.yu` では `std::list::fold_impl` / `std::range::fold_from` が `instantiation-missing-vars`、`std::range::fold_ints` が `apply-evidence-missing-principal-callee`。したがって fold 系でも、instantiation の欠落補完と principal callee evidence の欠落は別問題として扱う。
- `YULANG_SUBST_SPECIALIZE=1` でも apply substitution evidence を export するようにした。`YULANG_COALESCE_APPLY_EVIDENCE=1` の早期 return でも principal evidence を落とさない。さらに substitution が空でも `principal_callee` は保持するようにした結果、`examples/07_junction.yu` の `std::range::fold_ints` は `apply-evidence-missing-principal-callee` ではなく `evidence-empty-substitutions` として分類できた。次は principal callee から fold accumulator/item の substitution を引けない理由を `complete_principal` 側で見る。
- 部分適用された callee からも residual principal scheme を作るようにした。`examples/07_junction.yu` の core IR では `fold_ints f` 以降の apply にも `principal=` が出る。ただし `std::range::fold_ints` の `evidence-empty-substitutions` は残るので、次は principal の伝播ではなく、callback/accumulator の expected edge または derived evidence から substitution を作る必要がある。
- `SubstitutionSpecialize` は apply spine 内の複数 `ApplyEvidence` から substitution 候補を集めるようにした。`examples/07_junction.yu` では `std::list::fold_impl` の runtime structural inference が少し減ったが、`std::range::fold_ints` はまだ `evidence-empty-substitutions`。残りは spine evidence の集約ではなく、callback/accumulator の slot-local relation 自体が principal substitution として閉じていない問題。
- `ApplyEvidence` に `substitution_candidates` を追加し、`complete_principal` で principal callee / arg / result slot の bounds から `PrincipalSubstitutionCandidate` を出す入口を作った。callee / arg 候補にはそれぞれ `callee_source_edge` / `arg_source_edge` を付け、verbose core IR で `@callee.param edge#...` や `@arg edge#...` として由来を見られる。runtime の `SubstitutionSpecialize` は spine 内の候補を集め、Exact 一致または Lower/Upper 同一 closed type がそろった場合だけ substitution として採用する。片側候補、衝突候補、open / Any / value Never は捨てる。
- 候補 solver の安全条件は unit test で固定した。Lower/Upper が同じ `int` なら bind し、Lower だけでは bind せず、Exact が `int` / `bool` で衝突する場合も bind しない。
- `examples/07_junction.yu` では `std::range::fold_ints` はまだ `evidence-empty-substitutions` のまま。つまり今回の候補生成は root の `junction::all/any` などでは見えるが、fold_ints の accumulator/item までは届いていない。次は global な arg/result bounds ではなく、`ApplicationArgument` / `ApplicationCallee` edge と `DerivedExpectedEdgeEvidence` を、特定の principal slot へ対応づけて candidate の `source_edge` / `path` として局所化する必要がある。
- `ApplicationArgument` / `ApplicationCallee` の source edge と、そこから派生した `DerivedExpectedEdgeEvidence` も principal substitution candidate の入力にした。closed ではない structural candidate も evidence として残し、solver 側だけが open candidate を無視する。これにより `examples/07_junction.yu` の `std::range::fold_ints` は `evidence-empty-substitutions=4` / `evidence-unsolved-candidates=4` まで分解できた。まだ高速化には効かないが、「候補すらない apply」と「open 候補止まりの apply」を分けられるようになった。
- `fold_ints f` の candidate は `t1193 <= t1193 | t1254 @callee.param.param edge#135` や `t1193 >= t1193 & t1254 @callee.param.return.return edge#135` のように、principal 変数同士の open relation が中心。現時点の solver はこれを bind しない。次は open candidate graph を spine 全体で正規化して closed candidate に伝播するか、あるいは `fold_ints` の accumulator `z/acc` から closed type が出ない理由を別に追う。
- `SubstitutionSpecialize` の skip target に `survives_final_prune` を表示するようにした。`examples/07_junction.yu` では `std::range::fold_ints`、`std::range::fold_from`、`std::list::fold_impl` の skip は最終 prune 後に残らない。つまりこの benchmark の `fold_ints` は support noise と見てよく、`t <= t | u` / `t >= t & u` 形の open candidate graph solver は保留する。range-specific な reachable example で `fold_ints` が残る場合は、open graph propagation ではなく full-spine principal candidate generation で accumulator/result slot から closed candidate を出す方向を優先する。
- `SubstitutionSpecialize` の skip reason を actionable / benign に分類した。`skip-non-generic-callee` と leaf specialization skip は benign とし、それ以外は evidence / adapter 改善の余地がある actionable として扱う。`examples/07_junction.yu` では `surviving_actionable_targets=0`、`surviving_benign_targets=4` になった。残る visible skip は `std::list::&impl#187::fold__mono2` の `skip-non-generic-callee` で、すでに mono 化された callee の再訪問なので追わない。runtime specialization はここで observable checkpoint として一旦畳み、次は diagnostics の regression snippet 収集へ移る。
- handler adapter は ExpectedEdge だけで足りなければ `ExpectedAdapterEdge` のような別種を考える。
  - `ThunkWrap` / `BindHere` / `HandlerAdapter` / `EffectResidual` の境界として扱う。
- `RecordField` / `VariantPayload` は lowering を bidirectional にせず、まず annotation edge などから派生する diagnostic 用 `DerivedExpectedEdge` として始めた。nominal constructor payload などの追加は、expected slot が見える場所から広げる。

## Current Checkpoint: ShapeTable / ShapedCore

Runtime specialization is parked at the observable checkpoint for now:

- `examples/07_junction.yu` has `surviving_actionable_targets=0`.
- The remaining surviving substitution-specialize skips are benign already-monomorphic callee revisits.
- `std::range::fold_ints` / `fold_from` / `std::list::fold_impl` do not survive final prune in that benchmark.
- Open candidate graph solving remains parked unless a surviving target proves it necessary.

The next direction is a non-behavior-changing shaped core layer. `CoreProgram`
now gets a `ShapeTable` / `CoreShapeProfile` pass before runtime lowering. The
first pass records expression traversal paths and detailed apply shape slots
from existing `ApplyEvidence`, without changing runtime lowering,
monomorphization, VM output, or diagnostics.

Short-term goal:

- Keep expanding shape coverage as an evidence ledger for diagnostics and
  specialization.
- Prefer adding slot-local shape/evidence records over strengthening runtime
  recovery heuristics.
- Use `--runtime-phase-timings` `core_shape:` output to decide where evidence is
  missing before changing behavior.

## Direction Guardrail: One-Pass Typed IR

The long-term direction is still to build a typed IR with as little looping and
runtime rediscovery as possible.

The recent evidence / shape work is on that path only if it moves information
from later recovery passes into earlier, explicit records:

```text
infer/lower:
  place expected/coerce/adapter boundaries

complete_principal:
  export slot-local expression shape and principal evidence

runtime lower:
  consume shape/evidence instead of rediscovering types and adapters

monomorphize:
  use principal evidence instead of demand/fixpoint recovery where possible
```

Use this as the main test for future changes:

```text
Does this change move a type/adapter decision from a later heuristic loop into
complete_principal / ShapeTable / explicit evidence?
```

If yes, it is probably on the main line.
If it only adds profiling, strengthens runtime heuristics, solves open candidate
graphs globally, or special-cases std helpers without reducing later recovery,
it is likely sideways.

`ShapeTable` is not the goal by itself. It is the smallest checkpoint toward a
shaped core where every expression has intrinsic/contextual value/effect shape,
principal instantiation data, and adapter/coercion boundary information that
runtime can eventually trust.

## Current Slice: CoreShape Explanations and First Call Diagnostic Context

`CoreShape` now records apply owner / target / callee head and missing reasons
without changing runtime behavior. `YULANG_DEBUG_CORE_SHAPES=1` prints grouped
missing/partial apply reasons by target; `YULANG_TRACE_CORE_SHAPES=1` is required
for the full per-apply dump.

This is meant to answer:

```text
which apply target is partial, and why?
```

The first user-facing diagnostic context is also attached to runtime type
mismatches in apply lowering. For `1 + true`, the message now includes the
surface call label:

```text
result type mismatch in call to `+`: expected bool -> bool, got int -> int
```

This is still not final source-span diagnostics. The next diagnostics step is to
carry source ranges from expected/source edges into core evidence, then use those
ranges for code frames.

## Current Slice: Source Ranges in Principal Evidence

Expected edge and expected adapter edge evidence now carry byte source ranges
through core IR:

```text
ConstraintCause.span
  -> complete_principal ExpectedEdgeEvidence / ExpectedAdapterEdgeEvidence
  -> core_ir::PrincipalEvidence
  -> --infer/--core-ir --verbose-ir source-range=START..END
```

This is still non-behavior-changing plumbing. Runtime diagnostics do not render
code frames yet, but an apply mismatch that has an `arg_source_edge` or
`callee_source_edge` can now resolve that edge back to a source byte range in
`CoreProgram.evidence`.

Next diagnostic step:

- Use the source edge on apply mismatch context to look up the matching expected
  edge evidence.
- Convert the stored byte range into a line/column frame in the CLI.
- Keep the fallback message useful when no source edge or range is available.

The CLI now has the first source-frame bridge for runtime type mismatches:

```text
RuntimeError::TypeMismatch.context.{arg_source_edge,callee_source_edge}
  -> CoreProgram.evidence.expected_edge(id).source_range
  -> one-line source frame
```

This only renders when the runtime mismatch carries a source edge whose expected
edge evidence has a range. The current `1 + true` runtime error still lacks a
frame because that root operator apply reaches runtime lowering without apply
evidence/source edge. Next step is to preserve or synthesize source-edge-backed
apply shape for that root/operator case, rather than adding a broad fallback
frame that may point at the wrong source.
