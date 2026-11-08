# Cycle 3 新規定理の型と日本語の主張

2026-11-08。対象は新規9モジュールと `lean/Main.lean`。実際のソースの theorem 宣言から型を抽出した。各項目のコードは証明本体を除いた宣言型であり、括弧内の引数・前提はすべて全称量化される。省略可能な暗黙引数 `n : Nat` も任意であり、特に固定値を仮定しない。コード中の `:=` 以降の証明は掲載しない。

## 共通記法と適用範囲

- 完全名は `Yulang.<節のモジュール名>.<定理名>`。Main も `Yulang.Main`。
- `State n` は n 個の occurrence slot に対する ordinary 制約状態。`All ... values s.atoms` は全制約の充足、`s.Models` はそれを満たす values の存在。`Comp` は型と効果を含む計算型。型に関する `Equivalent` は効果の等しさを要求しない。
- `extend s slot .str` は slot の型を str と等置する制約を追加する。IndexPath の `expected outputs s` は全 outputs に同制約を追加した状態。旧制約は残す。
- `Evidence` は ordinary 制約にある基底型の上下の証拠。`detect` と `materialize` はその実計算。
- SourceDescent の `Table` は source 名の有限 occurrence リスト、`Slot table = Fin table.length`。`Coherent` は同じ source 名の occurrence の型が同値であること。`Factors` は全 slot の型が sourceValues(source(slot)) と同値であること。
- Sweep の `Produced` は materialized receiver と実関連宣言の Computed から独立に定義。`Step` の失敗枝も Produced の不存在で定義。`Runs` はこの Step の有限列。
- ParentExample の固定環境は Parent(box a) where Left a, Right a、Left str、Right str。Right str に関連型 value=str。逆順2辺を2回走査する。中間 Index 宣言の環境は別で、全宣言を単一 registry に統合した定理ではない。
- PathComplete/PathParent/NamedPath の seed は固定 Index(box str,int) の関連型。有限 path は入力データであり、一般 source program から生成した child graph ではない。NamedPath の seed と names は Nat の識別名で、任意の seed 型ではない。
- 各 outer_exact の Final は実 run を呼び出さず、明示した制約状態・モデル（該当する場合）・str 引数・独立 Dictionary の存在で定義する。有限断片の成功 exactness であり、一般 B4 の飽和停止・四方向分類・parser/lowering・全 source graph を証明したものではない。

## CommonRoleSourceDescent

### `representative_source`

代表探索が slot を返したなら、その slot の source 名は探索した name と等しい。

```lean
theorem representative_source (table : Table) (name : Nat) (slot : Slot table)
    (found : representative table name = some slot) : source table slot = name
```

### `representative_exists`

任意の実在 occurrence slot の source 名には、探索で返される代表 first が存在する。

```lean
theorem representative_exists (table : Table) (slot : Slot table) :
    ∃ first, representative table (source table slot) = some first
```

### `descend_factors`

任意の fallback 型について、occurrence 評価 values が Coherent なら、代表から計算した descend を通じて全 slot の型が因子化する。

```lean
theorem descend_factors (table : Table) (values : Slot table → Comp Common.model)
    (fallback : Common.Ty) (coherent : Coherent table values) :
    Factors table values (descend table values fallback)
```

### `factors_coherent`

sourceValues を通じた Factors があれば values は Coherent である。

```lean
theorem factors_coherent (table : Table) (values : Slot table → Comp Common.model)
    (sourceValues : Nat → Common.Ty) (factor : Factors table values sourceValues) :
    Coherent table values
```

### `factorization_exact`

values が Coherent であることと、全 occurrence の型を因子化する sourceValues が存在することは同値。

```lean
theorem factorization_exact (table : Table) (values : Slot table → Comp Common.model) :
    Coherent table values ↔ ∃ sourceValues, Factors table values sourceValues
```

### `atoms_factorization_exact`

生成した source identity atoms を values が満たすことと、sourceValues による型の因子化が存在することは同値。

```lean
theorem atoms_factorization_exact (table : Table) (values : Slot table → Comp Common.model) :
    PresenceNormalForm.All Common.model values (atoms table) ↔
      ∃ sourceValues, Factors table values sourceValues
```

### `fallback_independent`

任意の二つの fallback 型 a,b と実在 slot について、その source 名での descend の値は等しい。coherence は前提に不要。

```lean
theorem fallback_independent (table : Table) (values : Slot table → Comp Common.model)
    (a b : Common.Ty) (slot : Slot table) :
    descend table values a (source table slot) = descend table values b (source table slot)
```

### `solver_factorization_exact`

任意の旧 state について、identity 制約拡張後の実 consistent が true である iff 旧制約を満たす occurrence 評価 values と、その型を因子化する sourceValues が存在する。

```lean
theorem solver_factorization_exact (table : Table)
    (state : CommonRoleSettledConstraints.State table.length) :
    CommonRoleOpenPropagation.consistent (extend table state) = true ↔
      ∃ values : Slot table → Comp Common.model,
        PresenceNormalForm.All Common.model values state.atoms ∧
        ∃ sourceValues, Factors table values sourceValues
```

### `factor_unique_on_occurrence`

同じ values を因子化する二つの source 評価 left,right は、任意の実在 slot の source 名で型同値になる。

```lean
theorem factor_unique_on_occurrence (table : Table)
    (values : Slot table → Comp Common.model) (left right : Nat → Common.Ty)
    (hl : Factors table values left) (hr : Factors table values right)
    (slot : Slot table) :
    Common.Equivalent (left (source table slot)) (right (source table slot))
```

### `source_equation_exact`

coherent な values、任意の fallback,target、実在 slot について、descend した source 型が target と同値 iff 同じ source 名の全 other occurrence の型が target と同値。

```lean
theorem source_equation_exact (table : Table)
    (values : Slot table → Comp Common.model) (fallback target : Common.Ty)
    (coherent : Coherent table values) (slot : Slot table) :
    Common.Equivalent (descend table values fallback (source table slot)) target ↔
      ∀ other, source table other = source table slot →
        Common.Equivalent (values other).1 target
```

## CommonRoleStatefulIndexSweep

### `produced_exact`

実 produceIndex が out を返す iff materialize した receiver と実関連宣言の Computed を用いた独立 Produced が out を導く。

```lean
theorem produced_exact (s : State n) (edge : Edge n) (out : State n) :
    produceIndex s edge.receiver edge.output = some out ↔ Produced s edge out
```

### `visit_exact`

実 visit の結果が (done,out) iff 独立 Step。false の場合は Produced を満たす next が存在せず状態不変、true の場合は Produced が成り立つ。

```lean
theorem visit_exact (s : State n) (edge : Edge n) (done : Bool) (out : State n) :
    visit s edge = (done, out) ↔ Step s edge done out
```

### `sweep_exact`

任意の有限 edges、開始状態 s、trace、out について、実 sweep の結果が (trace,out) iff Step をつないだ独立 Runs。

```lean
theorem sweep_exact (edges : List (Edge n)) (s : State n) (trace : List Bool) (out : State n) :
    sweep edges s = (trace, out) ↔ Runs edges s trace out
```

### `visit_preserves`

visit 後の制約を満たす任意の assignment は旧 s の制約も満たす。

```lean
theorem visit_preserves (s : State n) (edge : Edge n)
    (assignment : Fin n → Comp Common.model)
    (model : All Common.model assignment (visit s edge).2.atoms) :
    All Common.model assignment s.atoms
```

### `sweep_preserves`

有限 sweep 後の制約を満たす任意の assignment は旧 s の制約も満たす。

```lean
theorem sweep_preserves (edges : List (Edge n)) (s : State n)
    (assignment : Fin n → Comp Common.model)
    (model : All Common.model assignment (sweep edges s).2.atoms) :
    All Common.model assignment s.atoms
```

## CommonRoleStatefulIndexPath

### `detect_of_str_evidence`

定数 pure str 評価 strAssignment が s を満たし、slot に str の Evidence があるなら、detect は some str を返す。

```lean
theorem detect_of_str_evidence (s : State n) (slot : Fin n)
    (model : All Common.model strAssignment s.atoms)
    (evidence : Evidence s.atoms slot .str) : detect s.atoms slot = some .str
```

### `extend_str_model`

strAssignment が s を満たすなら、任意の slot を str に等置する拡張も同じ評価が満たす。

```lean
theorem extend_str_model (s : State n) (slot : Fin n)
    (model : All Common.model strAssignment s.atoms) :
    All Common.model strAssignment (extend s slot .str).atoms
```

### `extended_detected`

strAssignment が s を満たすなら、slot=str の拡張後にその slot の detect は some str。

```lean
theorem extended_detected (s : State n) (slot : Fin n)
    (model : All Common.model strAssignment s.atoms) :
    detect (extend s slot .str).atoms slot = some .str
```

### `run_expected`

任意の有限 outputs、receiver、s について、strAssignment が s を満たし receiver の detect が some str なら、実 run は expected outputs s を返す。

```lean
theorem run_expected (outputs : List (Fin n)) (receiver : Fin n) (s : State n)
    (model : All Common.model strAssignment s.atoms)
    (known : detect s.atoms receiver = some .str) :
    run outputs receiver s = some (expected outputs s)
```

### `expected_models`

任意の assignment が expected outputs s を満たす iff 旧 s を満たし、outputs 中の全 output の型が str と同値。

```lean
theorem expected_models (outputs : List (Fin n)) (s : State n)
    (assignment : Fin n → Comp Common.model) :
    All Common.model assignment (expected outputs s).atoms ↔
      All Common.model assignment s.atoms ∧
      ∀ output ∈ outputs, Common.Equivalent (assignment output).1 (.base .str)
```

### `expected_idempotent_models`

任意の assignment について、同じ outputs による expected を二回適用した状態と一回適用した状態のモデル性は同値。成功の前提は不要。atom 列の等しさではない。

```lean
theorem expected_idempotent_models (outputs : List (Fin n)) (s : State n)
    (assignment : Fin n → Comp Common.model) :
    All Common.model assignment (expected outputs (expected outputs s)).atoms ↔
      All Common.model assignment (expected outputs s).atoms
```

### `from_declaration_exact`

任意の receiver と有限 outputs について、空状態から実 Index(box str) 関連宣言を seed とする fromDeclaration は expected outputs (extend empty receiver str) を返す。外部成功前提なし。

```lean
theorem from_declaration_exact (receiver : Fin n) (outputs : List (Fin n)) :
    fromDeclaration receiver outputs =
      some (expected outputs (extend State.empty receiver .str))
```

## CommonRoleStatefulParentExample

### `declarations_checked`

固定 visible=[parent,left,right] に対する実宣言 checkDatabase は true。

```lean
theorem declarations_checked : CheckedRoles.checkDatabase visible = true
```

### `declarations_wellFormed`

固定 visible は Roles.WellFormed。

```lean
theorem declarations_wellFormed : Roles.WellFormed visible
```

### `assoc_wellFormed`

固定関連型環境 assocEnvironment.cores は Roles.WellFormed。

```lean
theorem assoc_wellFormed : Roles.WellFormed assocEnvironment.cores
```

### `associated_checked`

固定関連型環境と assocRoles は AssocWellFormed。

```lean
theorem associated_checked : Roles.AssocWellFormed assocEnvironment assocRoles
```

### `right_resolved`

固定 Right str goal は実 resolve で resolved。

```lean
theorem right_resolved : Roles.resolve assocEnvironment.cores assoc_wellFormed rightGoal = .resolved
```

### `right_value`

固定 Right str の関連型番号0を assocOf すると some str が得られる。

```lean
theorem right_value : Roles.assocOf assocEnvironment assocRoles assoc_wellFormed rightGoal 0 =
    some Roles.Examples.str
```

### `seed_from_declaration`

固定 Right str の実関連宣言から seed を計算すると some s0。

```lean
theorem seed_from_declaration : seed = some s0
```

### `first_pending`

s0 の slot1 は未 materialize なので Index の辺1→2は none。これは最終言語分類の pending 定理ではない。

```lean
theorem first_pending : produceIndex s0 (1 : Fin 3) (2 : Fin 3) = none
```

### `first_sweep`

逆順 edges=[1→2,0→1] の第一 sweep は trace=[false,true] と s1 を返す。

```lean
theorem first_sweep : sweep reverseEdges s0 = ([false, true], s1)
```

### `second_sweep`

同じ edges の第二 sweep は trace=[true,true] と s3 を返す。

```lean
theorem second_sweep : sweep reverseEdges s1 = ([true, true], s3)
```

### `final_materialized`

s3 の slot2 は実 materialize で str。

```lean
theorem final_materialized : materialize s3.atoms (2 : Fin 3) = some Roles.Examples.str
```

### `final_models`

任意の3-slot assignment について、s3 を満たす iff slot0,1,2 の型が全て str と同値。

```lean
theorem final_models (assignment : Fin 3 → Comp Common.model) :
    All Common.model assignment s3.atoms ↔
      Common.Equivalent (assignment (0 : Fin 3)).1 (.base .str) ∧
      Common.Equivalent (assignment (1 : Fin 3)).1 (.base .str) ∧
      Common.Equivalent (assignment (2 : Fin 3)).1 (.base .str)
```

### `final_consistent`

実 ordinary consistent は s3 に対して true。

```lean
theorem final_consistent : CommonRoleOpenPropagation.consistent s3 = true
```

### `parent_str_resolved`

固定 visible において Parent(box str) は実 resolve で resolved。Parent の where は Left a と Right a で同じ a。

```lean
theorem parent_str_resolved : Roles.resolve visible declarations_wellFormed
    (parentGoal Roles.Examples.str) = .resolved
```

### `run_value`

固定実入口 run は s3、str、および Parent(box str) の実 elaborate 結果を返す。

```lean
theorem run_value : run = some (s3, Roles.Examples.str,
    RoleDictionaries.elaborate visible declarations_wellFormed
      (parentGoal Roles.Examples.str))
```

### `outer_exact`

任意の out,argument,answer について、固定 run がそれらを返す iff out=s3、argument=str、独立 Dictionary の消去が answer=resolved であるという Final。外部成功前提なし。

```lean
theorem outer_exact (out : State 3) (argument : Roles.Term)
    (answer : RoleDictionaries.Answer) : run = some (out, argument, answer) ↔
      Final out argument answer
```

### `resolved_visible`

固定 run の resolved plan が存在し、plan.declarations 中の全 implementation は visible に属する。

```lean
theorem resolved_visible : ∃ plan, run = some (s3, Roles.Examples.str, .resolved plan) ∧
    ∀ implementation ∈ plan.declarations, implementation ∈ visible
```

## CommonRoleStatefulPathComplete

### `detect_of_models`

s にモデルが存在し、slot=str の Evidence があるなら、detect は some str。定数評価に限定しない。

```lean
theorem detect_of_models (s : State n) (slot : Fin n) (models : s.Models)
    (evidence : Evidence s.atoms slot .str) : detect s.atoms slot = some .str
```

### `extension_evidence`

任意の s,slot について extend s slot str にはその slot=str の Evidence がある。

```lean
theorem extension_evidence (s : State n) (slot : Fin n) :
    Evidence (extend s slot .str).atoms slot .str
```

### `path_preserves`

実有限 path run が out を返し assignment が out を満たすなら、同じ assignment は旧 s を満たす。

```lean
theorem path_preserves (outputs : List (Fin n)) (receiver : Fin n) (s out : State n)
    (result : run outputs receiver s = some out)
    (assignment : Fin n → Comp Common.model)
    (model : All Common.model assignment out.atoms) :
    All Common.model assignment s.atoms
```

### `run_expected_of_models`

expected outputs s にモデルが存在し、開始 receiver=str の Evidence があるなら、実 run は expected outputs s を返す。

```lean
theorem run_expected_of_models (outputs : List (Fin n)) (receiver : Fin n) (s : State n)
    (models : (expected outputs s).Models)
    (evidence : Evidence s.atoms receiver .str) :
    run outputs receiver s = some (expected outputs s)
```

### `successful_state`

実 run が out を返し、out にモデルが存在し、開始 receiver=str の Evidence があるなら、out は expected outputs s に等しい。

```lean
theorem successful_state (outputs : List (Fin n)) (receiver : Fin n) (s out : State n)
    (result : run outputs receiver s = some out) (models : out.Models)
    (evidence : Evidence s.atoms receiver .str) : out = expected outputs s
```

### `seed_exact`

任意の receiver と任意の旧 s に対し、実 Index(box str) 宣言からの seed は extend s receiver str を返す。

```lean
theorem seed_exact (receiver : Fin n) (s : State n) : seed receiver s = some (extend s receiver .str)
```

### `checked_exact`

任意の outputs,receiver,s,out について checkedRun が out を返す iff out=expected outputs (extend s receiver str) かつ out にモデルが存在する。モデル・成功は iff 全体の外部前提ではない。

```lean
theorem checked_exact (outputs : List (Fin n)) (receiver : Fin n) (s out : State n) :
    checkedRun outputs receiver s = some out ↔
      out = expected outputs (extend s receiver .str) ∧ out.Models
```

### `checked_models_exact`

任意の outputs,receiver,s について checkedRun の成功結果が存在する iff 旧 s を満たし、receiver と outputs 中の全 slot の型を str と同値にする assignment が存在する。

```lean
theorem checked_models_exact (outputs : List (Fin n)) (receiver : Fin n) (s : State n) :
    (∃ out, checkedRun outputs receiver s = some out) ↔
      ∃ assignment : Fin n → Comp Common.model,
        All Common.model assignment s.atoms ∧
        Common.Equivalent (assignment receiver).1 (.base .str) ∧
        ∀ output ∈ outputs, Common.Equivalent (assignment output).1 (.base .str)
```

## CommonRoleStatefulPathParent

### `final_evidence`

開始 s に receiver=str の Evidence があれば、expected outputs s の lastSlot にも str の Evidence がある。

```lean
theorem final_evidence (outputs : List (Fin n)) (receiver : Fin n) (s : State n)
    (evidence : Evidence s.atoms receiver .str) :
    Evidence (expected outputs s).atoms (lastSlot outputs receiver) .str
```

### `final_materialized`

expected outputs (extend s receiver str) にモデルが存在すれば、その lastSlot を materialize すると str。

```lean
theorem final_materialized (outputs : List (Fin n)) (receiver : Fin n) (s : State n)
    (models : (expected outputs (extend s receiver .str)).Models) :
    materialize (expected outputs (extend s receiver .str)).atoms (lastSlot outputs receiver) =
      some Roles.Examples.str
```

### `run_of_models`

expected outputs (extend s receiver str) にモデルが存在すれば、実 run はその expected 状態、str、Parent(box str) の実 elaborate 結果を返す。

```lean
theorem run_of_models (outputs : List (Fin n)) (receiver : Fin n) (s : State n)
    (models : (expected outputs (extend s receiver .str)).Models) :
    run outputs receiver s = some (expected outputs (extend s receiver .str), Roles.Examples.str,
      RoleDictionaries.elaborate visible declarations_wellFormed (parentGoal Roles.Examples.str))
```

### `outer_exact`

任意の有限 outputs,receiver,旧 s,out,argument,answer について、実 run の成功 iff 独立 Final。Final は out=expected、out.Models、argument=str、Parent(box str) の独立辞書の存在と消去結果を要求する。外部成功・モデル・fuel 前提なし。

```lean
theorem outer_exact (outputs : List (Fin n)) (receiver : Fin n) (s out : State n)
    (argument : Roles.Term) (answer : RoleDictionaries.Answer) :
    run outputs receiver s = some (out, argument, answer) ↔
      Final outputs receiver s out argument answer
```

### `success_visible`

任意の実 run の成功結果について resolved plan が存在し、answer はその plan の resolved、全 plan 宣言は固定 visible に含まれる。

```lean
theorem success_visible (outputs : List (Fin n)) (receiver : Fin n) (s out : State n)
    (argument : Roles.Term) (answer : RoleDictionaries.Answer)
    (result : run outputs receiver s = some (out, argument, answer)) :
    ∃ plan, answer = .resolved plan ∧
      ∀ implementation ∈ plan.declarations, implementation ∈ visible
```

## CommonRoleNamedPath

### `output_exact`

任意の seed,names とその table の slot について、slot が計算済み outputs に属する iff slot.val≠0。

```lean
theorem output_exact (seed : Nat) (names : List Nat) (slot : Slot (table seed names)) :
    slot ∈ outputs seed names ↔ slot.val ≠ 0
```

### `slot_covered`

任意の seed,names,slot について slot は receiver そのものか、計算済み outputs の要素。

```lean
theorem slot_covered (seed : Nat) (names : List Nat) (slot : Slot (table seed names)) :
    slot = receiver seed names ∨ slot ∈ outputs seed names
```

### `seed_identity`

任意の seed,names について計算した receiver の source 名は seed。

```lean
theorem seed_identity (seed : Nat) (names : List Nat) :
    CommonRoleSourceIdentity.source (table seed names) (receiver seed names) = seed
```

### `expected_models`

任意の seed,names,旧 s,values について expected の全 atoms を満たす iff 旧 s を満たし、table 上で Coherent、かつ全 slot の型が str と同値。

```lean
theorem expected_models (seed : Nat) (names : List Nat) (s : State (table seed names).length)
    (values : Slot (table seed names) → Comp Common.model) :
    All Common.model values (expected seed names s).atoms ↔
      All Common.model values s.atoms ∧ Coherent (table seed names) values ∧
        ∀ slot, Common.Equivalent (values slot).1 (.base .str)
```

### `outer_exact`

任意の seed,names,旧 s,out,argument,answer について、slot と同一性制約を入口で計算する実 run の成功 iff 独立 Final。Final は expected 状態、モデル存在、str 引数、実 Parent goal の独立辞書を要求する。

```lean
theorem outer_exact (seed : Nat) (names : List Nat) (s out : State (table seed names).length)
    (argument : Roles.Term) (answer : RoleDictionaries.Answer) :
    run seed names s = some (out, argument, answer) ↔ Final seed names s out argument answer
```

### `source_factorization`

任意の seed,names,s,out,argument,answer について実 run が成功し、任意の values が out を満たすなら、その values は旧 s を満たす。また values を型同値で因子化し、使用された全 source 名に str 同値の型を与える sourceValues が存在する。

```lean
theorem source_factorization (seed : Nat) (names : List Nat)
    (s out : State (table seed names).length) (argument : Roles.Term)
    (answer : RoleDictionaries.Answer) (result : run seed names s = some (out, argument, answer))
    (values : Slot (table seed names) → Comp Common.model)
    (model : All Common.model values out.atoms) :
    All Common.model values s.atoms ∧
      ∃ sourceValues, CommonRoleSourceDescent.Factors (table seed names) values sourceValues ∧
        ∀ slot, Common.Equivalent (sourceValues (CommonRoleSourceIdentity.source (table seed names) slot))
          (.base .str)
```

### `success_domain`

任意の seed,names,旧 s について実 run の成功結果が存在する iff 旧 s を満たし全 slot の型が str と同値になる values が存在する。旧効果制約を消さない。

```lean
theorem success_domain (seed : Nat) (names : List Nat) (s : State (table seed names).length) :
    (∃ out argument answer, run seed names s = some (out, argument, answer)) ↔
      ∃ values : Slot (table seed names) → Comp Common.model,
        All Common.model values s.atoms ∧
        ∀ slot, Common.Equivalent (values slot).1 (.base .str)
```

### `empty_success`

任意の seed と有限 names について空 ordinary state からの実 run は成功結果を持つ。同名の重複も許す。

```lean
theorem empty_success (seed : Nat) (names : List Nat) :
    ∃ out argument answer, run seed names (State.empty) = some (out, argument, answer)
```

### `rejects_inconsistent`

任意の seed,names,旧 s について s にモデルが存在しなければ、実 run は none。

```lean
theorem rejects_inconsistent (seed : Nat) (names : List Nat)
    (s : State (table seed names).length) (bad : ¬ s.Models) : run seed names s = none
```

## Main

前半8定理は既存定理の昇格・再掲であり、対象 carrier、量化子、外部前提を維持する。後半3定理は今回の有限動的断片への公開入口。`OpenPassSemanticStabilization` は全 n,registry,allocate,q,s に対し ∃k, ∀assignment, k回後とk+1回後のモデル性が同値、という定義。

### `settled_role_exact`

任意の n、checked registry、settled request q、四方向 result について、実 classify の結果=result iff 独立 Classify。request 型が等しい上下端点の断片を制限する。元定理の型・前提を維持した昇格。

```lean
theorem settled_role_exact (registry : CommonRoleSettledFrontier.Registry)
    (q : CommonRoleSettledFrontier.Request n) (result : CommonRoleOutermostResolver.Result) :
    CommonRoleSettledResolver.classify registry q = result ↔
      CommonRoleOutermostResolver.Classify
        (CommonRoleSettledFrontier.Local registry.declarations) q result
```

### `settled_role_accessible`

任意の n、checked registry、settled q に対し実局所 Child 関係は q で Acc。外部 rank/Acc を要求しない。元定理の型・前提を維持した昇格。

```lean
theorem settled_role_accessible (registry : CommonRoleSettledFrontier.Registry)
    (q : CommonRoleSettledFrontier.Request n) :
    Acc (CommonRoleOutermostResolver.Child
      (CommonRoleSettledFrontier.Local registry.declarations)) q
```

### `open_pass_exact`

任意の n、checked registry、外部 Allocation n、q,s,trace,final について実一回 run の結果 iff 独立 Runs。Allocation は外部入力のまま。元定理の型・前提を維持した昇格。

```lean
theorem open_pass_exact (registry : CommonRoleOpenProducer.Registry)
    (allocate : CommonRoleOpenPropagation.Allocation n)
    (q : CommonRoleOpenProducer.Request) (s : CommonRoleSettledConstraints.State n)
    (trace : CommonRoleOpenRecursivePass.Trace) (final : CommonRoleSettledConstraints.State n) :
    CommonRoleOpenRecursivePass.run registry allocate q s = (trace, final) ↔
      CommonRoleOpenRecursivePass.Runs registry.declarations allocate q s trace final
```

### `declaration_variance_registry_exact`

任意の Index,Formal 型と各 DecidableEq、program,pool,headers,result に対し実 registry=result iff RegistryJudgment program headers result。元定理の型・前提を維持した昇格。

```lean
theorem declaration_variance_registry_exact {Index Formal : Type}
    [DecidableEq Index] [DecidableEq Formal]
    (program : CommonDeclarationVarianceSyntax.Program Index Formal)
    (pool : CommonDeclarationVarianceOccurrences.Universe Index Formal)
    (headers : List (CommonDeclarationVarianceLowering.Header Formal))
    (result : CommonDeclaredNominalInspection.Registry) :
    CommonDeclarationVarianceRegistry.registry program pool headers = result ↔
      CommonDeclarationVarianceRegistry.RegistryJudgment program headers result
```

### `checked_cast_cost_bound`

任意の n、Plan n、check=true の accepted、node,cost、Run plan node cost の execution に対し cost≤budget plan accepted node。受理と実行導出の前提を除去していない。元定理の型・前提を維持した昇格。

```lean
theorem checked_cast_cost_bound (plan : CommonDeclaredCastCostGraph.Plan n)
    (accepted : CommonDeclaredCastCostGraph.check plan = true)
    (node : Fin n) (cost : Nat) (execution : CommonDeclaredCastCost.Run plan node cost) :
    cost ≤ CommonDeclaredCastCost.budget plan accepted node
```

### `optional_source_x22`

固定 arms の生成制約は固定 assignment で成立し、固定 absent program は80を返し、全整数 port の present program はその port を返す。元定理の型・前提を維持した昇格。

```lean
theorem optional_source_x22 :
    (CommonSourceArmsSolved.principal [] CommonSourceOptionalX22.arms).Holds Common.model
      CommonSourceOptionalX22.assignment ∧
    (ScopedCaseDataProgram.eval Empty.elim [] CommonSourceOptionalX22.absentProgram).result =
      .ok (some (.literal (.int 80))) ∧
    (∀ port : Int,
      (ScopedCaseDataProgram.eval Empty.elim [] (CommonSourceOptionalX22.presentProgram port)).result =
        .ok (some (.literal (.int port))))
```

### `current_core_principal`

任意の現存 Core.Required.Term expression と Common 計算型 result について、空環境の Core.Typing iff 実 infer が返す scheme とその unrestricted Parameters が存在し instantiate≤result。現存 model の定理であり新版 B6 完成ではない。元定理の型・前提を維持した昇格。

```lean
theorem current_core_principal (expression : Core.Required.Term)
    (result : Core.PresenceGeneration.Comp Common.model) :
    Core.Typing (Core.CommonSyntax.model Common.model) [] expression result ↔
      ∃ scheme ∈ Core.infer expression, ∃ parameters : scheme.Parameters,
        Core.PresenceGeneration.Comp.le Common.model (scheme.instantiate parameters) result
```

### `open_pass_stabilizes`

任意の n、checked registry、外部 Allocation、q,s に対し有限反復回数 k が存在し、k 回後と k+1 回後は任意の assignment に対して同じモデルを持つ。証明は k=1。固定 structural producer の意味安定性のみ。既存意味冪等定理を同じ範囲で昇格。

```lean
theorem open_pass_stabilizes : OpenPassSemanticStabilization
```

### `stateful_finite_path_parent_exact`

任意の n,有限 outputs,receiver,s,out,argument,answer について PathParent の実 run の成功 iff 同モジュールの独立 Final。上記 PathParent.outer_exact と同じ量化子・前提。

```lean
theorem stateful_finite_path_parent_exact (outputs : List (Fin n)) (receiver : Fin n)
    (s out : CommonRoleSettledConstraints.State n) (argument : Roles.Term)
    (answer : RoleDictionaries.Answer) :
    CommonRoleStatefulPathParent.run outputs receiver s = some (out, argument, answer) ↔
      CommonRoleStatefulPathParent.Final outputs receiver s out argument answer
```

### `stateful_reverse_siblings_exact`

任意の3-slot out,argument,answer について固定逆順兄弟例の実 run の成功 iff 同例の独立 Final。上記 ParentExample.outer_exact と同じ量化子・前提。

```lean
theorem stateful_reverse_siblings_exact (out : CommonRoleSettledConstraints.State 3)
    (argument : Roles.Term) (answer : RoleDictionaries.Answer) :
    CommonRoleStatefulParentExample.run = some (out, argument, answer) ↔
      CommonRoleStatefulParentExample.Final out argument answer
```

### `named_finite_path_exact`

任意の seed,names,それに対応する s,out,argument,answer について NamedPath の実 run の成功 iff 同モジュールの独立 Final。上記 NamedPath.outer_exact と同じ量化子・前提。

```lean
theorem named_finite_path_exact (seed : Nat) (names : List Nat)
    (s out : CommonRoleSettledConstraints.State (CommonRoleNamedPath.table seed names).length)
    (argument : Roles.Term) (answer : RoleDictionaries.Answer) :
    CommonRoleNamedPath.run seed names s = some (out, argument, answer) ↔
      CommonRoleNamedPath.Final seed names s out argument answer
```

## 件数と検証範囲

掲載定理数: 72（新規9モジュールと Main の全 theorem 宣言）。この文書は定理の型・前提の説明であり、実行ログではない。ビルド、Audit、verify-lean の成否と所要時間は親のサイクル報告を参照。未証明の一般化をこの文書で PROVED に変更しない。

## CommonRoleSiblingOrders

固定した3slotのRight seed/2 Index辺/Parent辞書例に限定。forwardは1 sweep、reverseは2 sweeps。任意の兄弟集合やscheduleの一般定理ではない。

### `forward_sweep`

forward順の実sweepは両辺を成功させs2へ至る。

```lean
theorem forward_sweep : sweep forwardEdges s0 = ([true, true], s2)
```

### `forward_models`

任意のvaluesについて、s2の充足は3slot全ての型がstrと同値であることと同値。

```lean
theorem forward_models (values : Fin 3 → Comp Common.model) :
    All Common.model values s2.atoms ↔
      Common.Equivalent (values (0 : Fin 3)).1 (.base .str) ∧
      Common.Equivalent (values (1 : Fin 3)).1 (.base .str) ∧
      Common.Equivalent (values (2 : Fin 3)).1 (.base .str)
```

### `orders_models`

任意のvaluesについて、forward1回とreverse2回の最終ordinary制約の充足は同値。

```lean
theorem orders_models (values : Fin 3 → Comp Common.model) :
    All Common.model values (sweep forwardEdges s0).2.atoms ↔
      All Common.model values (sweep reverseEdges (sweep reverseEdges s0).2).2.atoms
```

### `forward_consistent`

実solverはforward最終状態を整合と判定する。

```lean
theorem forward_consistent : CommonRoleOpenPropagation.consistent s2 = true
```

### `forward_materialized`

実materializeはforward最終slotからstrを返す。

```lean
theorem forward_materialized : materialize s2.atoms (2 : Fin 3) = some Roles.Examples.str
```

### `forward_value`

forward実入口はs2・str・実Parent辞書elaborationを返す。

```lean
theorem forward_value : forwardRun = some (s2, Roles.Examples.str,
    RoleDictionaries.elaborate visible declarations_wellFormed (parentGoal Roles.Examples.str))
```

### `orders_observable`

内部stateを除いた実外側結果のargumentと辞書answerは、forwardとreverseで等しい。

```lean
theorem orders_observable : observable forwardRun = observable CommonRoleStatefulParentExample.run
```

## CommonRolePathOrder

`SameTargets left right` は任意slotのmembershipが同値であること。固定Index(box str) seedを使う有限pathの断片で、任意の旧状態（効果制約を含む）を保持する。

### `expected_same_models`

任意の同じtarget集合を持つ有限2列・旧状態・評価に対し、expected状態の充足は同値。

```lean
theorem expected_same_models (left right : List (Fin n)) (same : SameTargets left right)
    (s : State n) (values : Fin n → Comp Common.model) :
    All Common.model values (expected left s).atoms ↔
      All Common.model values (expected right s).atoms
```

### `models_equivalent`

同じ前提でexpected状態のモデル存在が同値。

```lean
theorem models_equivalent (left right : List (Fin n)) (same : SameTargets left right)
    (s : State n) : (expected left s).Models ↔ (expected right s).Models
```

### `no_models_none`

任意path・receiver・旧状態について、expected状態にモデルがなければ実Parent入口はnone。

```lean
theorem no_models_none (outputs : List (Fin n)) (receiver : Fin n) (s : State n)
    (bad : ¬ (expected outputs (extend s receiver .str)).Models) :
    CommonRoleStatefulPathParent.run outputs receiver s = none
```

### `observable_order_independent`

任意の同じtarget集合を持つ有限2列・receiver・旧状態に対し、実Parent入口のobservableは等しい。成功やモデル存在の外部前提なし。

```lean
theorem observable_order_independent (left right : List (Fin n))
    (same : SameTargets left right) (receiver : Fin n) (s : State n) :
    observable (CommonRoleStatefulPathParent.run left receiver s) =
      observable (CommonRoleStatefulPathParent.run right receiver s)
```

### `permutation_observable`

任意の有限2列の置換・receiver・旧状態に対し、実Parent入口のobservableは等しい。

```lean
theorem permutation_observable (left right : List (Fin n)) (perm : left.Perm right)
    (receiver : Fin n) (s : State n) :
    observable (CommonRoleStatefulPathParent.run left receiver s) =
      observable (CommonRoleStatefulPathParent.run right receiver s)
```
