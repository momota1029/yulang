# Cycle127: public theorem statements

全100定理。以下の日本語文と、暗黙引数を明示した`#check @`の型を対にする。型に現れる全変数は任意、各矢印の左側は前提であり、省略しない。固定fixtureの文はその定数に限る。

健全性・完全性の分類は今回の部分materialization/source evidenceについてのもの。一般B4の完全性・主型性、候補解決・飽和を閉じた主張ではない。一般B4Bridges V3は12/12未充填。

独立な再帰Materializesとのiff、SourceRecipeの操作分解iff、独立source Instanceへの一方向の健全性を区別する。独立Instanceはcompatibleな不等identity区間も許すため、compilerとの無条件iffではない。

## Yulang.GeneralDictionaryHeadlessCandidateBoundary.survivor_outputs_empty

側: 補助。

任意のregistry・context・root・key・childrenで、現行のSurvivorが成り立つならrootの出力義務は空である。これは現行証明書の対応範囲であり、言語の拒否規則ではない。

```lean
@Yulang.GeneralDictionaryHeadlessCandidateBoundary.survivor_outputs_empty : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (context : Yulang.GeneralCandidateBoundaryParts.Context roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (key : Nat)
  (children : List.{0} (Yulang.GeneralSourceDictionaries.Occurrence roles)),
  Yulang.GeneralCandidateBoundaryParts.Survivor registry context root key children →
    Eq.{1} root.demand.outputs List.nil.{0}
```

## Yulang.GeneralDictionaryHeadlessCandidateBoundary.output_demand_outside_range

側: 補助。

任意のregistry・context・rootで、rootの出力義務が非空なら、任意のkeyとchildrenについて現行の部分Survivorは成り立たない。

```lean
@Yulang.GeneralDictionaryHeadlessCandidateBoundary.output_demand_outside_range : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (context : Yulang.GeneralCandidateBoundaryParts.Context roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
  Ne.{1} root.demand.outputs List.nil.{0} →
    ∀ (key : Nat) (children : List.{0} (Yulang.GeneralSourceDictionaries.Occurrence roles)),
      ¬Yulang.GeneralCandidateBoundaryParts.Survivor registry context root key children
```

## Yulang.GeneralDictionaryHeadlessCandidateBoundary.prepared_output_tree_outside_range

側: 補助。

任意のfixture用candidate contextについて、実出力を持つ固定recipeは準備に成功する一方、任意のkeyとchildrenでその根は現行の部分Survivorの範囲外となる。

```lean
Yulang.GeneralDictionaryHeadlessCandidateBoundary.prepared_output_tree_outside_range : ∀
  (context : Yulang.GeneralCandidateBoundaryParts.Context Yulang.GeneralDictionaryHeadlessFixture.roles),
  Eq.{1}
      (Yulang.GeneralDictionaryHeadlessPreparation.prepare Yulang.GeneralDictionaryHeadlessFixture.registry
        Yulang.GeneralDictionaryHeadlessFixture.registry_checked
        (fun x => Yulang.GeneralDictionaryHeadlessFixture.frame) Yulang.GeneralDictionaryHeadlessExamples.recipe)
      (some.{0} Yulang.GeneralDictionaryHeadlessFixture.tree) ∧
    ∀ (key : Nat)
      (children : List.{0} (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDictionaryHeadlessFixture.roles)),
      ¬Yulang.GeneralCandidateBoundaryParts.Survivor Yulang.GeneralDictionaryHeadlessFixture.registry context
          Yulang.GeneralDictionaryHeadlessFixture.root key children
```

## Yulang.GeneralDictionaryHeadlessExactness.prepare_materializes

側: 健全性。

任意のchecked registry・state・frames・有限recipe・treeで、準備がtreeを返せば、実head/RHS・source位置・全canonical子を述べる独立な再帰Materializesが成り立つ。

```lean
@Yulang.GeneralDictionaryHeadlessExactness.prepare_materializes : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (recipe : Yulang.GeneralDictionaryHeadlessPreparation.Recipe registry.roles state)
  (tree : Yulang.GeneralDictionaryTransactions.Prepared registry.roles state),
  Eq.{1} (Yulang.GeneralDictionaryHeadlessPreparation.prepare registry checked frames recipe) (some.{0} tree) →
    Yulang.GeneralDictionaryHeadlessExactness.Materializes registry checked frames recipe tree
```

## Yulang.GeneralDictionaryHeadlessExactness.materializes_prepare

側: 完全性（明記した部分範囲）。

同じ任意の入力で、独立な再帰Materializesが成り立つなら、準備はそのtreeを返す。対応する変数materialization範囲に限る。

```lean
@Yulang.GeneralDictionaryHeadlessExactness.materializes_prepare : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (recipe : Yulang.GeneralDictionaryHeadlessPreparation.Recipe registry.roles state)
  (tree : Yulang.GeneralDictionaryTransactions.Prepared registry.roles state),
  Yulang.GeneralDictionaryHeadlessExactness.Materializes registry checked frames recipe tree →
    Eq.{1} (Yulang.GeneralDictionaryHeadlessPreparation.prepare registry checked frames recipe) (some.{0} tree)
```

## Yulang.GeneralDictionaryHeadlessExactness.prepare_exact

側: 完全性（明記した部分範囲）。

任意の型欄のregistry・state・frames・recipe・treeについて、準備成功と右辺の契約が同値。HeadlessExactnessでは独立Materializes、SourceRecipeではlocalizeと既存準備の明示的な二段階成功を述べる。後者を独立意味論のiffとは呼ばない。

```lean
@Yulang.GeneralDictionaryHeadlessExactness.prepare_exact : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (recipe : Yulang.GeneralDictionaryHeadlessPreparation.Recipe registry.roles state)
  (tree : Yulang.GeneralDictionaryTransactions.Prepared registry.roles state),
  Eq.{1} (Yulang.GeneralDictionaryHeadlessPreparation.prepare registry checked frames recipe) (some.{0} tree) ↔
    Yulang.GeneralDictionaryHeadlessExactness.Materializes registry checked frames recipe tree
```

## Yulang.GeneralDictionaryHeadlessExactness.materializes_functional

側: 補助。

任意のchecked registry・state・frames・recipeと二つのtreeについて、両方が独立Materializesを満たすならtreeは等しい。

```lean
@Yulang.GeneralDictionaryHeadlessExactness.materializes_functional : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (recipe : Yulang.GeneralDictionaryHeadlessPreparation.Recipe registry.roles state)
  (first last : Yulang.GeneralDictionaryTransactions.Prepared registry.roles state),
  Yulang.GeneralDictionaryHeadlessExactness.Materializes registry checked frames recipe first →
    Yulang.GeneralDictionaryHeadlessExactness.Materializes registry checked frames recipe last → Eq.{1} first last
```

## Yulang.GeneralDictionaryHeadlessExactness.prepare_none_exact

側: 補助。

任意のchecked registry・state・frames・recipeについて、準備がnoneであることと、この対応範囲の独立Materializesを満たすtreeが一つもないことは同値。言語の拒否は意味しない。

```lean
@Yulang.GeneralDictionaryHeadlessExactness.prepare_none_exact : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (recipe : Yulang.GeneralDictionaryHeadlessPreparation.Recipe registry.roles state),
  Eq.{1} (Yulang.GeneralDictionaryHeadlessPreparation.prepare registry checked frames recipe) none.{0} ↔
    ∀ (tree : Yulang.GeneralDictionaryTransactions.Prepared registry.roles state),
      ¬Yulang.GeneralDictionaryHeadlessExactness.Materializes registry checked frames recipe tree
```

## Yulang.GeneralDictionaryHeadlessExamples.root_lookup

側: 補助。

固定fixtureの根で、実visible宣言のkey/roleと捕捉を使うlookupが指定した完全packageを返す。

```lean
Yulang.GeneralDictionaryHeadlessExamples.root_lookup : Eq.{1}
  (Yulang.GeneralDictionaryHeadlessPlans.lookup Yulang.GeneralDictionaryHeadlessFixture.registry
    Yulang.GeneralDictionaryHeadlessFixture.registry_checked Yulang.GeneralDictionaryHeadlessFixture.frame
    Yulang.GeneralDictionaryHeadlessFixture.root 2 Yulang.GeneralDictionaryHeadlessFixture.rootHeadless)
  (some.{0} Yulang.GeneralDictionaryHeadlessExamples.rootResult)
```

## Yulang.GeneralDictionaryHeadlessExamples.child_lookup

側: 補助。

固定fixtureの終端childで、実visible宣言のlookupが指定した完全packageを返す。

```lean
Yulang.GeneralDictionaryHeadlessExamples.child_lookup : Eq.{1}
  (Yulang.GeneralDictionaryHeadlessPlans.lookup Yulang.GeneralDictionaryHeadlessFixture.registry
    Yulang.GeneralDictionaryHeadlessFixture.registry_checked Yulang.GeneralDictionaryHeadlessFixture.frame
    Yulang.GeneralDictionaryHeadlessFixture.child 3 Yulang.GeneralDictionaryHeadlessFixture.childHeadless)
  (some.{0} Yulang.GeneralDictionaryHeadlessExamples.childResult)
```

## Yulang.GeneralDictionaryHeadlessExamples.leaf_prepared

側: 補助。

固定の終端recipeから、出力変数を計算した子のPrepared木が返る。

```lean
Yulang.GeneralDictionaryHeadlessExamples.leaf_prepared : Eq.{1}
  (Yulang.GeneralDictionaryHeadlessPreparation.prepare Yulang.GeneralDictionaryHeadlessFixture.registry
    Yulang.GeneralDictionaryHeadlessFixture.registry_checked (fun x => Yulang.GeneralDictionaryHeadlessFixture.frame)
    Yulang.GeneralDictionaryHeadlessExamples.leafRecipe)
  (some.{0} Yulang.GeneralDictionaryHeadlessExamples.leafTree)
```

## Yulang.GeneralDictionaryHeadlessExamples.tree_prepared

側: 補助。

固定の実producerと終端leafのrecipeから、全childと二つの根出力を保持するPrepared木が返る。

```lean
Yulang.GeneralDictionaryHeadlessExamples.tree_prepared : Eq.{1}
  (Yulang.GeneralDictionaryHeadlessPreparation.prepare Yulang.GeneralDictionaryHeadlessFixture.registry
    Yulang.GeneralDictionaryHeadlessFixture.registry_checked (fun x => Yulang.GeneralDictionaryHeadlessFixture.frame)
    Yulang.GeneralDictionaryHeadlessExamples.recipe)
  (some.{0} Yulang.GeneralDictionaryHeadlessFixture.tree)
```

## Yulang.GeneralDictionaryHeadlessExamples.prepared_uniform_completion

側: 補助。

固定recipeとtreeについて、一つのsource辞書witnessがあり、そのreadbackが一致し、このtreeのbatchを満たす任意のmodelで、実head/RHSを持つSourceInstanceのEvidenceが成立する。

```lean
Yulang.GeneralDictionaryHeadlessExamples.prepared_uniform_completion : Exists.{1} fun witness =>
  Yulang.GeneralSourceDictionaries.Readback Yulang.GeneralDictionaryHeadlessExamples.recipe.root
      (Yulang.GeneralSourceDictionaries.erase Yulang.GeneralDictionaryHeadlessFixture.tree.dictionary) witness ∧
    ∀ (model : Yulang.GeneralSourceState.Assignment),
      Yulang.GeneralSourceState.Models
          (Yulang.GeneralDictionaryBatchRecording.record Yulang.GeneralDictionaryHeadlessFixture.tree.items) model →
        Yulang.GeneralSourceDictionaries.Evidence
          (Yulang.GeneralDictionaryVariableTransactions.SourceInstance Yulang.GeneralDictionaryHeadlessFixture.registry
            Yulang.GeneralDictionaryHeadlessFixture.registry_checked
            (fun x => Yulang.GeneralDictionaryHeadlessFixture.frame)
            (Yulang.GeneralDictionaryVariableHeads.heads Yulang.GeneralDictionaryHeadlessFixture.roles
              Yulang.GeneralDictionaryHeadlessFixture.state)
            model)
          witness
```

## Yulang.GeneralDictionaryHeadlessExamples.prepared_nonvacuous

側: 補助。

固定recipeはtreeを返し、明示的なall-int assignmentがその全batchのModelsを満たす。

```lean
Yulang.GeneralDictionaryHeadlessExamples.prepared_nonvacuous : Eq.{1}
    (Yulang.GeneralDictionaryHeadlessPreparation.prepare Yulang.GeneralDictionaryHeadlessFixture.registry
      Yulang.GeneralDictionaryHeadlessFixture.registry_checked (fun x => Yulang.GeneralDictionaryHeadlessFixture.frame)
      Yulang.GeneralDictionaryHeadlessExamples.recipe)
    (some.{0} Yulang.GeneralDictionaryHeadlessFixture.tree) ∧
  Yulang.GeneralSourceState.Models
    (Yulang.GeneralDictionaryBatchRecording.record Yulang.GeneralDictionaryHeadlessFixture.tree.items)
    Yulang.GeneralDictionaryHeadlessFixture.assignment
```

## Yulang.GeneralDictionaryHeadlessExamples.omitted_child_defers

側: 補助。

固定producerの実childをrecipeから落とすと準備はnoneとなる。位置を自動計算する版でも子の完全性を弱めない。

```lean
Yulang.GeneralDictionaryHeadlessExamples.omitted_child_defers : Eq.{1}
  (Yulang.GeneralDictionaryHeadlessPreparation.prepare Yulang.GeneralDictionaryHeadlessFixture.registry
    Yulang.GeneralDictionaryHeadlessFixture.registry_checked (fun x => Yulang.GeneralDictionaryHeadlessFixture.frame)
    (Yulang.GeneralDictionaryHeadlessPreparation.Recipe.node Yulang.GeneralDictionaryHeadlessFixture.root 2
      Yulang.GeneralDictionaryHeadlessFixture.rootHeadless List.nil.{0}))
  none.{0}
```

## Yulang.GeneralDictionaryHeadlessExamples.wrong_role_key_defers

側: 補助。

固定rootに終端childのkeyを渡してもroleが違うのでlookupはnoneとなる。

```lean
Yulang.GeneralDictionaryHeadlessExamples.wrong_role_key_defers : Eq.{1}
  (Yulang.GeneralDictionaryHeadlessPlans.lookup Yulang.GeneralDictionaryHeadlessFixture.registry
    Yulang.GeneralDictionaryHeadlessFixture.registry_checked Yulang.GeneralDictionaryHeadlessFixture.frame
    Yulang.GeneralDictionaryHeadlessFixture.root 3 Yulang.GeneralDictionaryHeadlessFixture.rootHeadless)
  none.{0}
```

## Yulang.GeneralDictionaryHeadlessExamples.absent_key_defers

側: 補助。

固定rootに存在しないkey99を渡すとlookupはnoneとなる。

```lean
Yulang.GeneralDictionaryHeadlessExamples.absent_key_defers : Eq.{1}
  (Yulang.GeneralDictionaryHeadlessPlans.lookup Yulang.GeneralDictionaryHeadlessFixture.registry
    Yulang.GeneralDictionaryHeadlessFixture.registry_checked Yulang.GeneralDictionaryHeadlessFixture.frame
    Yulang.GeneralDictionaryHeadlessFixture.root 99 Yulang.GeneralDictionaryHeadlessFixture.rootHeadless)
  none.{0}
```

## Yulang.GeneralDictionaryHeadlessExamples.nominal_root_still_defers

側: 補助。

前cycleのnominal headの固定rootは、今回の変数head builderでもnoneとなる。nominalの意味を変数に読み替えない。

```lean
Yulang.GeneralDictionaryHeadlessExamples.nominal_root_still_defers : Eq.{1}
  (Yulang.GeneralDictionaryVariableHeads.build Yulang.GeneralDictionaryOutputBinderExamples.binderWrap
    Yulang.GeneralDictionaryOutputBinderExamples.binderWrap_checked ⋯ Yulang.GeneralDictionaryTerminalFixture.capture
    Yulang.GeneralDictionaryHeadExamples.rootHeadless)
  none.{0}
```

## Yulang.GeneralDictionaryHeadlessExamples.unequal_capture_defers

側: 補助。

固定childで捕捉の上下端source IDを100/101にすると、両方が存在してもlookupはnoneとなる。

```lean
Yulang.GeneralDictionaryHeadlessExamples.unequal_capture_defers : Eq.{1}
  (Yulang.GeneralDictionaryHeadlessPlans.lookup Yulang.GeneralDictionaryHeadlessFixture.registry
    Yulang.GeneralDictionaryHeadlessFixture.registry_checked Yulang.GeneralDictionaryHeadlessExamples.unequalFrame
    Yulang.GeneralDictionaryHeadlessFixture.child 3 Yulang.GeneralDictionaryHeadlessFixture.childHeadless)
  none.{0}
```

## Yulang.GeneralDictionaryHeadlessExamples.absent_second_source_defers

側: 補助。

固定binary rootの第1引数は存在しても、第2引数のsource999が存在しなければ全lookupはnoneとなる。

```lean
Yulang.GeneralDictionaryHeadlessExamples.absent_second_source_defers : Eq.{1}
  (Yulang.GeneralDictionaryHeadlessPlans.lookup Yulang.GeneralDictionaryHeadlessFixture.registry
    Yulang.GeneralDictionaryHeadlessFixture.registry_checked Yulang.GeneralDictionaryHeadlessExamples.absentSecondFrame
    Yulang.GeneralDictionaryHeadlessFixture.root 2 Yulang.GeneralDictionaryHeadlessFixture.rootHeadless)
  none.{0}
```

## Yulang.GeneralDictionaryHeadlessExamples.changed_child_identity_defers

側: 補助。

固定rootで、同じ需要を持つ別identity999のchildを代わりに渡すと準備はnoneとなる。

```lean
Yulang.GeneralDictionaryHeadlessExamples.changed_child_identity_defers : Eq.{1}
  (Yulang.GeneralDictionaryHeadlessPreparation.prepare Yulang.GeneralDictionaryHeadlessFixture.registry
    Yulang.GeneralDictionaryHeadlessFixture.registry_checked (fun x => Yulang.GeneralDictionaryHeadlessFixture.frame)
    (Yulang.GeneralDictionaryHeadlessPreparation.Recipe.node Yulang.GeneralDictionaryHeadlessFixture.root 2
      Yulang.GeneralDictionaryHeadlessFixture.rootHeadless
      (List.cons.{0} Yulang.GeneralDictionaryHeadlessExamples.wrongLeafRecipe List.nil.{0})))
  none.{0}
```

## Yulang.GeneralDictionaryHeadlessExamples.source_localization

側: 補助。

固定fixtureのsource mapはslot+100であり、計算されたhead/outputの局所slotと実source100/101/102の対応が保持される。正確な等式群は型欄の通り。

```lean
Yulang.GeneralDictionaryHeadlessExamples.source_localization : Eq.{1}
    (Yulang.GeneralDictionaryHeadlessFixture.state.source 0) 100 ∧
  Eq.{1}
    (Yulang.GeneralDictionaryVariableHeads.compileAt Yulang.GeneralDictionaryHeadlessFixture.state
      Yulang.GeneralDictionaryHeadlessFixture.leaf Yulang.GeneralDictionaryHeadlessFixture.capture 0)
    (some.{0} (Yulang.Core.PresenceGeneration.TyTerm.var 0))
```

## Yulang.GeneralDictionaryHeadlessFixture.binderWrap_checked

側: 補助。

binary変数head、実producer child、output binderを持つ固定宣言が全DeclarationChecked条件を満たす。任意captureでの厳密なPaterson下降も含む。

```lean
Yulang.GeneralDictionaryHeadlessFixture.binderWrap_checked : Yulang.GeneralDeclarations.DeclarationChecked
  Yulang.GeneralDeclarationExamples.constructors Yulang.GeneralDictionaryHeadlessFixture.roles
  Yulang.GeneralDictionaryHeadlessFixture.binderWrap
```

## Yulang.GeneralDictionaryHeadlessFixture.leaf_checked

側: 補助。

変数head・明示input変数RHS・whereなしの固定終端宣言がDeclarationCheckedを満たす。

```lean
Yulang.GeneralDictionaryHeadlessFixture.leaf_checked : Yulang.GeneralDeclarations.DeclarationChecked
  Yulang.GeneralDeclarationExamples.constructors Yulang.GeneralDictionaryHeadlessFixture.roles
  Yulang.GeneralDictionaryHeadlessFixture.leaf
```

## Yulang.GeneralDictionaryHeadlessFixture.registry_checked

側: 補助。

根と終端の固定visible registryがkey一意性と全宣言検査を満たす。

```lean
Yulang.GeneralDictionaryHeadlessFixture.registry_checked : Yulang.GeneralDeclarations.Checked
  Yulang.GeneralDictionaryHeadlessFixture.registry
```

## Yulang.GeneralDictionaryHeadlessFixture.root_actual_children

側: 補助。

固定根の実宣言の完全canonical生成列は、指定した一つのchild occurrenceと等しい。

```lean
Yulang.GeneralDictionaryHeadlessFixture.root_actual_children : Eq.{1}
  (Yulang.GeneralDictionaryEmissionPlans.children Yulang.GeneralDictionaryHeadlessFixture.frame
    Yulang.GeneralDictionaryHeadlessFixture.root Yulang.GeneralDictionaryHeadlessFixture.binderWrap
    Yulang.GeneralDictionaryHeadlessFixture.binderWrap_checked)
  (List.cons.{0} Yulang.GeneralDictionaryHeadlessFixture.child List.nil.{0})
```

## Yulang.GeneralDictionaryHeadlessFixture.child_actual_children

側: 補助。

固定終端宣言の完全canonical生成列は空である。

```lean
Yulang.GeneralDictionaryHeadlessFixture.child_actual_children : Eq.{1}
  (Yulang.GeneralDictionaryEmissionPlans.children Yulang.GeneralDictionaryHeadlessFixture.frame
    Yulang.GeneralDictionaryHeadlessFixture.child Yulang.GeneralDictionaryHeadlessFixture.leaf
    Yulang.GeneralDictionaryHeadlessFixture.leaf_checked)
  List.nil.{0}
```

## Yulang.GeneralDictionaryHeadlessFixture.root_holds

側: 補助。

固定all-int assignmentは固定根Locatedのすべての引数区間と出力等式を満たす。

```lean
Yulang.GeneralDictionaryHeadlessFixture.root_holds : Yulang.GeneralDictionaryHeadlessFixture.rootLocated.equations.Holds
  Yulang.GeneralDictionaryHeadlessFixture.assignment
```

## Yulang.GeneralDictionaryHeadlessFixture.child_holds

側: 補助。

固定all-int assignmentは固定child Locatedのすべての区間と出力等式を満たす。

```lean
Yulang.GeneralDictionaryHeadlessFixture.child_holds : Yulang.GeneralDictionaryHeadlessFixture.childLocated.equations.Holds
  Yulang.GeneralDictionaryHeadlessFixture.assignment
```

## Yulang.GeneralDictionaryHeadlessFixture.joint_model

側: 補助。

固定all-int assignmentは根とchildを一度に記録したbatchのModelsを満たす。

```lean
Yulang.GeneralDictionaryHeadlessFixture.joint_model : Yulang.GeneralSourceState.Models
  (Yulang.GeneralDictionaryBatchRecording.record
    (List.cons.{0} Yulang.GeneralDictionaryHeadlessFixture.rootItem
      (List.cons.{0} Yulang.GeneralDictionaryHeadlessFixture.childItem List.nil.{0})))
  Yulang.GeneralDictionaryHeadlessFixture.assignment
```

## Yulang.GeneralDictionaryHeadlessFixture.tree_items

側: 補助。

固定Prepared木から抽出する記録項目は根項目とchild項目の二つである。

```lean
Yulang.GeneralDictionaryHeadlessFixture.tree_items : Eq.{1} Yulang.GeneralDictionaryHeadlessFixture.tree.items
  (List.cons.{0} Yulang.GeneralDictionaryHeadlessFixture.rootItem
    (List.cons.{0} Yulang.GeneralDictionaryHeadlessFixture.childItem List.nil.{0}))
```

## Yulang.GeneralDictionaryHeadlessFixture.tree_joint_model

側: 補助。

固定treeの全itemsを記録した状態は明示的all-int assignmentをmodelに持つ。

```lean
Yulang.GeneralDictionaryHeadlessFixture.tree_joint_model : Yulang.GeneralSourceState.Models
  (Yulang.GeneralDictionaryBatchRecording.record Yulang.GeneralDictionaryHeadlessFixture.tree.items)
  Yulang.GeneralDictionaryHeadlessFixture.assignment
```

## Yulang.GeneralDictionaryHeadlessFixture.retained_outputs

側: 補助。

固定rootの出力target103/104とchildのproducer target102が別の義務として保持される。

```lean
Yulang.GeneralDictionaryHeadlessFixture.retained_outputs : Eq.{1}
    Yulang.GeneralDictionaryHeadlessFixture.rootDemand.outputs
    (List.cons.{0} { name := 0, target := 103 } (List.cons.{0} { name := 0, target := 104 } List.nil.{0})) ∧
  Eq.{1} Yulang.GeneralDictionaryHeadlessFixture.childDemand.outputs
    (List.cons.{0} { name := 1, target := 102 } List.nil.{0})
```

## Yulang.GeneralDictionaryHeadlessFixture.root_build

側: 補助。

固定根の実RHSから、指定したLocatedのoutput vectorが計算される。

```lean
Yulang.GeneralDictionaryHeadlessFixture.root_build : Eq.{1}
  (Yulang.GeneralDictionaryVariableTerms.build Yulang.GeneralDictionaryHeadlessFixture.binderWrap
    Yulang.GeneralDictionaryHeadlessFixture.capture Yulang.GeneralDictionaryHeadlessFixture.rootInputs)
  (some.{0} Yulang.GeneralDictionaryHeadlessFixture.rootLocated)
```

## Yulang.GeneralDictionaryHeadlessFixture.child_build

側: 補助。

固定終端の実input変数RHSから、指定したLocatedのoutput vectorが計算される。

```lean
Yulang.GeneralDictionaryHeadlessFixture.child_build : Eq.{1}
  (Yulang.GeneralDictionaryVariableTerms.build Yulang.GeneralDictionaryHeadlessFixture.leaf
    Yulang.GeneralDictionaryHeadlessFixture.capture Yulang.GeneralDictionaryHeadlessFixture.childInputs)
  (some.{0} Yulang.GeneralDictionaryHeadlessFixture.childLocated)
```

## Yulang.GeneralDictionaryHeadlessFixture.root_lookup

側: 補助。

固定fixtureの根で、実visible宣言のkey/roleと捕捉を使うlookupが指定した完全packageを返す。

```lean
Yulang.GeneralDictionaryHeadlessFixture.root_lookup : Eq.{1}
  (Yulang.GeneralDictionaryVariablePlans.lookup Yulang.GeneralDictionaryHeadlessFixture.registry
    Yulang.GeneralDictionaryHeadlessFixture.registry_checked Yulang.GeneralDictionaryHeadlessFixture.frame
    Yulang.GeneralDictionaryHeadlessFixture.root 2 Yulang.GeneralDictionaryHeadlessFixture.rootInputs)
  (some.{0} Yulang.GeneralDictionaryHeadlessFixture.rootResult)
```

## Yulang.GeneralDictionaryHeadlessFixture.child_lookup

側: 補助。

固定fixtureの終端childで、実visible宣言のlookupが指定した完全packageを返す。

```lean
Yulang.GeneralDictionaryHeadlessFixture.child_lookup : Eq.{1}
  (Yulang.GeneralDictionaryVariablePlans.lookup Yulang.GeneralDictionaryHeadlessFixture.registry
    Yulang.GeneralDictionaryHeadlessFixture.registry_checked Yulang.GeneralDictionaryHeadlessFixture.frame
    Yulang.GeneralDictionaryHeadlessFixture.child 3 Yulang.GeneralDictionaryHeadlessFixture.childInputs)
  (some.{0} Yulang.GeneralDictionaryHeadlessFixture.childResult)
```

## Yulang.GeneralDictionaryHeadlessFixture.root_head_denotes

側: 補助。

固定binary根の各positional head termが、実宣言の正規化変数と正確な捕捉sourceを表す。

```lean
Yulang.GeneralDictionaryHeadlessFixture.root_head_denotes : Yulang.GeneralDictionaryVariableHeads.HeadDenotes
  Yulang.GeneralDictionaryHeadlessFixture.binderWrap Yulang.GeneralDictionaryHeadlessFixture.capture
  Yulang.GeneralDictionaryHeadlessFixture.rootDemand Yulang.GeneralDictionaryHeadlessFixture.rootInputs.head
```

## Yulang.GeneralDictionaryHeadlessFixture.child_head_denotes

側: 補助。

固定終端のhead termが実宣言の正規化変数と正確な捕捉sourceを表す。

```lean
Yulang.GeneralDictionaryHeadlessFixture.child_head_denotes : Yulang.GeneralDictionaryVariableHeads.HeadDenotes
  Yulang.GeneralDictionaryHeadlessFixture.leaf Yulang.GeneralDictionaryHeadlessFixture.capture
  Yulang.GeneralDictionaryHeadlessFixture.childDemand Yulang.GeneralDictionaryHeadlessFixture.childInputs.head
```

## Yulang.GeneralDictionaryHeadlessFixture.root_head_builds

側: 補助。

固定根でheadを渡さずに、実binary変数headから指定したInputsが計算される。

```lean
Yulang.GeneralDictionaryHeadlessFixture.root_head_builds : Eq.{1}
  (Yulang.GeneralDictionaryVariableHeads.build Yulang.GeneralDictionaryHeadlessFixture.binderWrap
    Yulang.GeneralDictionaryHeadlessFixture.binderWrap_checked ⋯ Yulang.GeneralDictionaryHeadlessFixture.capture
    Yulang.GeneralDictionaryHeadlessFixture.rootHeadless)
  (some.{0} Yulang.GeneralDictionaryHeadlessFixture.rootInputs)
```

## Yulang.GeneralDictionaryHeadlessFixture.child_head_builds

側: 補助。

固定終端でheadを渡さずに、実変数headから指定したInputsが計算される。

```lean
Yulang.GeneralDictionaryHeadlessFixture.child_head_builds : Eq.{1}
  (Yulang.GeneralDictionaryVariableHeads.build Yulang.GeneralDictionaryHeadlessFixture.leaf
    Yulang.GeneralDictionaryHeadlessFixture.leaf_checked ⋯ Yulang.GeneralDictionaryHeadlessFixture.capture
    Yulang.GeneralDictionaryHeadlessFixture.childHeadless)
  (some.{0} Yulang.GeneralDictionaryHeadlessFixture.childInputs)
```

## Yulang.GeneralDictionaryHeadlessFixture.tree_built

側: 補助。

固定treeは、外部head解釈の前提なしに具体的VariableHeads.headsでBuiltとなる。

```lean
Yulang.GeneralDictionaryHeadlessFixture.tree_built : Yulang.GeneralDictionaryVariableTransactions.Built
  Yulang.GeneralDictionaryHeadlessFixture.registry Yulang.GeneralDictionaryHeadlessFixture.registry_checked
  (fun x => Yulang.GeneralDictionaryHeadlessFixture.frame)
  (Yulang.GeneralDictionaryVariableHeads.heads Yulang.GeneralDictionaryHeadlessFixture.roles
    Yulang.GeneralDictionaryHeadlessFixture.state)
  Yulang.GeneralDictionaryHeadlessFixture.tree
```

## Yulang.GeneralDictionaryHeadlessFixture.uniform_completion

側: 補助。

固定treeについて一つのreadback辞書witnessがあり、その全batchを満たす任意のmodelで実head/RHSのEvidenceが成立する。

```lean
Yulang.GeneralDictionaryHeadlessFixture.uniform_completion : Exists.{1} fun witness =>
  Yulang.GeneralSourceDictionaries.Readback Yulang.GeneralDictionaryHeadlessFixture.tree.root
      (Yulang.GeneralSourceDictionaries.erase Yulang.GeneralDictionaryHeadlessFixture.tree.dictionary) witness ∧
    ∀ (model : Yulang.GeneralSourceState.Assignment),
      Yulang.GeneralSourceState.Models
          (Yulang.GeneralDictionaryBatchRecording.record Yulang.GeneralDictionaryHeadlessFixture.tree.items) model →
        Yulang.GeneralSourceDictionaries.Evidence
          (Yulang.GeneralDictionaryVariableTransactions.SourceInstance Yulang.GeneralDictionaryHeadlessFixture.registry
            Yulang.GeneralDictionaryHeadlessFixture.registry_checked
            (fun x => Yulang.GeneralDictionaryHeadlessFixture.frame)
            (Yulang.GeneralDictionaryVariableHeads.heads Yulang.GeneralDictionaryHeadlessFixture.roles
              Yulang.GeneralDictionaryHeadlessFixture.state)
            model)
          witness
```

## Yulang.GeneralDictionaryHeadlessFixture.all_model_root_child_input

側: 健全性。

固定treeのbatchを満たす任意のassignmentと任意の根output occurrenceについて、targetとproducer102、producer102とinput100、従ってtargetとinput100がそれぞれCommon同値となる。

```lean
Yulang.GeneralDictionaryHeadlessFixture.all_model_root_child_input : ∀ (model : Yulang.GeneralSourceState.Assignment),
  Yulang.GeneralSourceState.Models
      (Yulang.GeneralDictionaryBatchRecording.record Yulang.GeneralDictionaryHeadlessFixture.tree.items) model →
    ∀ (index : Fin (List.length.{0} Yulang.GeneralDictionaryHeadlessFixture.rootDemand.outputs)),
      Yulang.Common.Equivalent
          (Prod.fst.{0, 0}
            (model (getElem.{0, 0, 0} Yulang.GeneralDictionaryHeadlessFixture.rootDemand.outputs index ⋯).target))
          (Prod.fst.{0, 0} (model 102)) ∧
        Yulang.Common.Equivalent (Prod.fst.{0, 0} (model 102)) (Prod.fst.{0, 0} (model 100)) ∧
          Yulang.Common.Equivalent
            (Prod.fst.{0, 0}
              (model (getElem.{0, 0, 0} Yulang.GeneralDictionaryHeadlessFixture.rootDemand.outputs index ⋯).target))
            (Prod.fst.{0, 0} (model 100))
```

## Yulang.GeneralDictionaryHeadlessLocations.inputs_unique

側: 補助。

任意state・demandと二つの有効なHeadlessInputsについて、source mapの単射性から全input packageが等しい。

```lean
@Yulang.GeneralDictionaryHeadlessLocations.inputs_unique : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State} {demand : Yulang.GeneralSourceState.Demand roles}
  (first last : Yulang.GeneralDictionaryVariableHeads.HeadlessInputs state demand), Eq.{1} first last
```

## Yulang.GeneralDictionaryHeadlessLocations.inputs_available

側: 補助。

任意state・demandでHeadlessInputsがあれば、すべての引数上下端と全output targetにsource slotが存在する。

```lean
@Yulang.GeneralDictionaryHeadlessLocations.inputs_available : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State} {demand : Yulang.GeneralSourceState.Demand roles}
  (inputs : Yulang.GeneralDictionaryVariableHeads.HeadlessInputs state demand),
  Yulang.GeneralDictionaryHeadlessLocations.Available state demand
```

## Yulang.GeneralDictionaryHeadlessLocations.locate_success_iff

側: 完全性（明記した部分範囲）。

任意state・demandについて、locateが何らかのHeadlessInputsを返すことと、独立な全endpoint/target source membership Availableが同値。

```lean
@Yulang.GeneralDictionaryHeadlessLocations.locate_success_iff : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralSourceState.State) (demand : Yulang.GeneralSourceState.Demand roles),
  (Exists.{1} fun inputs => Eq.{1} (Yulang.GeneralDictionaryHeadlessLocations.locate state demand) (some.{0} inputs)) ↔
    Yulang.GeneralDictionaryHeadlessLocations.Available state demand
```

## Yulang.GeneralDictionaryHeadlessLocations.locate_inputs

側: 完全性（明記した部分範囲）。

任意state・demandと有効なHeadlessInputsについて、locateは必ずその一意なpackageを返す。

```lean
@Yulang.GeneralDictionaryHeadlessLocations.locate_inputs : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State} {demand : Yulang.GeneralSourceState.Demand roles}
  (inputs : Yulang.GeneralDictionaryVariableHeads.HeadlessInputs state demand),
  Eq.{1} (Yulang.GeneralDictionaryHeadlessLocations.locate state demand) (some.{0} inputs)
```

## Yulang.GeneralDictionaryHeadlessLocations.locate_none_iff

側: 補助。

任意state・demandについて、locateがnoneであることとAvailableが成り立たないことは同値。

```lean
@Yulang.GeneralDictionaryHeadlessLocations.locate_none_iff : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralSourceState.State) (demand : Yulang.GeneralSourceState.Demand roles),
  Eq.{1} (Yulang.GeneralDictionaryHeadlessLocations.locate state demand) none.{0} ↔
    ¬Yulang.GeneralDictionaryHeadlessLocations.Available state demand
```

## Yulang.GeneralDictionaryHeadlessLocations.linked_available

側: 補助。

任意state・demandでLinkedが成り立つなら、全endpoint/targetがsource mapに存在するAvailableが成り立つ。

```lean
@Yulang.GeneralDictionaryHeadlessLocations.linked_available : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State} {demand : Yulang.GeneralSourceState.Demand roles},
  Yulang.GeneralSourceState.Linked state demand → Yulang.GeneralDictionaryHeadlessLocations.Available state demand
```

## Yulang.GeneralDictionaryHeadlessLocations.locate_linked

側: 完全性（明記した部分範囲）。

任意state・demandでLinkedなら、locateが返すHeadlessInputsが存在する。

```lean
@Yulang.GeneralDictionaryHeadlessLocations.locate_linked : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State} {demand : Yulang.GeneralSourceState.Demand roles},
  Yulang.GeneralSourceState.Linked state demand →
    Exists.{1} fun inputs => Eq.{1} (Yulang.GeneralDictionaryHeadlessLocations.locate state demand) (some.{0} inputs)
```

## Yulang.GeneralDictionaryHeadlessOrder.prepare_reorders

側: 補助。

任意の同じconstructors/roles・二つのchecked宣言列・許されたReorders・state・frames・recipeについて、準備のOption結果全体が等しい。成功だけでなくnoneも保存する。

```lean
@Yulang.GeneralDictionaryHeadlessOrder.prepare_reorders : ∀ {state : Yulang.GeneralSourceState.State}
  (constructors : Yulang.GeneralDeclarationPatterns.Constructors) (roles : Yulang.Roles.RoleDecls)
  (first last : List.{0} Yulang.GeneralDeclarations.Declaration)
  (one : Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := first })
  (two : Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := last }),
  Yulang.GeneralRegistryReordering.Reorders { constructors := constructors, roles := roles, declarations := first }
      { constructors := constructors, roles := roles, declarations := last } →
    ∀ (frames : Yulang.GeneralDictionaryTransactions.Frames roles)
      (recipe : Yulang.GeneralDictionaryHeadlessPreparation.Recipe roles state),
      Eq.{1}
        (Yulang.GeneralDictionaryHeadlessPreparation.prepare
          { constructors := constructors, roles := roles, declarations := first } one frames recipe)
        (Yulang.GeneralDictionaryHeadlessPreparation.prepare
          { constructors := constructors, roles := roles, declarations := last } two frames recipe)
```

## Yulang.GeneralDictionaryHeadlessOrder.dictionary_reorders

側: 補助。

上記の任意の固定入力とregistry Reordersについて、準備結果から取り出す辞書のOption全体が等しい。

```lean
@Yulang.GeneralDictionaryHeadlessOrder.dictionary_reorders : ∀ {state : Yulang.GeneralSourceState.State}
  (constructors : Yulang.GeneralDeclarationPatterns.Constructors) (roles : Yulang.Roles.RoleDecls)
  (first last : List.{0} Yulang.GeneralDeclarations.Declaration)
  (one : Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := first })
  (two : Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := last }),
  Yulang.GeneralRegistryReordering.Reorders { constructors := constructors, roles := roles, declarations := first }
      { constructors := constructors, roles := roles, declarations := last } →
    ∀ (frames : Yulang.GeneralDictionaryTransactions.Frames roles)
      (recipe : Yulang.GeneralDictionaryHeadlessPreparation.Recipe roles state),
      Eq.{1}
        (Option.map.{0, 0} Yulang.GeneralDictionaryTransactions.Prepared.dictionary
          (Yulang.GeneralDictionaryHeadlessPreparation.prepare
            { constructors := constructors, roles := roles, declarations := first } one frames recipe))
        (Option.map.{0, 0} Yulang.GeneralDictionaryTransactions.Prepared.dictionary
          (Yulang.GeneralDictionaryHeadlessPreparation.prepare
            { constructors := constructors, roles := roles, declarations := last } two frames recipe))
```

## Yulang.GeneralDictionaryHeadlessOrder.record_reorders

側: 補助。

同じ任意の入力とReordersについて、準備結果の全batchを記録した状態のOptionが等しい。

```lean
@Yulang.GeneralDictionaryHeadlessOrder.record_reorders : ∀ {state : Yulang.GeneralSourceState.State}
  (constructors : Yulang.GeneralDeclarationPatterns.Constructors) (roles : Yulang.Roles.RoleDecls)
  (first last : List.{0} Yulang.GeneralDeclarations.Declaration)
  (one : Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := first })
  (two : Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := last }),
  Yulang.GeneralRegistryReordering.Reorders { constructors := constructors, roles := roles, declarations := first }
      { constructors := constructors, roles := roles, declarations := last } →
    ∀ (frames : Yulang.GeneralDictionaryTransactions.Frames roles)
      (recipe : Yulang.GeneralDictionaryHeadlessPreparation.Recipe roles state),
      Eq.{1}
        (Option.map.{0, 0} (fun tree => Yulang.GeneralDictionaryBatchRecording.record tree.items)
          (Yulang.GeneralDictionaryHeadlessPreparation.prepare
            { constructors := constructors, roles := roles, declarations := first } one frames recipe))
        (Option.map.{0, 0} (fun tree => Yulang.GeneralDictionaryBatchRecording.record tree.items)
          (Yulang.GeneralDictionaryHeadlessPreparation.prepare
            { constructors := constructors, roles := roles, declarations := last } two frames recipe))
```

## Yulang.GeneralDictionaryHeadlessOrder.prepared_equal

側: 補助。

同じ固定入力でReorders前後の準備がそれぞれbefore/afterに成功するなら、Prepared木全体が等しい。

```lean
@Yulang.GeneralDictionaryHeadlessOrder.prepared_equal : ∀ {state : Yulang.GeneralSourceState.State}
  (constructors : Yulang.GeneralDeclarationPatterns.Constructors) (roles : Yulang.Roles.RoleDecls)
  (first last : List.{0} Yulang.GeneralDeclarations.Declaration)
  (one : Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := first })
  (two : Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := last }),
  Yulang.GeneralRegistryReordering.Reorders { constructors := constructors, roles := roles, declarations := first }
      { constructors := constructors, roles := roles, declarations := last } →
    ∀ (frames : Yulang.GeneralDictionaryTransactions.Frames roles)
      (recipe : Yulang.GeneralDictionaryHeadlessPreparation.Recipe roles state)
      (before after : Yulang.GeneralDictionaryTransactions.Prepared roles state),
      Eq.{1}
          (Yulang.GeneralDictionaryHeadlessPreparation.prepare
            { constructors := constructors, roles := roles, declarations := first } one frames recipe)
          (some.{0} before) →
        Eq.{1}
            (Yulang.GeneralDictionaryHeadlessPreparation.prepare
              { constructors := constructors, roles := roles, declarations := last } two frames recipe)
            (some.{0} after) →
          Eq.{1} before after
```

## Yulang.GeneralDictionaryHeadlessOrder.dictionary_equivalent

側: 補助。

上記の成功前提で、前後のsource辞書はDictionaryEquivalent、消去したpayloadもEquivalentとなる。候補探索順や異なる最終状態の定理ではない。

```lean
@Yulang.GeneralDictionaryHeadlessOrder.dictionary_equivalent : ∀ {state : Yulang.GeneralSourceState.State}
  (constructors : Yulang.GeneralDeclarationPatterns.Constructors) (roles : Yulang.Roles.RoleDecls)
  (first last : List.{0} Yulang.GeneralDeclarations.Declaration)
  (one : Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := first })
  (two : Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := last }),
  Yulang.GeneralRegistryReordering.Reorders { constructors := constructors, roles := roles, declarations := first }
      { constructors := constructors, roles := roles, declarations := last } →
    ∀ (frames : Yulang.GeneralDictionaryTransactions.Frames roles)
      (recipe : Yulang.GeneralDictionaryHeadlessPreparation.Recipe roles state)
      (before after : Yulang.GeneralDictionaryTransactions.Prepared roles state),
      Eq.{1}
          (Yulang.GeneralDictionaryHeadlessPreparation.prepare
            { constructors := constructors, roles := roles, declarations := first } one frames recipe)
          (some.{0} before) →
        Eq.{1}
            (Yulang.GeneralDictionaryHeadlessPreparation.prepare
              { constructors := constructors, roles := roles, declarations := last } two frames recipe)
            (some.{0} after) →
          Yulang.GeneralSourceDictionaries.DictionaryEquivalent before.dictionary after.dictionary ∧
            Yulang.GeneralDictionaryPayloadOrder.Equivalent (Yulang.GeneralSourceDictionaries.erase before.dictionary)
              (Yulang.GeneralSourceDictionaries.erase after.dictionary)
```

## Yulang.GeneralDictionaryHeadlessPendingBoundary.root_still_pending

側: 補助。

固定fixtureで全無名引数をNeededにすると、実source stateの根はRootPendingである。

```lean
Yulang.GeneralDictionaryHeadlessPendingBoundary.root_still_pending : Yulang.GeneralSourceState.RootPending
  Yulang.GeneralDictionaryHeadlessFixture.state Yulang.GeneralDictionaryHeadlessFixture.rootDemand
  Yulang.GeneralDictionaryHeadlessPendingBoundary.allInputs
```

## Yulang.GeneralDictionaryHeadlessPendingBoundary.preparation_with_pending

側: 補助。

固定の完全な二node recipeが準備に成功することと、全無名引数を必要とする根がRootPendingであることが同時に成立する。準備成功は解決開始の許可ではない。

```lean
Yulang.GeneralDictionaryHeadlessPendingBoundary.preparation_with_pending : Eq.{1}
    (Yulang.GeneralDictionaryHeadlessPreparation.prepare Yulang.GeneralDictionaryHeadlessFixture.registry
      Yulang.GeneralDictionaryHeadlessFixture.registry_checked (fun x => Yulang.GeneralDictionaryHeadlessFixture.frame)
      Yulang.GeneralDictionaryHeadlessExamples.recipe)
    (some.{0} Yulang.GeneralDictionaryHeadlessFixture.tree) ∧
  Yulang.GeneralSourceState.RootPending Yulang.GeneralDictionaryHeadlessFixture.state
    Yulang.GeneralDictionaryHeadlessFixture.rootDemand Yulang.GeneralDictionaryHeadlessPendingBoundary.allInputs
```

## Yulang.GeneralDictionaryHeadlessPlans.lookup_build_exact

側: 補助。

任意のchecked registry・state・frame・root・key・headless入力・resultについて、lookup成功は、同じvisible宣言のkey/role一致・head build成功・既存output lookup成功の存在と同値。これは操作の分解である。

```lean
@Yulang.GeneralDictionaryHeadlessPlans.lookup_build_exact : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frame : Yulang.GeneralDictionaryEmissionPlans.Frame registry.roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles) (key : Nat)
  (inputs : Yulang.GeneralDictionaryVariableHeads.HeadlessInputs state root.demand)
  (result : Yulang.GeneralDictionaryHeadlessPlans.Result state root),
  Eq.{1} (Yulang.GeneralDictionaryHeadlessPlans.lookup registry checked frame root key inputs) (some.{0} result) ↔
    Exists.{1} fun declaration =>
      Exists.{0} fun present =>
        Exists.{0} fun role =>
          Eq.{1} declaration.id key ∧
            Eq.{1}
                (Yulang.GeneralDictionaryVariableHeads.build declaration ⋯ role (frame.capture declaration.id) inputs)
                (some.{0} result.inputs) ∧
              Eq.{1} (Yulang.GeneralDictionaryVariablePlans.lookup registry checked frame root key result.inputs)
                (some.{0} result.plan)
```

## Yulang.GeneralDictionaryHeadlessPlans.lookup_plan

側: 健全性。

任意の上記入力でheadless lookupがresultを返すなら、result.inputsを使う既存variable lookupはresult.planを返す。

```lean
@Yulang.GeneralDictionaryHeadlessPlans.lookup_plan : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frame : Yulang.GeneralDictionaryEmissionPlans.Frame registry.roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles) (key : Nat)
  (inputs : Yulang.GeneralDictionaryVariableHeads.HeadlessInputs state root.demand)
  (result : Yulang.GeneralDictionaryHeadlessPlans.Result state root),
  Eq.{1} (Yulang.GeneralDictionaryHeadlessPlans.lookup registry checked frame root key inputs) (some.{0} result) →
    Eq.{1} (Yulang.GeneralDictionaryVariablePlans.lookup registry checked frame root key result.inputs)
      (some.{0} result.plan)
```

## Yulang.GeneralDictionaryHeadlessPlans.lookup_heads

側: 健全性。

任意の上記成功入力で、同key/roleの任意のvisible宣言に対して、計算されたhead vectorはその実宣言とcaptureのHeadDenotesを満たす。checked key一意性を使う。

```lean
@Yulang.GeneralDictionaryHeadlessPlans.lookup_heads : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frame : Yulang.GeneralDictionaryEmissionPlans.Frame registry.roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles) (key : Nat)
  (inputs : Yulang.GeneralDictionaryVariableHeads.HeadlessInputs state root.demand)
  (result : Yulang.GeneralDictionaryHeadlessPlans.Result state root),
  Eq.{1} (Yulang.GeneralDictionaryHeadlessPlans.lookup registry checked frame root key inputs) (some.{0} result) →
    ∀ (declaration : Yulang.GeneralDeclarations.Declaration),
      Membership.mem.{0, 0} registry.declarations declaration →
        Eq.{1} declaration.id key →
          Eq.{1} declaration.role root.demand.role →
            Yulang.GeneralDictionaryVariableHeads.heads registry.roles state root declaration
              (frame.capture declaration.id) result.inputs.head
```

## Yulang.GeneralDictionaryHeadlessPlans.lookup_exact

側: 完全性（明記した部分範囲）。

任意のchecked registry・state・frame・root・key・headless入力・resultで、lookup成功と独立MaterializesPlanが同値。同じ実宣言、全位置、実head/RHS、完全canonical子をまとめる。

```lean
@Yulang.GeneralDictionaryHeadlessPlans.lookup_exact : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frame : Yulang.GeneralDictionaryEmissionPlans.Frame registry.roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles) (key : Nat)
  (inputs : Yulang.GeneralDictionaryVariableHeads.HeadlessInputs state root.demand)
  (result : Yulang.GeneralDictionaryHeadlessPlans.Result state root),
  Eq.{1} (Yulang.GeneralDictionaryHeadlessPlans.lookup registry checked frame root key inputs) (some.{0} result) ↔
    Yulang.GeneralDictionaryHeadlessPlans.MaterializesPlan registry checked frame root key inputs result
```

## Yulang.GeneralDictionaryHeadlessPlans.head_compile_reorders

側: 補助。

任意のDeclarationReorders・state・capture・positional indexで、head compilerのOption結果は不変。

```lean
@Yulang.GeneralDictionaryHeadlessPlans.head_compile_reorders : ∀ {state : Yulang.GeneralSourceState.State}
  {first last : Yulang.GeneralDeclarations.Declaration},
  Yulang.GeneralRegistryReordering.DeclarationReorders first last →
    ∀ (capture : Yulang.GeneralDeclarationDemands.Capture) (index : Nat),
      Eq.{1} (Yulang.GeneralDictionaryVariableHeads.compileAt state first capture index)
        (Yulang.GeneralDictionaryVariableHeads.compileAt state last capture index)
```

## Yulang.GeneralDictionaryHeadlessPlans.head_build_reorders

側: 補助。

任意のDeclarationReorders・対応する宣言検査/role一致・capture・headless入力で、head builderの完全結果は不変。

```lean
@Yulang.GeneralDictionaryHeadlessPlans.head_build_reorders : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State} {first last : Yulang.GeneralDeclarations.Declaration}
  {constructors : Yulang.GeneralDeclarationPatterns.Constructors} {demand : Yulang.GeneralSourceState.Demand roles},
  Yulang.GeneralRegistryReordering.DeclarationReorders first last →
    ∀ (one : Yulang.GeneralDeclarations.DeclarationChecked constructors roles first)
      (two : Yulang.GeneralDeclarations.DeclarationChecked constructors roles last)
      (firstRole : Eq.{1} first.role demand.role) (lastRole : Eq.{1} last.role demand.role)
      (capture : Yulang.GeneralDeclarationDemands.Capture)
      (inputs : Yulang.GeneralDictionaryVariableHeads.HeadlessInputs state demand),
      Eq.{1} (Yulang.GeneralDictionaryVariableHeads.build first one firstRole capture inputs)
        (Yulang.GeneralDictionaryVariableHeads.build last two lastRole capture inputs)
```

## Yulang.GeneralDictionaryHeadlessPlans.lookup_reorders_forward

側: 補助。

任意の固定入力とchecked registry Reordersで、元のlookup成功は同じ完全resultを返す後のlookup成功へ移せる。

```lean
@Yulang.GeneralDictionaryHeadlessPlans.lookup_reorders_forward : ∀ {state : Yulang.GeneralSourceState.State}
  (constructors : Yulang.GeneralDeclarationPatterns.Constructors) (roles : Yulang.Roles.RoleDecls)
  (first last : List.{0} Yulang.GeneralDeclarations.Declaration)
  (one : Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := first })
  (two : Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := last }),
  Yulang.GeneralRegistryReordering.Reorders { constructors := constructors, roles := roles, declarations := first }
      { constructors := constructors, roles := roles, declarations := last } →
    ∀ (frame : Yulang.GeneralDictionaryEmissionPlans.Frame roles)
      (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (key : Nat)
      (inputs : Yulang.GeneralDictionaryVariableHeads.HeadlessInputs state root.demand)
      (result : Yulang.GeneralDictionaryHeadlessPlans.Result state root),
      Eq.{1}
          (Yulang.GeneralDictionaryHeadlessPlans.lookup
            { constructors := constructors, roles := roles, declarations := first } one frame root key inputs)
          (some.{0} result) →
        Eq.{1}
          (Yulang.GeneralDictionaryHeadlessPlans.lookup
            { constructors := constructors, roles := roles, declarations := last } two frame root key inputs)
          (some.{0} result)
```

## Yulang.GeneralDictionaryHeadlessPlans.lookup_reorders

側: 補助。

任意の固定入力とchecked registry Reordersで、headless lookupのOption結果全体は不変。

```lean
@Yulang.GeneralDictionaryHeadlessPlans.lookup_reorders : ∀ {state : Yulang.GeneralSourceState.State}
  (constructors : Yulang.GeneralDeclarationPatterns.Constructors) (roles : Yulang.Roles.RoleDecls)
  (first last : List.{0} Yulang.GeneralDeclarations.Declaration)
  (one : Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := first })
  (two : Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := last }),
  Yulang.GeneralRegistryReordering.Reorders { constructors := constructors, roles := roles, declarations := first }
      { constructors := constructors, roles := roles, declarations := last } →
    ∀ (frame : Yulang.GeneralDictionaryEmissionPlans.Frame roles)
      (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (key : Nat)
      (inputs : Yulang.GeneralDictionaryVariableHeads.HeadlessInputs state root.demand),
      Eq.{1}
        (Yulang.GeneralDictionaryHeadlessPlans.lookup
          { constructors := constructors, roles := roles, declarations := first } one frame root key inputs)
        (Yulang.GeneralDictionaryHeadlessPlans.lookup
          { constructors := constructors, roles := roles, declarations := last } two frame root key inputs)
```

## Yulang.GeneralDictionaryHeadlessPlans.lookup_none_exact

側: 補助。

任意のchecked registry・state・frame・root・key・headless入力で、lookupのnoneと独立MaterializesPlanを満たすresultの不存在は同値。部分materializationの範囲内の主張。

```lean
@Yulang.GeneralDictionaryHeadlessPlans.lookup_none_exact : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frame : Yulang.GeneralDictionaryEmissionPlans.Frame registry.roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles) (key : Nat)
  (inputs : Yulang.GeneralDictionaryVariableHeads.HeadlessInputs state root.demand),
  Eq.{1} (Yulang.GeneralDictionaryHeadlessPlans.lookup registry checked frame root key inputs) none.{0} ↔
    ∀ (result : Yulang.GeneralDictionaryHeadlessPlans.Result state root),
      ¬Yulang.GeneralDictionaryHeadlessPlans.MaterializesPlan registry checked frame root key inputs result
```

## Yulang.GeneralDictionaryHeadlessPreparation.prepare_node_exact

側: 補助。

任意のchecked registry・state・frames・root・key・headless入力・child recipes・treeで、node準備成功は、node lookup成功、全child準備成功、完全canonical occurrence列一致、返る木の形の一致と同値。

```lean
@Yulang.GeneralDictionaryHeadlessPreparation.prepare_node_exact : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles) (key : Nat)
  (inputs : Yulang.GeneralDictionaryVariableHeads.HeadlessInputs state root.demand)
  (children : List.{0} (Yulang.GeneralDictionaryHeadlessPreparation.Recipe registry.roles state))
  (tree : Yulang.GeneralDictionaryTransactions.Prepared registry.roles state),
  Eq.{1}
      (Yulang.GeneralDictionaryHeadlessPreparation.prepare registry checked frames
        (Yulang.GeneralDictionaryHeadlessPreparation.Recipe.node root key inputs children))
      (some.{0} tree) ↔
    Exists.{1} fun result =>
      Eq.{1} (Yulang.GeneralDictionaryHeadlessPlans.lookup registry checked (frames root) root key inputs)
          (some.{0} result) ∧
        Exists.{1} fun prepared =>
          Eq.{1}
              (List.mapM.{0, 0, 0} (Yulang.GeneralDictionaryHeadlessPreparation.prepare registry checked frames)
                children)
              (some.{0} prepared) ∧
            Eq.{1} (List.map.{0, 0} Yulang.GeneralDictionaryTransactions.Prepared.root prepared) result.plan.children ∧
              Eq.{1} tree (Yulang.GeneralDictionaryTransactions.Prepared.node root key result.plan.located prepared)
```

## Yulang.GeneralDictionaryHeadlessPreparation.prepare_root

側: 補助。

任意のchecked registry・state・frames・recipe・treeで準備が成功するなら、treeとrecipeのroot occurrenceは等しい。

```lean
@Yulang.GeneralDictionaryHeadlessPreparation.prepare_root : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (recipe : Yulang.GeneralDictionaryHeadlessPreparation.Recipe registry.roles state)
  (tree : Yulang.GeneralDictionaryTransactions.Prepared registry.roles state),
  Eq.{1} (Yulang.GeneralDictionaryHeadlessPreparation.prepare registry checked frames recipe) (some.{0} tree) →
    Eq.{1} tree.root recipe.root
```

## Yulang.GeneralDictionaryHeadlessPreparation.prepare_built

側: 健全性。

任意のchecked registry・state・frames・recipe・treeで準備が成功するなら、具体的VariableHeads.headsでBuiltとなる。再帰Heads前提は不要。

```lean
@Yulang.GeneralDictionaryHeadlessPreparation.prepare_built : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (recipe : Yulang.GeneralDictionaryHeadlessPreparation.Recipe registry.roles state)
  (tree : Yulang.GeneralDictionaryTransactions.Prepared registry.roles state),
  Eq.{1} (Yulang.GeneralDictionaryHeadlessPreparation.prepare registry checked frames recipe) (some.{0} tree) →
    Yulang.GeneralDictionaryVariableTransactions.Built registry checked frames
      (Yulang.GeneralDictionaryVariableHeads.heads registry.roles state) tree
```

## Yulang.GeneralDictionaryHeadlessPreparation.prepare_uniform

側: 健全性。

任意の上記成功入力で、一つのsource辞書witnessがreadbackを満たし、全batchの任意のmodelで具体的実head/RHSのEvidenceを満たす。

```lean
@Yulang.GeneralDictionaryHeadlessPreparation.prepare_uniform : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (recipe : Yulang.GeneralDictionaryHeadlessPreparation.Recipe registry.roles state)
  (tree : Yulang.GeneralDictionaryTransactions.Prepared registry.roles state),
  Eq.{1} (Yulang.GeneralDictionaryHeadlessPreparation.prepare registry checked frames recipe) (some.{0} tree) →
    Exists.{1} fun witness =>
      Yulang.GeneralSourceDictionaries.Readback recipe.root (Yulang.GeneralSourceDictionaries.erase tree.dictionary)
          witness ∧
        ∀ (assignment : Yulang.GeneralSourceState.Assignment),
          Yulang.GeneralSourceState.Models (Yulang.GeneralDictionaryBatchRecording.record tree.items) assignment →
            Yulang.GeneralSourceDictionaries.Evidence
              (Yulang.GeneralDictionaryVariableTransactions.SourceInstance registry checked frames
                (Yulang.GeneralDictionaryVariableHeads.heads registry.roles state) assignment)
              witness
```

## Yulang.GeneralDictionaryHeadlessRealization.normalized_var_occurs

側: 補助。

任意patternとbinderについて、patternの正規化がそのbare変数なら、そのbinderは正規化前のpatternにも語彙的に現れる。

```lean
Yulang.GeneralDictionaryHeadlessRealization.normalized_var_occurs : ∀
  (pattern : Yulang.GeneralDeclarationPatterns.Pattern) (binder : Nat),
  Eq.{1} (Yulang.GeneralDeclarationPatterns.normalize pattern) (Yulang.GeneralDeclarationPatterns.Pattern.var binder) →
    Membership.mem.{0, 0} pattern.variables binder
```

## Yulang.GeneralDictionaryHeadlessRealization.supported_input

側: 補助。

任意のchecked宣言・capture・demand・head vectorがHeadDenotesを満たすとき、任意の宣言input binderについて捕捉上下端のsource IDは等しく、そのbinderはoutputNamesに属さない。

```lean
@Yulang.GeneralDictionaryHeadlessRealization.supported_input : ∀ {state : Yulang.GeneralSourceState.State}
  {roles : Yulang.Roles.RoleDecls} {constructors : Yulang.GeneralDeclarationPatterns.Constructors}
  (declaration : Yulang.GeneralDeclarations.Declaration),
  Yulang.GeneralDeclarations.DeclarationChecked constructors roles declaration →
    ∀ (capture : Yulang.GeneralDeclarationDemands.Capture) (demand : Yulang.GeneralSourceState.Demand roles)
      (head : Fin (roles demand.role).arity → Yulang.Core.PresenceGeneration.TyTerm (Fin state.slots)),
      Yulang.GeneralDictionaryVariableHeads.HeadDenotes declaration capture demand head →
        ∀ (binder : Nat),
          Membership.mem.{0, 0} declaration.inputNames binder →
            Eq.{1} (Prod.fst.{0, 0} (capture.inputs binder)) (Prod.snd.{0, 0} (capture.inputs binder)) ∧
              ¬Membership.mem.{0, 0} declaration.outputNames binder
```

## Yulang.GeneralDictionaryHeadlessRealization.realizes

側: 健全性。

任意のchecked宣言・capture・demand・head vectorがHeadDenotesを満たすなら、任意のsource assignmentについて構成したvaluesがRealizesを満たす。外部Realizes前提なし。

```lean
@Yulang.GeneralDictionaryHeadlessRealization.realizes : ∀ {state : Yulang.GeneralSourceState.State}
  {roles : Yulang.Roles.RoleDecls} {constructors : Yulang.GeneralDeclarationPatterns.Constructors}
  (declaration : Yulang.GeneralDeclarations.Declaration),
  Yulang.GeneralDeclarations.DeclarationChecked constructors roles declaration →
    ∀ (capture : Yulang.GeneralDeclarationDemands.Capture) (demand : Yulang.GeneralSourceState.Demand roles)
      (head : Fin (roles demand.role).arity → Yulang.Core.PresenceGeneration.TyTerm (Fin state.slots)),
      Yulang.GeneralDictionaryVariableHeads.HeadDenotes declaration capture demand head →
        ∀ (assignment : Yulang.GeneralSourceState.Assignment),
          Yulang.GeneralDictionaryVariableRealization.Realizes declaration capture assignment
            (Yulang.GeneralDictionaryHeadlessRealization.values declaration capture assignment)
```

## Yulang.GeneralDictionaryHeadlessRealization.lookup_realization

側: 健全性。

任意のheadless lookup成功について一つの同key/roleのvisible宣言があり、任意assignmentで構成valuesはそのcaptureを実現し、各positional headの意味と一致する。さらにLocated記録のmodelなら各出力targetは実RHS変数値と同値。

```lean
@Yulang.GeneralDictionaryHeadlessRealization.lookup_realization : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frame : Yulang.GeneralDictionaryEmissionPlans.Frame registry.roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles) (key : Nat)
  (inputs : Yulang.GeneralDictionaryVariableHeads.HeadlessInputs state root.demand)
  (result : Yulang.GeneralDictionaryHeadlessPlans.Result state root),
  Eq.{1} (Yulang.GeneralDictionaryHeadlessPlans.lookup registry checked frame root key inputs) (some.{0} result) →
    Exists.{1} fun declaration =>
      Exists.{0} fun _present =>
        Eq.{1} declaration.id key ∧
          Eq.{1} declaration.role root.demand.role ∧
            ∀ (assignment : Yulang.GeneralSourceState.Assignment),
              Yulang.GeneralDictionaryVariableRealization.Realizes declaration (frame.capture declaration.id) assignment
                  (Yulang.GeneralDictionaryHeadlessRealization.values declaration (frame.capture declaration.id)
                    assignment) ∧
                (∀ (index : Fin (registry.roles root.demand.role).arity),
                    Exists.{1} fun pattern =>
                      Exists.{1} fun binder =>
                        Eq.{1} (getElem?.{0, 0, 0} declaration.head ↑index) (some.{0} pattern) ∧
                          Eq.{1} (Yulang.GeneralDeclarationPatterns.normalize pattern)
                              (Yulang.GeneralDeclarationPatterns.Pattern.var binder) ∧
                            Yulang.Common.Equivalent
                              (Yulang.GeneralDictionaryHeadlessRealization.values declaration
                                (frame.capture declaration.id) assignment binder)
                              (Yulang.Core.PresenceGeneration.TyTerm.eval.{0, 0} Yulang.Common.model assignment
                                (Yulang.GeneralDictionaryStateEquations.liftType state
                                  (result.plan.located.head index)))) ∧
                  (Yulang.GeneralSourceState.Models
                      (Yulang.GeneralDictionaryEquationRecording.record result.plan.located) assignment →
                    ∀ (index : Fin (List.length.{0} root.demand.outputs)),
                      Exists.{1} fun equation =>
                        Exists.{1} fun binder =>
                          Yulang.GeneralDictionaryAssociatedProvenance.Supplies registry.roles declaration
                              (getElem.{0, 0, 0} root.demand.outputs index ⋯).name
                              (Yulang.GeneralDictionaryAssociatedProvenance.Body.explicit equation) ∧
                            Eq.{1} (Yulang.GeneralDeclarationPatterns.normalize equation.rhs)
                                (Yulang.GeneralDeclarationPatterns.Pattern.var binder) ∧
                              Yulang.Common.Equivalent
                                (Prod.fst.{0, 0} (assignment (getElem.{0, 0, 0} root.demand.outputs index ⋯).target))
                                (Yulang.GeneralDictionaryHeadlessRealization.values declaration
                                  (frame.capture declaration.id) assignment binder))
```

## Yulang.GeneralDictionaryHeadlessSemanticOrder.realizes_reorders

側: 補助。

任意DeclarationReorders・capture・assignment・binderValuesについて、同じvaluesによるRealizesは前後で同値。

```lean
@Yulang.GeneralDictionaryHeadlessSemanticOrder.realizes_reorders : ∀
  {first last : Yulang.GeneralDeclarations.Declaration},
  Yulang.GeneralRegistryReordering.DeclarationReorders first last →
    ∀ (capture : Yulang.GeneralDeclarationDemands.Capture) (assignment : Yulang.GeneralSourceState.Assignment)
      (binderValues : Nat → Yulang.Common.Ty),
      Yulang.GeneralDictionaryVariableRealization.Realizes first capture assignment binderValues ↔
        Yulang.GeneralDictionaryVariableRealization.Realizes last capture assignment binderValues
```

## Yulang.GeneralDictionaryHeadlessSemanticOrder.instance_reorders_forward

側: 補助。

任意の同constructors/rolesのchecked registry Reorders・frames・assignment・root・key・childrenについて、独立なsource Instanceは同じvaluesとchildrenを保ち後のregistryへ移る。実行成功前提なし。

```lean
Yulang.GeneralDictionaryHeadlessSemanticOrder.instance_reorders_forward : ∀
  (constructors : Yulang.GeneralDeclarationPatterns.Constructors) (roles : Yulang.Roles.RoleDecls)
  (first last : List.{0} Yulang.GeneralDeclarations.Declaration)
  (one : Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := first })
  (two : Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := last }),
  Yulang.GeneralRegistryReordering.Reorders { constructors := constructors, roles := roles, declarations := first }
      { constructors := constructors, roles := roles, declarations := last } →
    ∀ (frames : Yulang.GeneralDictionaryTransactions.Frames roles) (assignment : Yulang.GeneralSourceState.Assignment)
      (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (key : Nat)
      (children : List.{0} (Yulang.GeneralSourceDictionaries.Occurrence roles)),
      Yulang.GeneralDictionaryHeadlessSourceEvidence.Instance
          { constructors := constructors, roles := roles, declarations := first } one frames assignment root key
          children →
        Yulang.GeneralDictionaryHeadlessSourceEvidence.Instance
          { constructors := constructors, roles := roles, declarations := last } two frames assignment root key children
```

## Yulang.GeneralDictionaryHeadlessSemanticOrder.instance_reorders

側: 補助。

上記の任意入力について独立source InstanceはReorders前後で同値。

```lean
Yulang.GeneralDictionaryHeadlessSemanticOrder.instance_reorders : ∀
  (constructors : Yulang.GeneralDeclarationPatterns.Constructors) (roles : Yulang.Roles.RoleDecls)
  (first last : List.{0} Yulang.GeneralDeclarations.Declaration)
  (one : Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := first })
  (two : Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := last }),
  Yulang.GeneralRegistryReordering.Reorders { constructors := constructors, roles := roles, declarations := first }
      { constructors := constructors, roles := roles, declarations := last } →
    ∀ (frames : Yulang.GeneralDictionaryTransactions.Frames roles) (assignment : Yulang.GeneralSourceState.Assignment)
      (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (key : Nat)
      (children : List.{0} (Yulang.GeneralSourceDictionaries.Occurrence roles)),
      Yulang.GeneralDictionaryHeadlessSourceEvidence.Instance
          { constructors := constructors, roles := roles, declarations := first } one frames assignment root key
          children ↔
        Yulang.GeneralDictionaryHeadlessSourceEvidence.Instance
          { constructors := constructors, roles := roles, declarations := last } two frames assignment root key children
```

## Yulang.GeneralDictionaryHeadlessSemanticOrder.evidence_reorders

側: 補助。

上記の任意入力と任意の有限source Dictionaryについて、独立Instanceに基づくEvidenceはReorders前後で同値。辞書自体は同じで、準備が作った辞書に限定しない。

```lean
Yulang.GeneralDictionaryHeadlessSemanticOrder.evidence_reorders : ∀
  (constructors : Yulang.GeneralDeclarationPatterns.Constructors) (roles : Yulang.Roles.RoleDecls)
  (first last : List.{0} Yulang.GeneralDeclarations.Declaration)
  (one : Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := first })
  (two : Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := last }),
  Yulang.GeneralRegistryReordering.Reorders { constructors := constructors, roles := roles, declarations := first }
      { constructors := constructors, roles := roles, declarations := last } →
    ∀ (frames : Yulang.GeneralDictionaryTransactions.Frames roles) (assignment : Yulang.GeneralSourceState.Assignment)
      (dictionary : Yulang.GeneralSourceDictionaries.Dictionary roles),
      Yulang.GeneralSourceDictionaries.Evidence
          (Yulang.GeneralDictionaryHeadlessSourceEvidence.Instance
            { constructors := constructors, roles := roles, declarations := first } one frames assignment)
          dictionary ↔
        Yulang.GeneralSourceDictionaries.Evidence
          (Yulang.GeneralDictionaryHeadlessSourceEvidence.Instance
            { constructors := constructors, roles := roles, declarations := last } two frames assignment)
          dictionary
```

## Yulang.GeneralDictionaryHeadlessSourceEvidence.source_instance

側: 健全性。

任意のchecked registry・state・frames・assignment・root・key・childrenで、具体的実head/RHSのSourceInstanceから、実宣言・全子・共有binderValues・各head区間・各RHS出力等式だけを述べる独立Instanceを導く。

```lean
@Yulang.GeneralDictionaryHeadlessSourceEvidence.source_instance : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (assignment : Yulang.GeneralSourceState.Assignment)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles) (key : Nat)
  (children : List.{0} (Yulang.GeneralSourceDictionaries.Occurrence registry.roles)),
  Yulang.GeneralDictionaryVariableTransactions.SourceInstance registry checked frames
      (Yulang.GeneralDictionaryVariableHeads.heads registry.roles state) assignment root key children →
    Yulang.GeneralDictionaryHeadlessSourceEvidence.Instance registry checked frames assignment root key children
```

## Yulang.GeneralDictionaryHeadlessSourceEvidence.prepare_uniform_source

側: 健全性。

任意の型欄のchecked registry・state・frames・recipe・成功treeについて、一つのsource辞書witnessがreadbackを満たし、全batchの任意modelで独立InstanceのEvidenceを満たす。辞書はmodelによらず固定、binderValuesはassignmentごとに構成する。

```lean
@Yulang.GeneralDictionaryHeadlessSourceEvidence.prepare_uniform_source : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (recipe : Yulang.GeneralDictionaryHeadlessPreparation.Recipe registry.roles state)
  (tree : Yulang.GeneralDictionaryTransactions.Prepared registry.roles state),
  Eq.{1} (Yulang.GeneralDictionaryHeadlessPreparation.prepare registry checked frames recipe) (some.{0} tree) →
    Exists.{1} fun witness =>
      Yulang.GeneralSourceDictionaries.Readback recipe.root (Yulang.GeneralSourceDictionaries.erase tree.dictionary)
          witness ∧
        ∀ (assignment : Yulang.GeneralSourceState.Assignment),
          Yulang.GeneralSourceState.Models (Yulang.GeneralDictionaryBatchRecording.record tree.items) assignment →
            Yulang.GeneralSourceDictionaries.Evidence
              (Yulang.GeneralDictionaryHeadlessSourceEvidence.Instance registry checked frames assignment) witness
```

## Yulang.GeneralDictionaryHeadlessSourceExamples.tree_uniform_source

側: 補助。

固定二node treeについて、一つのsource辞書witnessがreadbackを満たし、そのbatchの任意modelで独立InstanceのEvidenceが成立する。

```lean
Yulang.GeneralDictionaryHeadlessSourceExamples.tree_uniform_source : Exists.{1} fun witness =>
  Yulang.GeneralSourceDictionaries.Readback Yulang.GeneralDictionaryHeadlessExamples.recipe.root
      (Yulang.GeneralSourceDictionaries.erase Yulang.GeneralDictionaryHeadlessFixture.tree.dictionary) witness ∧
    ∀ (model : Yulang.GeneralSourceState.Assignment),
      Yulang.GeneralSourceState.Models
          (Yulang.GeneralDictionaryBatchRecording.record Yulang.GeneralDictionaryHeadlessFixture.tree.items) model →
        Yulang.GeneralSourceDictionaries.Evidence
          (Yulang.GeneralDictionaryHeadlessSourceEvidence.Instance Yulang.GeneralDictionaryHeadlessFixture.registry
            Yulang.GeneralDictionaryHeadlessFixture.registry_checked
            (fun x => Yulang.GeneralDictionaryHeadlessFixture.frame) model)
          witness
```

## Yulang.GeneralDictionaryHeadlessSourceExamples.tree_source_nonvacuous

側: 補助。

固定treeのbatchを満たす明示的assignmentがあり、そのassignmentでreadbackを満たす独立InstanceのEvidence witnessが存在する。SourceRecipe版では準備成功も同時に結論する。

```lean
Yulang.GeneralDictionaryHeadlessSourceExamples.tree_source_nonvacuous : Yulang.GeneralSourceState.Models
    (Yulang.GeneralDictionaryBatchRecording.record Yulang.GeneralDictionaryHeadlessFixture.tree.items)
    Yulang.GeneralDictionaryHeadlessFixture.assignment ∧
  Exists.{1} fun witness =>
    Yulang.GeneralSourceDictionaries.Readback Yulang.GeneralDictionaryHeadlessExamples.recipe.root
        (Yulang.GeneralSourceDictionaries.erase Yulang.GeneralDictionaryHeadlessFixture.tree.dictionary) witness ∧
      Yulang.GeneralSourceDictionaries.Evidence
        (Yulang.GeneralDictionaryHeadlessSourceEvidence.Instance Yulang.GeneralDictionaryHeadlessFixture.registry
          Yulang.GeneralDictionaryHeadlessFixture.registry_checked
          (fun x => Yulang.GeneralDictionaryHeadlessFixture.frame) Yulang.GeneralDictionaryHeadlessFixture.assignment)
        witness
```

## Yulang.GeneralDictionaryHeadlessSourceExamples.unequal_capture_realizes

側: 補助。

上下端identity100/101の固定captureは、all-int assignmentとall-int binderValuesの下で実終端宣言のRealizesを満たす。異なるIDが異なる型を強制するわけではない。

```lean
Yulang.GeneralDictionaryHeadlessSourceExamples.unequal_capture_realizes : Yulang.GeneralDictionaryVariableRealization.Realizes
  Yulang.GeneralDictionaryHeadlessFixture.leaf Yulang.GeneralDictionaryHeadlessExamples.unequalCapture
  Yulang.GeneralDictionaryHeadlessFixture.assignment Yulang.GeneralDictionaryHeadlessSourceExamples.binderValues
```

## Yulang.GeneralDictionaryHeadlessSourceExamples.unequal_source_instance

側: 補助。

固定の不等identity capture・終端child・key3・空childrenについて、実宣言と明示binderValuesが独立Instanceを満たす。

```lean
Yulang.GeneralDictionaryHeadlessSourceExamples.unequal_source_instance : Yulang.GeneralDictionaryHeadlessSourceEvidence.Instance
  Yulang.GeneralDictionaryHeadlessFixture.registry Yulang.GeneralDictionaryHeadlessFixture.registry_checked
  (fun x => Yulang.GeneralDictionaryHeadlessExamples.unequalFrame) Yulang.GeneralDictionaryHeadlessFixture.assignment
  Yulang.GeneralDictionaryHeadlessFixture.child 3 List.nil.{0}
```

## Yulang.GeneralDictionaryHeadlessSourceExamples.source_instance_while_lookup_defers

側: 補助。

固定不等identity captureで独立Instanceが成立する一方、headless lookupはnoneになる。独立source意味への健全性に無条件の逆向きはない。

```lean
Yulang.GeneralDictionaryHeadlessSourceExamples.source_instance_while_lookup_defers : Yulang.GeneralDictionaryHeadlessSourceEvidence.Instance
    Yulang.GeneralDictionaryHeadlessFixture.registry Yulang.GeneralDictionaryHeadlessFixture.registry_checked
    (fun x => Yulang.GeneralDictionaryHeadlessExamples.unequalFrame) Yulang.GeneralDictionaryHeadlessFixture.assignment
    Yulang.GeneralDictionaryHeadlessFixture.child 3 List.nil.{0} ∧
  Eq.{1}
    (Yulang.GeneralDictionaryHeadlessPlans.lookup Yulang.GeneralDictionaryHeadlessFixture.registry
      Yulang.GeneralDictionaryHeadlessFixture.registry_checked Yulang.GeneralDictionaryHeadlessExamples.unequalFrame
      Yulang.GeneralDictionaryHeadlessFixture.child 3 Yulang.GeneralDictionaryHeadlessFixture.childHeadless)
    none.{0}
```

## Yulang.GeneralDictionaryHeadlessSourceExamples.unequal_leaf_preparation_defers

側: 補助。

同じ固定不等identity captureで終端recipeの準備もnoneとなる。

```lean
Yulang.GeneralDictionaryHeadlessSourceExamples.unequal_leaf_preparation_defers : Eq.{1}
  (Yulang.GeneralDictionaryHeadlessPreparation.prepare Yulang.GeneralDictionaryHeadlessFixture.registry
    Yulang.GeneralDictionaryHeadlessFixture.registry_checked
    (fun x => Yulang.GeneralDictionaryHeadlessExamples.unequalFrame)
    Yulang.GeneralDictionaryHeadlessExamples.leafRecipe)
  none.{0}
```

## Yulang.GeneralDictionarySourceRecipe.localize_root

側: 補助。

任意state・source-only recipe・localize成功結果について、元と計算後のroot occurrenceは同じ。

```lean
@Yulang.GeneralDictionarySourceRecipe.localize_root : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralSourceState.State) (recipe : Yulang.GeneralDictionarySourceRecipe.Recipe roles)
  (localized : Yulang.GeneralDictionaryHeadlessPreparation.Recipe roles state),
  Eq.{1} (Yulang.GeneralDictionarySourceRecipe.localize state recipe) (some.{0} localized) →
    Eq.{1} localized.root recipe.root
```

## Yulang.GeneralDictionarySourceRecipe.prepare_exact

側: 補助（操作分解）。

任意の型欄のregistry・state・frames・recipe・treeについて、準備成功と右辺の契約が同値。HeadlessExactnessでは独立Materializes、SourceRecipeではlocalizeと既存準備の明示的な二段階成功を述べる。後者を独立意味論のiffとは呼ばない。

```lean
Yulang.GeneralDictionarySourceRecipe.prepare_exact : ∀ (registry : Yulang.GeneralDeclarations.Registry)
  (checked : Yulang.GeneralDeclarations.Checked registry) (state : Yulang.GeneralSourceState.State)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (recipe : Yulang.GeneralDictionarySourceRecipe.Recipe registry.roles)
  (tree : Yulang.GeneralDictionaryTransactions.Prepared registry.roles state),
  Eq.{1} (Yulang.GeneralDictionarySourceRecipe.prepare registry checked state frames recipe) (some.{0} tree) ↔
    Exists.{1} fun localized =>
      Eq.{1} (Yulang.GeneralDictionarySourceRecipe.localize state recipe) (some.{0} localized) ∧
        Eq.{1} (Yulang.GeneralDictionaryHeadlessPreparation.prepare registry checked frames localized) (some.{0} tree)
```

## Yulang.GeneralDictionarySourceRecipe.prepare_uniform_source

側: 健全性。

任意の型欄のchecked registry・state・frames・recipe・成功treeについて、一つのsource辞書witnessがreadbackを満たし、全batchの任意modelで独立InstanceのEvidenceを満たす。辞書はmodelによらず固定、binderValuesはassignmentごとに構成する。

```lean
Yulang.GeneralDictionarySourceRecipe.prepare_uniform_source : ∀ (registry : Yulang.GeneralDeclarations.Registry)
  (checked : Yulang.GeneralDeclarations.Checked registry) (state : Yulang.GeneralSourceState.State)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (recipe : Yulang.GeneralDictionarySourceRecipe.Recipe registry.roles)
  (tree : Yulang.GeneralDictionaryTransactions.Prepared registry.roles state),
  Eq.{1} (Yulang.GeneralDictionarySourceRecipe.prepare registry checked state frames recipe) (some.{0} tree) →
    Exists.{1} fun witness =>
      Yulang.GeneralSourceDictionaries.Readback recipe.root (Yulang.GeneralSourceDictionaries.erase tree.dictionary)
          witness ∧
        ∀ (assignment : Yulang.GeneralSourceState.Assignment),
          Yulang.GeneralSourceState.Models (Yulang.GeneralDictionaryBatchRecording.record tree.items) assignment →
            Yulang.GeneralSourceDictionaries.Evidence
              (Yulang.GeneralDictionaryHeadlessSourceEvidence.Instance registry checked frames assignment) witness
```

## Yulang.GeneralDictionarySourceRecipe.prepare_reorders

側: 補助。

任意の同じconstructors/roles・二つのchecked宣言列・許されたReorders・state・frames・recipeについて、準備のOption結果全体が等しい。成功だけでなくnoneも保存する。

```lean
Yulang.GeneralDictionarySourceRecipe.prepare_reorders : ∀
  (constructors : Yulang.GeneralDeclarationPatterns.Constructors) (roles : Yulang.Roles.RoleDecls)
  (first last : List.{0} Yulang.GeneralDeclarations.Declaration)
  (one : Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := first })
  (two : Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := last }),
  Yulang.GeneralRegistryReordering.Reorders { constructors := constructors, roles := roles, declarations := first }
      { constructors := constructors, roles := roles, declarations := last } →
    ∀ (state : Yulang.GeneralSourceState.State) (frames : Yulang.GeneralDictionaryTransactions.Frames roles)
      (recipe : Yulang.GeneralDictionarySourceRecipe.Recipe roles),
      Eq.{1}
        (Yulang.GeneralDictionarySourceRecipe.prepare
          { constructors := constructors, roles := roles, declarations := first } one state frames recipe)
        (Yulang.GeneralDictionarySourceRecipe.prepare
          { constructors := constructors, roles := roles, declarations := last } two state frames recipe)
```

## Yulang.GeneralDictionarySourceRecipeExamples.leaf_localizes

側: 補助。

位置を一切持たない固定終端source recipeをlocalizeすると、既存の検証済みheadless終端recipeが得られる。

```lean
Yulang.GeneralDictionarySourceRecipeExamples.leaf_localizes : Eq.{1}
  (Yulang.GeneralDictionarySourceRecipe.localize Yulang.GeneralDictionaryHeadlessFixture.state
    Yulang.GeneralDictionarySourceRecipeExamples.leafRecipe)
  (some.{0} Yulang.GeneralDictionaryHeadlessExamples.leafRecipe)
```

## Yulang.GeneralDictionarySourceRecipeExamples.tree_localizes

側: 補助。

位置を一切持たない固定二node source recipeをlocalizeすると、既存の検証済みheadless二node recipeが得られる。

```lean
Yulang.GeneralDictionarySourceRecipeExamples.tree_localizes : Eq.{1}
  (Yulang.GeneralDictionarySourceRecipe.localize Yulang.GeneralDictionaryHeadlessFixture.state
    Yulang.GeneralDictionarySourceRecipeExamples.recipe)
  (some.{0} Yulang.GeneralDictionaryHeadlessExamples.recipe)
```

## Yulang.GeneralDictionarySourceRecipeExamples.tree_prepared

側: 補助。

固定の実producerと終端leafのrecipeから、全childと二つの根出力を保持するPrepared木が返る。

```lean
Yulang.GeneralDictionarySourceRecipeExamples.tree_prepared : Eq.{1}
  (Yulang.GeneralDictionarySourceRecipe.prepare Yulang.GeneralDictionaryHeadlessFixture.registry
    Yulang.GeneralDictionaryHeadlessFixture.registry_checked Yulang.GeneralDictionaryHeadlessFixture.state
    (fun x => Yulang.GeneralDictionaryHeadlessFixture.frame) Yulang.GeneralDictionarySourceRecipeExamples.recipe)
  (some.{0} Yulang.GeneralDictionaryHeadlessFixture.tree)
```

## Yulang.GeneralDictionarySourceRecipeExamples.tree_uniform_source

側: 補助。

固定二node treeについて、一つのsource辞書witnessがreadbackを満たし、そのbatchの任意modelで独立InstanceのEvidenceが成立する。

```lean
Yulang.GeneralDictionarySourceRecipeExamples.tree_uniform_source : Exists.{1} fun witness =>
  Yulang.GeneralSourceDictionaries.Readback Yulang.GeneralDictionarySourceRecipeExamples.recipe.root
      (Yulang.GeneralSourceDictionaries.erase Yulang.GeneralDictionaryHeadlessFixture.tree.dictionary) witness ∧
    ∀ (model : Yulang.GeneralSourceState.Assignment),
      Yulang.GeneralSourceState.Models
          (Yulang.GeneralDictionaryBatchRecording.record Yulang.GeneralDictionaryHeadlessFixture.tree.items) model →
        Yulang.GeneralSourceDictionaries.Evidence
          (Yulang.GeneralDictionaryHeadlessSourceEvidence.Instance Yulang.GeneralDictionaryHeadlessFixture.registry
            Yulang.GeneralDictionaryHeadlessFixture.registry_checked
            (fun x => Yulang.GeneralDictionaryHeadlessFixture.frame) model)
          witness
```

## Yulang.GeneralDictionarySourceRecipeExamples.tree_source_nonvacuous

側: 補助。

固定treeのbatchを満たす明示的assignmentがあり、そのassignmentでreadbackを満たす独立InstanceのEvidence witnessが存在する。SourceRecipe版では準備成功も同時に結論する。

```lean
Yulang.GeneralDictionarySourceRecipeExamples.tree_source_nonvacuous : Eq.{1}
    (Yulang.GeneralDictionarySourceRecipe.prepare Yulang.GeneralDictionaryHeadlessFixture.registry
      Yulang.GeneralDictionaryHeadlessFixture.registry_checked Yulang.GeneralDictionaryHeadlessFixture.state
      (fun x => Yulang.GeneralDictionaryHeadlessFixture.frame) Yulang.GeneralDictionarySourceRecipeExamples.recipe)
    (some.{0} Yulang.GeneralDictionaryHeadlessFixture.tree) ∧
  Yulang.GeneralSourceState.Models
      (Yulang.GeneralDictionaryBatchRecording.record Yulang.GeneralDictionaryHeadlessFixture.tree.items)
      Yulang.GeneralDictionaryHeadlessFixture.assignment ∧
    Exists.{1} fun witness =>
      Yulang.GeneralSourceDictionaries.Readback Yulang.GeneralDictionarySourceRecipeExamples.recipe.root
          (Yulang.GeneralSourceDictionaries.erase Yulang.GeneralDictionaryHeadlessFixture.tree.dictionary) witness ∧
        Yulang.GeneralSourceDictionaries.Evidence
          (Yulang.GeneralDictionaryHeadlessSourceEvidence.Instance Yulang.GeneralDictionaryHeadlessFixture.registry
            Yulang.GeneralDictionaryHeadlessFixture.registry_checked
            (fun x => Yulang.GeneralDictionaryHeadlessFixture.frame) Yulang.GeneralDictionaryHeadlessFixture.assignment)
          witness
```

## Yulang.GeneralDictionarySourceRecipeExamples.absent_output_location_defers

側: 補助。

宣言上有効なoutput名でも、target999がsource mapに存在しない固定demandのlocateはnoneとなる。

```lean
Yulang.GeneralDictionarySourceRecipeExamples.absent_output_location_defers : Eq.{1}
  (Yulang.GeneralDictionaryHeadlessLocations.locate Yulang.GeneralDictionaryHeadlessFixture.state
    Yulang.GeneralDictionarySourceRecipeExamples.absentOutputDemand)
  none.{0}
```

## Yulang.GeneralDictionarySourceRecipeExamples.absent_output_localization_defers

側: 補助。

そのtarget999を持つ固定source recipe全体のlocalizeはnoneとなる。

```lean
Yulang.GeneralDictionarySourceRecipeExamples.absent_output_localization_defers : Eq.{1}
  (Yulang.GeneralDictionarySourceRecipe.localize Yulang.GeneralDictionaryHeadlessFixture.state
    Yulang.GeneralDictionarySourceRecipeExamples.absentOutputRecipe)
  none.{0}
```

## Yulang.GeneralDictionarySourceRecipeExamples.absent_output_preparation_defers

側: 補助。

そのtarget999を持つ固定source recipe全体の準備はnoneとなる。

```lean
Yulang.GeneralDictionarySourceRecipeExamples.absent_output_preparation_defers : Eq.{1}
  (Yulang.GeneralDictionarySourceRecipe.prepare Yulang.GeneralDictionaryHeadlessFixture.registry
    Yulang.GeneralDictionaryHeadlessFixture.registry_checked Yulang.GeneralDictionaryHeadlessFixture.state
    (fun x => Yulang.GeneralDictionaryHeadlessFixture.frame)
    Yulang.GeneralDictionarySourceRecipeExamples.absentOutputRecipe)
  none.{0}
```

## Yulang.GeneralDictionarySourceRecipeExamples.omitted_child_defers

側: 補助。

固定producerの実childをrecipeから落とすと準備はnoneとなる。位置を自動計算する版でも子の完全性を弱めない。

```lean
Yulang.GeneralDictionarySourceRecipeExamples.omitted_child_defers : Eq.{1}
  (Yulang.GeneralDictionarySourceRecipe.prepare Yulang.GeneralDictionaryHeadlessFixture.registry
    Yulang.GeneralDictionaryHeadlessFixture.registry_checked Yulang.GeneralDictionaryHeadlessFixture.state
    (fun x => Yulang.GeneralDictionaryHeadlessFixture.frame)
    (Yulang.GeneralDictionarySourceRecipe.Recipe.node Yulang.GeneralDictionaryHeadlessFixture.root 2 List.nil.{0}))
  none.{0}
```
