# Yulang cycle126 公開定理一覧

対象は17モジュール、109公開定理（健全性 31、完全性 10、補助 68）。定理数は B4 の閉鎖数ではない。General B4 は12/12未充足のままである。

ここでの完全性は、明示的な前提と対応する独立関係に対する部分実装の iff を指す。capture の発見・候補選択・一般の head 照合・任意の役割意味論・一般 B4 の完全性を意味しない。互換性は明示された旧実装の成功保存に限る。全モデルについての結論は、モデル自体の存在を含まない。固定回帰例は任意入力の成功を主張しない。

109件すべての公理依存監査は成功（終了コード0）。各項目に監査結果を原文のまま併記する。依存公理は propext、Classical.choice、Quot.sound の範囲であり、sorryAx はない。

型は final-signatures.log の #check @ 出力を省略せず転記している。Lean 出力に元からある ⋯ はそのまま保持し、こちらで量化子・前提を削除していない。

## 1. output_requires_nonempty_child

- 分類: 健全性
- ソースモジュール: Yulang.GeneralDictionaryBinderOnlyBoundary
- ソースファイル: lean/Yulang/GeneralDictionaryBinderOnlyBoundary.lean
- 命題: 検査済み宣言と与えた capture に対する出力束縛子専用 Interpreted があり、根の出力位置を一つ指定できるなら、生成された子の中に出力要求が空でない子が存在する。

### カーネル確認済みの型（#check @）

```lean
@Yulang.GeneralDictionaryBinderOnlyBoundary.output_requires_nonempty_child : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State} {constructors : Yulang.GeneralDeclarationPatterns.Constructors}
  (declaration : Yulang.GeneralDeclarations.Declaration)
  (checked : Yulang.GeneralDeclarations.DeclarationChecked constructors roles declaration)
  (frame : Yulang.GeneralDictionaryEmissionPlans.Frame roles) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (located : Yulang.GeneralDictionaryStateEquations.Located state root.demand),
  Yulang.GeneralDictionaryOutputBinderTerms.Interpreted declaration (frame.capture declaration.id) located →
    ∀ (index : Fin root.demand.outputs.length),
      ∃ child,
        child ∈ Yulang.GeneralDictionaryEmissionPlans.children frame root declaration checked ∧
          child.demand.outputs ≠ []
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryBinderOnlyBoundary.output_requires_nonempty_child' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 2. built_root_outputs_empty

- 分類: 健全性
- ソースモジュール: Yulang.GeneralDictionaryBinderOnlyBoundary
- ソースファイル: lean/Yulang/GeneralDictionaryBinderOnlyBoundary.lean
- 命題: 検査済み registry、明示的 frames／heads に対して出力束縛子専用の Built を満たす有限準備木では、根の出力要求は空である。

### カーネル確認済みの型（#check @）

```lean
@Yulang.GeneralDictionaryBinderOnlyBoundary.built_root_outputs_empty : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (heads : Yulang.GeneralDictionaryComputedOutputPlans.HeadInstances registry.roles state)
  (tree : Yulang.GeneralDictionaryTransactions.Prepared registry.roles state),
  Yulang.GeneralDictionaryComputedTransactions.Built registry checked frames heads tree → tree.root.demand.outputs = []
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryBinderOnlyBoundary.built_root_outputs_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 3. registry_checked

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryComputedOutputExamples
- ソースファイル: lean/Yulang/GeneralDictionaryComputedOutputExamples.lean
- 命題: 固定例の registry は Checked を満たす。

### カーネル確認済みの型（#check @）

```lean
Yulang.GeneralDictionaryComputedOutputExamples.registry_checked : Yulang.GeneralDeclarations.Checked
  Yulang.GeneralDictionaryComputedOutputExamples.registry
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryComputedOutputExamples.registry_checked' depends on axioms: [propext, Quot.sound]
```

## 4. actual_lookup

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryComputedOutputExamples
- ソースファイル: lean/Yulang/GeneralDictionaryComputedOutputExamples.lean
- 命題: 固定例で根・key 2・inputs に対する lookup は指定した result を返す。

### カーネル確認済みの型（#check @）

```lean
Yulang.GeneralDictionaryComputedOutputExamples.actual_lookup : Yulang.GeneralDictionaryComputedOutputPlans.lookup
    Yulang.GeneralDictionaryComputedOutputExamples.registry
    Yulang.GeneralDictionaryComputedOutputExamples.registry_checked Yulang.GeneralDictionaryComputedOutputExamples.frame
    Yulang.GeneralDictionaryComputedOutputExamples.root 2 Yulang.GeneralDictionaryBinderLocationExamples.inputs =
  some Yulang.GeneralDictionaryComputedOutputExamples.result
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryComputedOutputExamples.actual_lookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 5. absent_key_defers

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryComputedOutputExamples
- ソースファイル: lean/Yulang/GeneralDictionaryComputedOutputExamples.lean
- 命題: 固定例で存在しない key 99 の lookup は none を返す。

### カーネル確認済みの型（#check @）

```lean
Yulang.GeneralDictionaryComputedOutputExamples.absent_key_defers : Yulang.GeneralDictionaryComputedOutputPlans.lookup
    Yulang.GeneralDictionaryComputedOutputExamples.registry
    Yulang.GeneralDictionaryComputedOutputExamples.registry_checked Yulang.GeneralDictionaryComputedOutputExamples.frame
    Yulang.GeneralDictionaryComputedOutputExamples.root 99 Yulang.GeneralDictionaryBinderLocationExamples.inputs =
  none
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryComputedOutputExamples.absent_key_defers' depends on axioms: [propext, Quot.sound]
```

## 6. wrong_role_defers

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryComputedOutputExamples
- ソースファイル: lean/Yulang/GeneralDictionaryComputedOutputExamples.lean
- 命題: 固定例で要求と役割が異なる key 1 の lookup は none を返す。

### カーネル確認済みの型（#check @）

```lean
Yulang.GeneralDictionaryComputedOutputExamples.wrong_role_defers : Yulang.GeneralDictionaryComputedOutputPlans.lookup
    Yulang.GeneralDictionaryComputedOutputExamples.registry
    Yulang.GeneralDictionaryComputedOutputExamples.registry_checked Yulang.GeneralDictionaryComputedOutputExamples.frame
    Yulang.GeneralDictionaryComputedOutputExamples.root 1 Yulang.GeneralDictionaryBinderLocationExamples.inputs =
  none
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryComputedOutputExamples.wrong_role_defers' depends on axioms: [propext, Quot.sound]
```

## 7. computes_repeated_outputs

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryComputedOutputExamples
- ソースファイル: lean/Yulang/GeneralDictionaryComputedOutputExamples.lean
- 命題: 固定例の lookup は二つの出力位置の双方に slot 2 の変数を返す。

### カーネル確認済みの型（#check @）

```lean
Yulang.GeneralDictionaryComputedOutputExamples.computes_repeated_outputs : Option.map
    (fun r => [r.located.output ⟨0, ⋯⟩, r.located.output ⟨1, ⋯⟩])
    (Yulang.GeneralDictionaryComputedOutputPlans.lookup Yulang.GeneralDictionaryComputedOutputExamples.registry
      Yulang.GeneralDictionaryComputedOutputExamples.registry_checked
      Yulang.GeneralDictionaryComputedOutputExamples.frame Yulang.GeneralDictionaryComputedOutputExamples.root 2
      Yulang.GeneralDictionaryBinderLocationExamples.inputs) =
  some [Yulang.Core.PresenceGeneration.TyTerm.var 2, Yulang.Core.PresenceGeneration.TyTerm.var 2]
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryComputedOutputExamples.computes_repeated_outputs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 8. retains_distinct_targets

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryComputedOutputExamples
- ソースファイル: lean/Yulang/GeneralDictionaryComputedOutputExamples.lean
- 命題: 固定例の二出力位置の target を source ID に戻すと [3, 4] となり、同じ出力項でも要求先を区別して保持する。

### カーネル確認済みの型（#check @）

```lean
Yulang.GeneralDictionaryComputedOutputExamples.retains_distinct_targets : Option.map
    (fun r =>
      [Yulang.GeneralDictionaryOutputBinderExamples.state.source (r.located.target ⟨0, ⋯⟩),
        Yulang.GeneralDictionaryOutputBinderExamples.state.source (r.located.target ⟨1, ⋯⟩)])
    (Yulang.GeneralDictionaryComputedOutputPlans.lookup Yulang.GeneralDictionaryComputedOutputExamples.registry
      Yulang.GeneralDictionaryComputedOutputExamples.registry_checked
      Yulang.GeneralDictionaryComputedOutputExamples.frame Yulang.GeneralDictionaryComputedOutputExamples.root 2
      Yulang.GeneralDictionaryBinderLocationExamples.inputs) =
  some [3, 4]
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryComputedOutputExamples.retains_distinct_targets' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 9. supplies_complete_plan

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryComputedOutputExamples
- ソースファイル: lean/Yulang/GeneralDictionaryComputedOutputExamples.lean
- 命題: 固定例の result.children は根・key 2 の Plan を満たす。

### カーネル確認済みの型（#check @）

```lean
Yulang.GeneralDictionaryComputedOutputExamples.supplies_complete_plan : Yulang.GeneralDictionaryEmissionPlans.Plan
  Yulang.GeneralDictionaryComputedOutputExamples.registry
  Yulang.GeneralDictionaryComputedOutputExamples.registry_checked Yulang.GeneralDictionaryComputedOutputExamples.frame
  Yulang.GeneralDictionaryComputedOutputExamples.root 2 Yulang.GeneralDictionaryComputedOutputExamples.result.children
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryComputedOutputExamples.supplies_complete_plan' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 10. supplies_concrete_terms

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryComputedOutputExamples
- ソースファイル: lean/Yulang/GeneralDictionaryComputedOutputExamples.lean
- 命題: 任意の heads について固定例の root head が当該 HeadInstances を満たすと仮定すれば、result.located は Terms を満たす。

### カーネル確認済みの型（#check @）

```lean
Yulang.GeneralDictionaryComputedOutputExamples.supplies_concrete_terms : ∀
  (heads :
    Yulang.GeneralDictionaryComputedOutputPlans.HeadInstances Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralDictionaryOutputBinderExamples.state),
  heads Yulang.GeneralDictionaryComputedOutputExamples.root Yulang.GeneralDictionaryOutputBinderExamples.binderWrap
      Yulang.GeneralDictionaryOutputBinderExamples.capture Yulang.GeneralDictionaryBinderLocationExamples.inputs.head →
    Yulang.GeneralDictionaryComputedOutputPlans.Terms Yulang.GeneralDictionaryComputedOutputExamples.registry
      (fun x => Yulang.GeneralDictionaryComputedOutputExamples.frame) heads
      Yulang.GeneralDictionaryComputedOutputExamples.root 2
      Yulang.GeneralDictionaryComputedOutputExamples.result.located
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryComputedOutputExamples.supplies_concrete_terms' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 11. same_visible_declaration

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryComputedOutputExamples
- ソースファイル: lean/Yulang/GeneralDictionaryComputedOutputExamples.lean
- 命題: 固定例では、ID 2・要求役割が一致する同一の可視宣言が存在し、その宣言由来の OutputPlan と capture に対する出力束縛子専用 Interpreted が同時に成り立つ。

### カーネル確認済みの型（#check @）

```lean
Yulang.GeneralDictionaryComputedOutputExamples.same_visible_declaration : ∃ declaration _present,
  declaration.id = 2 ∧
    declaration.role = Yulang.GeneralDictionaryComputedOutputExamples.root.demand.role ∧
      Yulang.GeneralDictionaryPlannedOutputs.OutputPlan Yulang.GeneralDictionaryComputedOutputExamples.registry
          Yulang.GeneralDictionaryComputedOutputExamples.registry_checked
          Yulang.GeneralDictionaryComputedOutputExamples.frame Yulang.GeneralDictionaryComputedOutputExamples.root 2
          (Yulang.GeneralDictionaryComputedOutputExamples.result.children,
            Yulang.GeneralDictionaryAssociatedProvenance.outputs Yulang.GeneralDeclarationExamples.roles declaration
              Yulang.GeneralDictionaryComputedOutputExamples.root.demand) ∧
        Yulang.GeneralDictionaryOutputBinderTerms.Interpreted declaration
          (Yulang.GeneralDictionaryComputedOutputExamples.frame.capture declaration.id)
          Yulang.GeneralDictionaryComputedOutputExamples.result.located
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryComputedOutputExamples.same_visible_declaration' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 12. nonidentity_lookup

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryComputedOutputExamples
- ソースファイル: lean/Yulang/GeneralDictionaryComputedOutputExamples.lean
- 命題: source map が非恒等の固定例でも、key 2 の lookup は指定した shiftedResult を返す。

### カーネル確認済みの型（#check @）

```lean
Yulang.GeneralDictionaryComputedOutputExamples.nonidentity_lookup : Yulang.GeneralDictionaryComputedOutputPlans.lookup
    Yulang.GeneralDictionaryComputedOutputExamples.registry
    Yulang.GeneralDictionaryComputedOutputExamples.registry_checked
    Yulang.GeneralDictionaryComputedOutputExamples.shiftedFrame
    Yulang.GeneralDictionaryComputedOutputExamples.shiftedRoot 2
    Yulang.GeneralDictionaryBinderLocationExamples.shiftedInputs =
  some Yulang.GeneralDictionaryComputedOutputExamples.shiftedResult
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryComputedOutputExamples.nonidentity_lookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 13. nonidentity_computed_output

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryComputedOutputExamples
- ソースファイル: lean/Yulang/GeneralDictionaryComputedOutputExamples.lean
- 命題: 非恒等 source map の固定例で、lookup の先頭出力項を持ち上げると source ID 12 の変数となる。

### カーネル確認済みの型（#check @）

```lean
Yulang.GeneralDictionaryComputedOutputExamples.nonidentity_computed_output : Option.map
    (fun r =>
      Yulang.GeneralDictionaryStateEquations.liftType Yulang.GeneralDictionaryBinderLocationExamples.shiftedState
        (r.located.output ⟨0, ⋯⟩))
    (Yulang.GeneralDictionaryComputedOutputPlans.lookup Yulang.GeneralDictionaryComputedOutputExamples.registry
      Yulang.GeneralDictionaryComputedOutputExamples.registry_checked
      Yulang.GeneralDictionaryComputedOutputExamples.shiftedFrame
      Yulang.GeneralDictionaryComputedOutputExamples.shiftedRoot 2
      Yulang.GeneralDictionaryBinderLocationExamples.shiftedInputs) =
  some (Yulang.Core.PresenceGeneration.TyTerm.var 12)
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryComputedOutputExamples.nonidentity_computed_output' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 14. nonidentity_repeated_targets

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryComputedOutputExamples
- ソースファイル: lean/Yulang/GeneralDictionaryComputedOutputExamples.lean
- 命題: 非恒等 source map の固定例で、二つの出力先を source ID に戻すと [13, 14] となる。

### カーネル確認済みの型（#check @）

```lean
Yulang.GeneralDictionaryComputedOutputExamples.nonidentity_repeated_targets : Option.map
    (fun r =>
      [Yulang.GeneralDictionaryBinderLocationExamples.shiftedState.source (r.located.target ⟨0, ⋯⟩),
        Yulang.GeneralDictionaryBinderLocationExamples.shiftedState.source (r.located.target ⟨1, ⋯⟩)])
    (Yulang.GeneralDictionaryComputedOutputPlans.lookup Yulang.GeneralDictionaryComputedOutputExamples.registry
      Yulang.GeneralDictionaryComputedOutputExamples.registry_checked
      Yulang.GeneralDictionaryComputedOutputExamples.shiftedFrame
      Yulang.GeneralDictionaryComputedOutputExamples.shiftedRoot 2
      Yulang.GeneralDictionaryBinderLocationExamples.shiftedInputs) =
  some [13, 14]
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryComputedOutputExamples.nonidentity_repeated_targets' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 15. missing_binder_defers

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryComputedOutputExamples
- ソースファイル: lean/Yulang/GeneralDictionaryComputedOutputExamples.lean
- 命題: 出力束縛子の source が欠ける固定例の lookup は none を返す。

### カーネル確認済みの型（#check @）

```lean
Yulang.GeneralDictionaryComputedOutputExamples.missing_binder_defers : Yulang.GeneralDictionaryComputedOutputPlans.lookup
    Yulang.GeneralDictionaryComputedOutputExamples.registry
    Yulang.GeneralDictionaryComputedOutputExamples.registry_checked
    Yulang.GeneralDictionaryComputedOutputExamples.absentFrame
    Yulang.GeneralDictionaryComputedOutputExamples.shiftedRoot 2
    Yulang.GeneralDictionaryBinderLocationExamples.shiftedInputs =
  none
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryComputedOutputExamples.missing_binder_defers' depends on axioms: [propext, Quot.sound]
```

## 16. lookup_exact

- 分類: 完全性
- ソースモジュール: Yulang.GeneralDictionaryComputedOutputPlans
- ソースファイル: lean/Yulang/GeneralDictionaryComputedOutputPlans.lean
- 命題: 任意の検査済み registry・frame・根・key・inputs・result について、出力束縛子専用 lookup がその result を返すことと、可視宣言が存在し、ID と役割が一致し、その capture で build が result.located を返し、子列が当該宣言の生成列に等しいことは同値。

### カーネル確認済みの型（#check @）

```lean
@Yulang.GeneralDictionaryComputedOutputPlans.lookup_exact : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frame : Yulang.GeneralDictionaryEmissionPlans.Frame registry.roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles) (key : Nat)
  (inputs : Yulang.GeneralDictionaryBinderLocations.Inputs state root.demand)
  (result : Yulang.GeneralDictionaryComputedOutputPlans.Result state root),
  Yulang.GeneralDictionaryComputedOutputPlans.lookup registry checked frame root key inputs = some result ↔
    ∃ declaration present,
      declaration.id = key ∧
        declaration.role = root.demand.role ∧
          Yulang.GeneralDictionaryBinderLocations.build declaration (frame.capture declaration.id) inputs =
              some result.located ∧
            result.children = Yulang.GeneralDictionaryEmissionPlans.children frame root declaration ⋯
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryComputedOutputPlans.lookup_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 17. build_head

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryComputedOutputPlans
- ソースファイル: lean/Yulang/GeneralDictionaryComputedOutputPlans.lean
- 命題: build が located を返した場合、その head は入力で与えた head に等しい。

### カーネル確認済みの型（#check @）

```lean
@Yulang.GeneralDictionaryComputedOutputPlans.build_head : ∀ {state : Yulang.GeneralSourceState.State}
  {roles : Yulang.Roles.RoleDecls} {demand : Yulang.GeneralSourceState.Demand roles}
  (declaration : Yulang.GeneralDeclarations.Declaration) (capture : Yulang.GeneralDeclarationDemands.Capture)
  (inputs : Yulang.GeneralDictionaryBinderLocations.Inputs state demand)
  (located : Yulang.GeneralDictionaryStateEquations.Located state demand),
  Yulang.GeneralDictionaryBinderLocations.build declaration capture inputs = some located → located.head = inputs.head
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryComputedOutputPlans.build_head' depends on axioms: [propext, Quot.sound]
```

## 18. lookup_plan

- 分類: 健全性
- ソースモジュール: Yulang.GeneralDictionaryComputedOutputPlans
- ソースファイル: lean/Yulang/GeneralDictionaryComputedOutputPlans.lean
- 命題: 出力束縛子専用 lookup が result を返せば、その子列は指定した根と key の Plan を満たす。

### カーネル確認済みの型（#check @）

```lean
@Yulang.GeneralDictionaryComputedOutputPlans.lookup_plan : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frame : Yulang.GeneralDictionaryEmissionPlans.Frame registry.roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles) (key : Nat)
  (inputs : Yulang.GeneralDictionaryBinderLocations.Inputs state root.demand)
  (result : Yulang.GeneralDictionaryComputedOutputPlans.Result state root),
  Yulang.GeneralDictionaryComputedOutputPlans.lookup registry checked frame root key inputs = some result →
    Yulang.GeneralDictionaryEmissionPlans.Plan registry checked frame root key result.children
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryComputedOutputPlans.lookup_plan' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 19. lookup_terms

- 分類: 健全性
- ソースモジュール: Yulang.GeneralDictionaryComputedOutputPlans
- ソースファイル: lean/Yulang/GeneralDictionaryComputedOutputPlans.lean
- 命題: 出力束縛子専用 lookup の成功に加え、該当 ID・役割の全可視宣言について supplied head が指定の HeadInstances を満たすと仮定すると、返された located は Terms を満たす。

### カーネル確認済みの型（#check @）

```lean
@Yulang.GeneralDictionaryComputedOutputPlans.lookup_terms : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (heads : Yulang.GeneralDictionaryComputedOutputPlans.HeadInstances registry.roles state)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles) (key : Nat)
  (inputs : Yulang.GeneralDictionaryBinderLocations.Inputs state root.demand)
  (result : Yulang.GeneralDictionaryComputedOutputPlans.Result state root),
  Yulang.GeneralDictionaryComputedOutputPlans.lookup registry checked (frames root) root key inputs = some result →
    (∀ (declaration : Yulang.GeneralDeclarations.Declaration),
        declaration ∈ registry.declarations →
          declaration.id = key →
            declaration.role = root.demand.role →
              heads root declaration ((frames root).capture declaration.id) inputs.head) →
      Yulang.GeneralDictionaryComputedOutputPlans.Terms registry frames heads root key result.located
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryComputedOutputPlans.lookup_terms' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 20. lookup_output_plan

- 分類: 健全性
- ソースモジュール: Yulang.GeneralDictionaryComputedOutputPlans
- ソースファイル: lean/Yulang/GeneralDictionaryComputedOutputPlans.lean
- 命題: 出力束縛子専用 lookup の成功から、ID・役割が一致する同一の可視宣言が存在し、その宣言に由来する子列・出力の OutputPlan と、その capture に対する located の Interpreted が同時に成り立つ。

### カーネル確認済みの型（#check @）

```lean
@Yulang.GeneralDictionaryComputedOutputPlans.lookup_output_plan : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frame : Yulang.GeneralDictionaryEmissionPlans.Frame registry.roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles) (key : Nat)
  (inputs : Yulang.GeneralDictionaryBinderLocations.Inputs state root.demand)
  (result : Yulang.GeneralDictionaryComputedOutputPlans.Result state root),
  Yulang.GeneralDictionaryComputedOutputPlans.lookup registry checked frame root key inputs = some result →
    ∃ declaration _present,
      declaration.id = key ∧
        declaration.role = root.demand.role ∧
          Yulang.GeneralDictionaryPlannedOutputs.OutputPlan registry checked frame root key
              (result.children,
                Yulang.GeneralDictionaryAssociatedProvenance.outputs registry.roles declaration root.demand) ∧
            Yulang.GeneralDictionaryOutputBinderTerms.Interpreted declaration (frame.capture declaration.id)
              result.located
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryComputedOutputPlans.lookup_output_plan' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 21. built_valid

- 分類: 健全性
- ソースモジュール: Yulang.GeneralDictionaryComputedTransactions
- ソースファイル: lean/Yulang/GeneralDictionaryComputedTransactions.lean
- 命題: 任意の検査済み registry、frames、heads、準備木について、出力束縛子専用 Built なら、対応する Terms を用いた Valid が成り立つ。

### カーネル確認済みの型（#check @）

```lean
@Yulang.GeneralDictionaryComputedTransactions.built_valid : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (heads : Yulang.GeneralDictionaryComputedOutputPlans.HeadInstances registry.roles state)
  (tree : Yulang.GeneralDictionaryTransactions.Prepared registry.roles state),
  Yulang.GeneralDictionaryComputedTransactions.Built registry checked frames heads tree →
    Yulang.GeneralDictionaryTransactions.Valid registry checked frames
      (Yulang.GeneralDictionaryComputedOutputPlans.Terms registry frames heads) tree
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryComputedTransactions.built_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 22. transaction_stored

- 分類: 健全性
- ソースモジュール: Yulang.GeneralDictionaryComputedTransactions
- ソースファイル: lean/Yulang/GeneralDictionaryComputedTransactions.lean
- 命題: 明示的 frames／heads に対する 出力束縛子専用 Built を満たす木の辞書は、木の items で持ち上げた Terms と Plan に基づく StoredInstance の Evidence を持つ。

### カーネル確認済みの型（#check @）

```lean
@Yulang.GeneralDictionaryComputedTransactions.transaction_stored : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (heads : Yulang.GeneralDictionaryComputedOutputPlans.HeadInstances registry.roles state)
  (tree : Yulang.GeneralDictionaryTransactions.Prepared registry.roles state),
  Yulang.GeneralDictionaryComputedTransactions.Built registry checked frames heads tree →
    Yulang.GeneralSourceDictionaries.Evidence
      (Yulang.GeneralDictionaryModelEvidence.StoredInstance
        (Yulang.GeneralDictionaryTransactions.PlannedAt registry checked frames
          (Yulang.GeneralDictionaryTransactions.LiftedTerms tree.items
            (Yulang.GeneralDictionaryComputedOutputPlans.Terms registry frames heads))))
      tree.dictionary
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryComputedTransactions.transaction_stored' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 23. lifted_source_instance

- 分類: 健全性
- ソースモジュール: Yulang.GeneralDictionaryComputedTransactions
- ソースファイル: lean/Yulang/GeneralDictionaryComputedTransactions.lean
- 命題: 任意の items・assignment・根・key・子列について、持ち上げた 出力束縛子専用 Terms と Plan の ModelInstance があれば、対応する SourceInstance が成り立つ。

### カーネル確認済みの型（#check @）

```lean
@Yulang.GeneralDictionaryComputedTransactions.lifted_source_instance : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (heads : Yulang.GeneralDictionaryComputedOutputPlans.HeadInstances registry.roles state)
  (items : List (Yulang.GeneralDictionaryBatchRecording.Item registry.roles state))
  (assignment : Yulang.GeneralSourceState.Assignment)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles) (key : Nat)
  (children : List (Yulang.GeneralSourceDictionaries.Occurrence registry.roles)),
  Yulang.GeneralDictionaryModelEvidence.ModelInstance
      (Yulang.GeneralDictionaryTransactions.PlannedAt registry checked frames
        (Yulang.GeneralDictionaryTransactions.LiftedTerms items
          (Yulang.GeneralDictionaryComputedOutputPlans.Terms registry frames heads)))
      assignment root key children →
    Yulang.GeneralDictionaryComputedTransactions.SourceInstance registry checked frames heads assignment root key
      children
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryComputedTransactions.lifted_source_instance' depends on axioms: [propext, Quot.sound]
```

## 24. transaction_uniform

- 分類: 健全性
- ソースモジュール: Yulang.GeneralDictionaryComputedTransactions
- ソースファイル: lean/Yulang/GeneralDictionaryComputedTransactions.lean
- 命題: 明示的 frames／heads に対する 出力束縛子専用 Built を満たす木には、消去した辞書からの一つの Readback witness が存在し、記録した全 items を満たすすべての assignment で、その同じ witness が SourceInstance の Evidence を持つ。モデルの存在自体は結論に含まない。

### カーネル確認済みの型（#check @）

```lean
@Yulang.GeneralDictionaryComputedTransactions.transaction_uniform : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (heads : Yulang.GeneralDictionaryComputedOutputPlans.HeadInstances registry.roles state)
  (tree : Yulang.GeneralDictionaryTransactions.Prepared registry.roles state),
  Yulang.GeneralDictionaryComputedTransactions.Built registry checked frames heads tree →
    ∃ witness,
      Yulang.GeneralSourceDictionaries.Readback tree.root (Yulang.GeneralSourceDictionaries.erase tree.dictionary)
          witness ∧
        ∀ (assignment : Yulang.GeneralSourceState.Assignment),
          Yulang.GeneralSourceState.Models (Yulang.GeneralDictionaryBatchRecording.record tree.items) assignment →
            Yulang.GeneralSourceDictionaries.Evidence
              (Yulang.GeneralDictionaryComputedTransactions.SourceInstance registry checked frames heads assignment)
              witness
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryComputedTransactions.transaction_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 25. source_instance_declaration

- 分類: 健全性
- ソースモジュール: Yulang.GeneralDictionaryComputedTransactions
- ソースファイル: lean/Yulang/GeneralDictionaryComputedTransactions.lean
- 命題: 任意の SourceInstance から、ID・役割が一致する可視宣言と located が存在し、子列が当該宣言の生成列に等しく、指定 heads、当該 capture の Interpreted、assignment における located の方程式成立を同時に満たす。

### カーネル確認済みの型（#check @）

```lean
@Yulang.GeneralDictionaryComputedTransactions.source_instance_declaration : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (heads : Yulang.GeneralDictionaryComputedOutputPlans.HeadInstances registry.roles state)
  (assignment : Yulang.GeneralSourceState.Assignment)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles) (key : Nat)
  (children : List (Yulang.GeneralSourceDictionaries.Occurrence registry.roles)),
  Yulang.GeneralDictionaryComputedTransactions.SourceInstance registry checked frames heads assignment root key
      children →
    ∃ declaration present,
      declaration.id = key ∧
        declaration.role = root.demand.role ∧
          children = Yulang.GeneralDictionaryEmissionPlans.children (frames root) root declaration ⋯ ∧
            ∃ located,
              heads root declaration ((frames root).capture declaration.id) located.head ∧
                Yulang.GeneralDictionaryOutputBinderTerms.Interpreted declaration ((frames root).capture declaration.id)
                    located ∧
                  located.equations.Holds assignment
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryComputedTransactions.source_instance_declaration' depends on axioms: [propext, Quot.sound]
```

## 26. source_output_denotes

- 分類: 健全性
- ソースモジュール: Yulang.GeneralDictionaryComputedTransactions
- ソースファイル: lean/Yulang/GeneralDictionaryComputedTransactions.lean
- 命題: 任意の SourceInstance と任意の要求出力位置について、ID・役割・子列の一致する可視宣言と出力項が存在し、その名前の 出力束縛子専用 Denotes が成り立ち、要求先の値はその項の assignment における評価と同値になる。

### カーネル確認済みの型（#check @）

```lean
@Yulang.GeneralDictionaryComputedTransactions.source_output_denotes : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (heads : Yulang.GeneralDictionaryComputedOutputPlans.HeadInstances registry.roles state)
  (assignment : Yulang.GeneralSourceState.Assignment)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles) (key : Nat)
  (children : List (Yulang.GeneralSourceDictionaries.Occurrence registry.roles)),
  Yulang.GeneralDictionaryComputedTransactions.SourceInstance registry checked frames heads assignment root key
      children →
    ∀ (index : Fin root.demand.outputs.length),
      ∃ declaration present,
        declaration.id = key ∧
          declaration.role = root.demand.role ∧
            children = Yulang.GeneralDictionaryEmissionPlans.children (frames root) root declaration ⋯ ∧
              ∃ term,
                Yulang.GeneralDictionaryOutputBinderTerms.Denotes registry.roles declaration
                    ((frames root).capture declaration.id) root.demand.outputs[index].name term ∧
                  Yulang.Common.Equivalent (assignment root.demand.outputs[index].target).fst
                    (Yulang.Core.PresenceGeneration.TyTerm.eval Yulang.Common.model assignment term)
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryComputedTransactions.source_output_denotes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 27. child_prepares

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryPreparationExamples
- ソースファイル: lean/Yulang/GeneralDictionaryPreparationExamples.lean
- 命題: 固定例の葉 recipe は、child・key 3・childLocated・空子列の node に prepare される。

### カーネル確認済みの型（#check @）

```lean
Yulang.GeneralDictionaryPreparationExamples.child_prepares : Yulang.GeneralDictionaryVariablePreparation.prepare
    Yulang.GeneralDictionaryTerminalFixture.registry Yulang.GeneralDictionaryTerminalFixture.registry_checked
    (fun x => Yulang.GeneralDictionaryTerminalFixture.frame) Yulang.GeneralDictionaryPreparationExamples.childRecipe =
  some
    (Yulang.GeneralDictionaryTransactions.Prepared.node Yulang.GeneralDictionaryTerminalFixture.child 3
      Yulang.GeneralDictionaryTerminalFixture.childLocated [])
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryPreparationExamples.child_prepares' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 28. tree_prepares

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryPreparationExamples
- ソースファイル: lean/Yulang/GeneralDictionaryPreparationExamples.lean
- 命題: 固定例の recipe は指定した tree に prepare される。

### カーネル確認済みの型（#check @）

```lean
Yulang.GeneralDictionaryPreparationExamples.tree_prepares : Yulang.GeneralDictionaryVariablePreparation.prepare
    Yulang.GeneralDictionaryTerminalFixture.registry Yulang.GeneralDictionaryTerminalFixture.registry_checked
    (fun x => Yulang.GeneralDictionaryTerminalFixture.frame) Yulang.GeneralDictionaryPreparationExamples.recipe =
  some Yulang.GeneralDictionaryTerminalFixture.tree
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryPreparationExamples.tree_prepares' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 29. missing_child_defers

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryPreparationExamples
- ソースファイル: lean/Yulang/GeneralDictionaryPreparationExamples.lean
- 命題: 固定例の根で必要な子 recipe を省くと prepare は none を返す。

### カーネル確認済みの型（#check @）

```lean
Yulang.GeneralDictionaryPreparationExamples.missing_child_defers : Yulang.GeneralDictionaryVariablePreparation.prepare
    Yulang.GeneralDictionaryTerminalFixture.registry Yulang.GeneralDictionaryTerminalFixture.registry_checked
    (fun x => Yulang.GeneralDictionaryTerminalFixture.frame)
    (Yulang.GeneralDictionaryVariablePreparation.Recipe.node Yulang.GeneralDictionaryTerminalFixture.root 2
      Yulang.GeneralDictionaryTerminalFixture.rootInputs []) =
  none
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryPreparationExamples.missing_child_defers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 30. extra_child_defers

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryPreparationExamples
- ソースファイル: lean/Yulang/GeneralDictionaryPreparationExamples.lean
- 命題: 固定例の根に同じ子 recipe を二つ与えると prepare は none を返す。

### カーネル確認済みの型（#check @）

```lean
Yulang.GeneralDictionaryPreparationExamples.extra_child_defers : Yulang.GeneralDictionaryVariablePreparation.prepare
    Yulang.GeneralDictionaryTerminalFixture.registry Yulang.GeneralDictionaryTerminalFixture.registry_checked
    (fun x => Yulang.GeneralDictionaryTerminalFixture.frame)
    (Yulang.GeneralDictionaryVariablePreparation.Recipe.node Yulang.GeneralDictionaryTerminalFixture.root 2
      Yulang.GeneralDictionaryTerminalFixture.rootInputs
      [Yulang.GeneralDictionaryPreparationExamples.childRecipe,
        Yulang.GeneralDictionaryPreparationExamples.childRecipe]) =
  none
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryPreparationExamples.extra_child_defers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 31. wrong_identity_defers

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryPreparationExamples
- ソースファイル: lean/Yulang/GeneralDictionaryPreparationExamples.lean
- 命題: 固定例で子の occurrence identity が一致しない recipe は prepare が none を返す。

### カーネル確認済みの型（#check @）

```lean
Yulang.GeneralDictionaryPreparationExamples.wrong_identity_defers : Yulang.GeneralDictionaryVariablePreparation.prepare
    Yulang.GeneralDictionaryTerminalFixture.registry Yulang.GeneralDictionaryTerminalFixture.registry_checked
    (fun x => Yulang.GeneralDictionaryTerminalFixture.frame)
    (Yulang.GeneralDictionaryVariablePreparation.Recipe.node Yulang.GeneralDictionaryTerminalFixture.root 2
      Yulang.GeneralDictionaryTerminalFixture.rootInputs
      [Yulang.GeneralDictionaryVariablePreparation.Recipe.node Yulang.GeneralDictionaryPreparationExamples.wrongChild 3
          Yulang.GeneralDictionaryTerminalFixture.childInputs []]) =
  none
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryPreparationExamples.wrong_identity_defers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 32. missing_key_defers

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryPreparationExamples
- ソースファイル: lean/Yulang/GeneralDictionaryPreparationExamples.lean
- 命題: 固定例で存在しない key 99 を根に指定すると prepare は none を返す。

### カーネル確認済みの型（#check @）

```lean
Yulang.GeneralDictionaryPreparationExamples.missing_key_defers : Yulang.GeneralDictionaryVariablePreparation.prepare
    Yulang.GeneralDictionaryTerminalFixture.registry Yulang.GeneralDictionaryTerminalFixture.registry_checked
    (fun x => Yulang.GeneralDictionaryTerminalFixture.frame)
    (Yulang.GeneralDictionaryVariablePreparation.Recipe.node Yulang.GeneralDictionaryTerminalFixture.root 99
      Yulang.GeneralDictionaryTerminalFixture.rootInputs [Yulang.GeneralDictionaryPreparationExamples.childRecipe]) =
  none
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryPreparationExamples.missing_key_defers' depends on axioms: [propext, Quot.sound]
```

## 33. unequal_leaf_defers

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryPreparationExamples
- ソースファイル: lean/Yulang/GeneralDictionaryPreparationExamples.lean
- 命題: 固定例で葉の入力両端 ID が異なる frame を与えると prepare は none を返す。

### カーネル確認済みの型（#check @）

```lean
Yulang.GeneralDictionaryPreparationExamples.unequal_leaf_defers : Yulang.GeneralDictionaryVariablePreparation.prepare
    Yulang.GeneralDictionaryTerminalFixture.registry Yulang.GeneralDictionaryTerminalFixture.registry_checked
    (fun x => Yulang.GeneralDictionaryPreparationExamples.unequalFrame)
    Yulang.GeneralDictionaryPreparationExamples.childRecipe =
  none
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryPreparationExamples.unequal_leaf_defers' depends on axioms: [propext, Quot.sound]
```

## 34. recipe_heads

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryPreparationExamples
- ソースファイル: lean/Yulang/GeneralDictionaryPreparationExamples.lean
- 命題: 任意の heads について固定例の rootHead と childHead を仮定すれば、recipe 全体の Heads が成り立つ。

### カーネル確認済みの型（#check @）

```lean
Yulang.GeneralDictionaryPreparationExamples.recipe_heads : ∀
  (heads :
    Yulang.GeneralDictionaryVariablePlans.HeadInstances Yulang.GeneralDictionaryTerminalFixture.registry.roles
      Yulang.GeneralDictionaryTerminalFixture.state),
  heads Yulang.GeneralDictionaryTerminalFixture.root Yulang.GeneralDictionaryOutputBinderExamples.binderWrap
      Yulang.GeneralDictionaryTerminalFixture.capture Yulang.GeneralDictionaryTerminalFixture.rootInputs.head →
    heads Yulang.GeneralDictionaryTerminalFixture.child Yulang.GeneralDictionaryTerminalFixture.leaf
        Yulang.GeneralDictionaryTerminalFixture.capture Yulang.GeneralDictionaryTerminalFixture.childInputs.head →
      Yulang.GeneralDictionaryVariablePreparation.Heads Yulang.GeneralDictionaryTerminalFixture.registry
        (fun x => Yulang.GeneralDictionaryTerminalFixture.frame) heads
        Yulang.GeneralDictionaryPreparationExamples.recipe
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryPreparationExamples.recipe_heads' depends on axioms: [propext, Quot.sound]
```

## 35. prepared_built

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryPreparationExamples
- ソースファイル: lean/Yulang/GeneralDictionaryPreparationExamples.lean
- 命題: 任意の heads について固定例の rootHead と childHead を仮定すれば、固定 tree は変数版 Built を満たす。

### カーネル確認済みの型（#check @）

```lean
Yulang.GeneralDictionaryPreparationExamples.prepared_built : ∀
  (heads :
    Yulang.GeneralDictionaryVariablePlans.HeadInstances Yulang.GeneralDictionaryTerminalFixture.registry.roles
      Yulang.GeneralDictionaryTerminalFixture.state),
  heads Yulang.GeneralDictionaryTerminalFixture.root Yulang.GeneralDictionaryOutputBinderExamples.binderWrap
      Yulang.GeneralDictionaryTerminalFixture.capture Yulang.GeneralDictionaryTerminalFixture.rootInputs.head →
    heads Yulang.GeneralDictionaryTerminalFixture.child Yulang.GeneralDictionaryTerminalFixture.leaf
        Yulang.GeneralDictionaryTerminalFixture.capture Yulang.GeneralDictionaryTerminalFixture.childInputs.head →
      Yulang.GeneralDictionaryVariableTransactions.Built Yulang.GeneralDictionaryTerminalFixture.registry
        Yulang.GeneralDictionaryTerminalFixture.registry_checked
        (fun x => Yulang.GeneralDictionaryTerminalFixture.frame) heads Yulang.GeneralDictionaryTerminalFixture.tree
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryPreparationExamples.prepared_built' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 36. leaf_checked

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryTerminalFixture
- ソースファイル: lean/Yulang/GeneralDictionaryTerminalFixture.lean
- 命題: 固定例の leaf 宣言は指定 constructors／roles の DeclarationChecked を満たす。

### カーネル確認済みの型（#check @）

```lean
Yulang.GeneralDictionaryTerminalFixture.leaf_checked : Yulang.GeneralDeclarations.DeclarationChecked
  Yulang.GeneralDeclarationExamples.constructors Yulang.GeneralDeclarationExamples.roles
  Yulang.GeneralDictionaryTerminalFixture.leaf
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryTerminalFixture.leaf_checked' depends on axioms: [propext, Quot.sound]
```

## 37. registry_checked

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryTerminalFixture
- ソースファイル: lean/Yulang/GeneralDictionaryTerminalFixture.lean
- 命題: 固定例の registry は Checked を満たす。

### カーネル確認済みの型（#check @）

```lean
Yulang.GeneralDictionaryTerminalFixture.registry_checked : Yulang.GeneralDeclarations.Checked
  Yulang.GeneralDictionaryTerminalFixture.registry
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryTerminalFixture.registry_checked' depends on axioms: [propext, Quot.sound]
```

## 38. root_actual_children

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryTerminalFixture
- ソースファイル: lean/Yulang/GeneralDictionaryTerminalFixture.lean
- 命題: 固定例で binderWrap から生成される根の子列はちょうど [child] である。

### カーネル確認済みの型（#check @）

```lean
Yulang.GeneralDictionaryTerminalFixture.root_actual_children : Yulang.GeneralDictionaryEmissionPlans.children
    Yulang.GeneralDictionaryTerminalFixture.frame Yulang.GeneralDictionaryTerminalFixture.root
    Yulang.GeneralDictionaryOutputBinderExamples.binderWrap
    Yulang.GeneralDictionaryOutputBinderExamples.binderWrap_checked =
  [Yulang.GeneralDictionaryTerminalFixture.child]
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryTerminalFixture.root_actual_children' depends on axioms: [propext, Quot.sound]
```

## 39. child_actual_children

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryTerminalFixture
- ソースファイル: lean/Yulang/GeneralDictionaryTerminalFixture.lean
- 命題: 固定例で leaf から生成される子の子列は空である。

### カーネル確認済みの型（#check @）

```lean
Yulang.GeneralDictionaryTerminalFixture.child_actual_children : Yulang.GeneralDictionaryEmissionPlans.children
    Yulang.GeneralDictionaryTerminalFixture.frame Yulang.GeneralDictionaryTerminalFixture.child
    Yulang.GeneralDictionaryTerminalFixture.leaf Yulang.GeneralDictionaryTerminalFixture.leaf_checked =
  []
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryTerminalFixture.child_actual_children' depends on axioms: [propext, Quot.sound]
```

## 40. root_holds

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryTerminalFixture
- ソースファイル: lean/Yulang/GeneralDictionaryTerminalFixture.lean
- 命題: 固定例の assignment は rootLocated の方程式を満たす。

### カーネル確認済みの型（#check @）

```lean
Yulang.GeneralDictionaryTerminalFixture.root_holds : Yulang.GeneralDictionaryTerminalFixture.rootLocated.equations.Holds
  Yulang.GeneralDictionaryTerminalFixture.assignment
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryTerminalFixture.root_holds' depends on axioms: [propext, Quot.sound]
```

## 41. child_holds

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryTerminalFixture
- ソースファイル: lean/Yulang/GeneralDictionaryTerminalFixture.lean
- 命題: 固定例の assignment は childLocated の方程式を満たす。

### カーネル確認済みの型（#check @）

```lean
Yulang.GeneralDictionaryTerminalFixture.child_holds : Yulang.GeneralDictionaryTerminalFixture.childLocated.equations.Holds
  Yulang.GeneralDictionaryTerminalFixture.assignment
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryTerminalFixture.child_holds' depends on axioms: [propext, Quot.sound]
```

## 42. joint_model

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryTerminalFixture
- ソースファイル: lean/Yulang/GeneralDictionaryTerminalFixture.lean
- 命題: 固定例の assignment は [rootItem, childItem] の一括記録を満たす。

### カーネル確認済みの型（#check @）

```lean
Yulang.GeneralDictionaryTerminalFixture.joint_model : Yulang.GeneralSourceState.Models
  (Yulang.GeneralDictionaryBatchRecording.record
    [Yulang.GeneralDictionaryTerminalFixture.rootItem, Yulang.GeneralDictionaryTerminalFixture.childItem])
  Yulang.GeneralDictionaryTerminalFixture.assignment
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryTerminalFixture.joint_model' depends on axioms: [propext, Quot.sound]
```

## 43. tree_items

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryTerminalFixture
- ソースファイル: lean/Yulang/GeneralDictionaryTerminalFixture.lean
- 命題: 固定 tree の items はちょうど [rootItem, childItem] である。

### カーネル確認済みの型（#check @）

```lean
Yulang.GeneralDictionaryTerminalFixture.tree_items : Yulang.GeneralDictionaryTerminalFixture.tree.items =
  [Yulang.GeneralDictionaryTerminalFixture.rootItem, Yulang.GeneralDictionaryTerminalFixture.childItem]
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryTerminalFixture.tree_items' depends on axioms: [propext, Quot.sound]
```

## 44. tree_joint_model

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryTerminalFixture
- ソースファイル: lean/Yulang/GeneralDictionaryTerminalFixture.lean
- 命題: 固定例の assignment は tree.items の一括記録を満たす。

### カーネル確認済みの型（#check @）

```lean
Yulang.GeneralDictionaryTerminalFixture.tree_joint_model : Yulang.GeneralSourceState.Models
  (Yulang.GeneralDictionaryBatchRecording.record Yulang.GeneralDictionaryTerminalFixture.tree.items)
  Yulang.GeneralDictionaryTerminalFixture.assignment
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryTerminalFixture.tree_joint_model' depends on axioms: [propext, Quot.sound]
```

## 45. retained_outputs

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryTerminalFixture
- ソースファイル: lean/Yulang/GeneralDictionaryTerminalFixture.lean
- 命題: 固定例の根の要求出力は名前 0・先 3 と名前 0・先 4 の二件、子の要求出力は名前 1・先 2 の一件である。

### カーネル確認済みの型（#check @）

```lean
Yulang.GeneralDictionaryTerminalFixture.retained_outputs : Yulang.GeneralDictionaryTerminalFixture.rootDemand.outputs =
    [{ name := 0, target := 3 }, { name := 0, target := 4 }] ∧
  Yulang.GeneralDictionaryTerminalFixture.childDemand.outputs = [{ name := 1, target := 2 }]
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryTerminalFixture.retained_outputs' depends on axioms: [propext]
```

## 46. root_build

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryTerminalFixture
- ソースファイル: lean/Yulang/GeneralDictionaryTerminalFixture.lean
- 命題: 固定例の binderWrap・capture・rootInputs の build は rootLocated を返す。

### カーネル確認済みの型（#check @）

```lean
Yulang.GeneralDictionaryTerminalFixture.root_build : Yulang.GeneralDictionaryVariableTerms.build
    Yulang.GeneralDictionaryOutputBinderExamples.binderWrap Yulang.GeneralDictionaryTerminalFixture.capture
    Yulang.GeneralDictionaryTerminalFixture.rootInputs =
  some Yulang.GeneralDictionaryTerminalFixture.rootLocated
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryTerminalFixture.root_build' depends on axioms: [propext, Quot.sound]
```

## 47. child_build

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryTerminalFixture
- ソースファイル: lean/Yulang/GeneralDictionaryTerminalFixture.lean
- 命題: 固定例の leaf・capture・childInputs の build は childLocated を返す。

### カーネル確認済みの型（#check @）

```lean
Yulang.GeneralDictionaryTerminalFixture.child_build : Yulang.GeneralDictionaryVariableTerms.build
    Yulang.GeneralDictionaryTerminalFixture.leaf Yulang.GeneralDictionaryTerminalFixture.capture
    Yulang.GeneralDictionaryTerminalFixture.childInputs =
  some Yulang.GeneralDictionaryTerminalFixture.childLocated
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryTerminalFixture.child_build' depends on axioms: [propext, Quot.sound]
```

## 48. root_lookup

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryTerminalFixture
- ソースファイル: lean/Yulang/GeneralDictionaryTerminalFixture.lean
- 命題: 固定例の根・key 2・rootInputs の lookup は rootResult を返す。

### カーネル確認済みの型（#check @）

```lean
Yulang.GeneralDictionaryTerminalFixture.root_lookup : Yulang.GeneralDictionaryVariablePlans.lookup
    Yulang.GeneralDictionaryTerminalFixture.registry Yulang.GeneralDictionaryTerminalFixture.registry_checked
    Yulang.GeneralDictionaryTerminalFixture.frame Yulang.GeneralDictionaryTerminalFixture.root 2
    Yulang.GeneralDictionaryTerminalFixture.rootInputs =
  some Yulang.GeneralDictionaryTerminalFixture.rootResult
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryTerminalFixture.root_lookup' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 49. child_lookup

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryTerminalFixture
- ソースファイル: lean/Yulang/GeneralDictionaryTerminalFixture.lean
- 命題: 固定例の子・key 3・childInputs の lookup は childResult を返す。

### カーネル確認済みの型（#check @）

```lean
Yulang.GeneralDictionaryTerminalFixture.child_lookup : Yulang.GeneralDictionaryVariablePlans.lookup
    Yulang.GeneralDictionaryTerminalFixture.registry Yulang.GeneralDictionaryTerminalFixture.registry_checked
    Yulang.GeneralDictionaryTerminalFixture.frame Yulang.GeneralDictionaryTerminalFixture.child 3
    Yulang.GeneralDictionaryTerminalFixture.childInputs =
  some Yulang.GeneralDictionaryTerminalFixture.childResult
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryTerminalFixture.child_lookup' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 50. tree_built

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryTerminalFixture
- ソースファイル: lean/Yulang/GeneralDictionaryTerminalFixture.lean
- 命題: 任意の heads について固定例の rootHead と childHead を仮定すれば、固定 tree は変数版 Built を満たす。

### カーネル確認済みの型（#check @）

```lean
Yulang.GeneralDictionaryTerminalFixture.tree_built : ∀
  (heads :
    Yulang.GeneralDictionaryVariablePlans.HeadInstances Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralDictionaryTerminalFixture.state),
  heads Yulang.GeneralDictionaryTerminalFixture.root Yulang.GeneralDictionaryOutputBinderExamples.binderWrap
      Yulang.GeneralDictionaryTerminalFixture.capture Yulang.GeneralDictionaryTerminalFixture.rootInputs.head →
    heads Yulang.GeneralDictionaryTerminalFixture.child Yulang.GeneralDictionaryTerminalFixture.leaf
        Yulang.GeneralDictionaryTerminalFixture.capture Yulang.GeneralDictionaryTerminalFixture.childInputs.head →
      Yulang.GeneralDictionaryVariableTransactions.Built Yulang.GeneralDictionaryTerminalFixture.registry
        Yulang.GeneralDictionaryTerminalFixture.registry_checked
        (fun x => Yulang.GeneralDictionaryTerminalFixture.frame) heads Yulang.GeneralDictionaryTerminalFixture.tree
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryTerminalFixture.tree_built' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 51. uniform_completion

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryTerminalFixture
- ソースファイル: lean/Yulang/GeneralDictionaryTerminalFixture.lean
- 命題: 任意の heads と固定例の rootHead／childHead を仮定すれば、固定 tree の消去辞書に一つの Readback witness が存在し、tree.items の記録を満たすすべての model で、その witness が変数版 SourceInstance の Evidence を持つ。

### カーネル確認済みの型（#check @）

```lean
Yulang.GeneralDictionaryTerminalFixture.uniform_completion : ∀
  (heads :
    Yulang.GeneralDictionaryVariablePlans.HeadInstances Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralDictionaryTerminalFixture.state),
  heads Yulang.GeneralDictionaryTerminalFixture.root Yulang.GeneralDictionaryOutputBinderExamples.binderWrap
      Yulang.GeneralDictionaryTerminalFixture.capture Yulang.GeneralDictionaryTerminalFixture.rootInputs.head →
    heads Yulang.GeneralDictionaryTerminalFixture.child Yulang.GeneralDictionaryTerminalFixture.leaf
        Yulang.GeneralDictionaryTerminalFixture.capture Yulang.GeneralDictionaryTerminalFixture.childInputs.head →
      ∃ witness,
        Yulang.GeneralSourceDictionaries.Readback Yulang.GeneralDictionaryTerminalFixture.tree.root
            (Yulang.GeneralSourceDictionaries.erase Yulang.GeneralDictionaryTerminalFixture.tree.dictionary) witness ∧
          ∀ (model : Yulang.GeneralSourceState.Assignment),
            Yulang.GeneralSourceState.Models
                (Yulang.GeneralDictionaryBatchRecording.record Yulang.GeneralDictionaryTerminalFixture.tree.items)
                model →
              Yulang.GeneralSourceDictionaries.Evidence
                (Yulang.GeneralDictionaryVariableTransactions.SourceInstance
                  Yulang.GeneralDictionaryTerminalFixture.registry
                  Yulang.GeneralDictionaryTerminalFixture.registry_checked
                  (fun x => Yulang.GeneralDictionaryTerminalFixture.frame) heads model)
                witness
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryTerminalFixture.uniform_completion' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 52. all_model_root_child_input

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryTerminalFixture
- ソースファイル: lean/Yulang/GeneralDictionaryTerminalFixture.lean
- 命題: 固定 tree.items の記録を満たす任意の model と任意の根出力位置について、その出力先の値と source 2 の値、source 2 と source 0 の値、および出力先と source 0 の値はそれぞれ同値である。

### カーネル確認済みの型（#check @）

```lean
Yulang.GeneralDictionaryTerminalFixture.all_model_root_child_input : ∀ (model : Yulang.GeneralSourceState.Assignment),
  Yulang.GeneralSourceState.Models
      (Yulang.GeneralDictionaryBatchRecording.record Yulang.GeneralDictionaryTerminalFixture.tree.items) model →
    ∀ (index : Fin Yulang.GeneralDictionaryTerminalFixture.rootDemand.outputs.length),
      Yulang.Common.Equivalent (model Yulang.GeneralDictionaryTerminalFixture.rootDemand.outputs[index].target).fst
          (model 2).fst ∧
        Yulang.Common.Equivalent (model 2).fst (model 0).fst ∧
          Yulang.Common.Equivalent (model Yulang.GeneralDictionaryTerminalFixture.rootDemand.outputs[index].target).fst
            (model 0).fst
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryTerminalFixture.all_model_root_child_input' depends on axioms: [propext, Quot.sound]
```

## 53. compile_preserved

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryVariableCompatibility
- ソースファイル: lean/Yulang/GeneralDictionaryVariableCompatibility.lean
- 命題: 関連方程式名が重複しない任意の宣言・capture について、旧 BinderLocations.compile の成功は同じ項を返す変数版 compile の成功として保存される。

### カーネル確認済みの型（#check @）

```lean
Yulang.GeneralDictionaryVariableCompatibility.compile_preserved : ∀ (state : Yulang.GeneralSourceState.State)
  (roles : Yulang.Roles.RoleDecls) (declaration : Yulang.GeneralDeclarations.Declaration)
  (capture : Yulang.GeneralDeclarationDemands.Capture),
  (List.map Yulang.GeneralDeclarations.Equation.name declaration.associated).Nodup →
    ∀ (name : Nat) (term : Yulang.Core.PresenceGeneration.TyTerm (Fin state.slots)),
      Yulang.GeneralDictionaryBinderLocations.compile state roles declaration capture name = some term →
        Yulang.GeneralDictionaryVariableTerms.compile state roles declaration capture name = some term
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryVariableCompatibility.compile_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 54. build_preserved

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryVariableCompatibility
- ソースファイル: lean/Yulang/GeneralDictionaryVariableCompatibility.lean
- 命題: 関連方程式名が重複しない任意の宣言・capture・inputs について、旧 BinderLocations.build の成功は同じ located を返す変数版 build の成功として保存される。

### カーネル確認済みの型（#check @）

```lean
@Yulang.GeneralDictionaryVariableCompatibility.build_preserved : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State} {demand : Yulang.GeneralSourceState.Demand roles}
  (declaration : Yulang.GeneralDeclarations.Declaration) (capture : Yulang.GeneralDeclarationDemands.Capture),
  (List.map Yulang.GeneralDeclarations.Equation.name declaration.associated).Nodup →
    ∀ (inputs : Yulang.GeneralDictionaryBinderLocations.Inputs state demand)
      (located : Yulang.GeneralDictionaryStateEquations.Located state demand),
      Yulang.GeneralDictionaryBinderLocations.build declaration capture inputs = some located →
        Yulang.GeneralDictionaryVariableTerms.build declaration capture inputs = some located
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryVariableCompatibility.build_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 55. singleton_input_lookup

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryVariableExamples
- ソースファイル: lean/Yulang/GeneralDictionaryVariableExamples.lean
- 命題: 固定例の単一点 capture に対する入力変数 lookup は source ID 12 の変数を返す。

### カーネル確認済みの型（#check @）

```lean
Yulang.GeneralDictionaryVariableExamples.singleton_input_lookup : Yulang.GeneralDictionaryVariableTerms.lookup
    Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryOutputBinderExamples.inputWrap
    Yulang.GeneralDictionaryVariableExamples.singletonCapture 0 =
  some (Yulang.Core.PresenceGeneration.TyTerm.var 12)
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryVariableExamples.singleton_input_lookup' depends on axioms: [propext, Quot.sound]
```

## 56. unequal_input_deferred

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryVariableExamples
- ソースファイル: lean/Yulang/GeneralDictionaryVariableExamples.lean
- 命題: 固定例の入力両端 ID が異なる capture では lookup は none を返す。

### カーネル確認済みの型（#check @）

```lean
Yulang.GeneralDictionaryVariableExamples.unequal_input_deferred : Yulang.GeneralDictionaryVariableTerms.lookup
    Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryOutputBinderExamples.inputWrap
    Yulang.GeneralDictionaryBinderLocationExamples.shiftedCapture 0 =
  none
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryVariableExamples.unequal_input_deferred' depends on axioms: [propext, Quot.sound]
```

## 57. output_binder_unchanged

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryVariableExamples
- ソースファイル: lean/Yulang/GeneralDictionaryVariableExamples.lean
- 命題: 固定例の出力束縛子 lookup は、入力両端 ID が異なる capture でも source ID 12 の変数を返す。

### カーネル確認済みの型（#check @）

```lean
Yulang.GeneralDictionaryVariableExamples.output_binder_unchanged : Yulang.GeneralDictionaryVariableTerms.lookup
    Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryOutputBinderExamples.binderWrap
    Yulang.GeneralDictionaryBinderLocationExamples.shiftedCapture 0 =
  some (Yulang.Core.PresenceGeneration.TyTerm.var 12)
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryVariableExamples.output_binder_unchanged' depends on axioms: [propext, Quot.sound]
```

## 58. compound_deferred

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryVariableExamples
- ソースファイル: lean/Yulang/GeneralDictionaryVariableExamples.lean
- 命題: 固定例の複合 RHS に対する lookup は none を返す。

### カーネル確認済みの型（#check @）

```lean
Yulang.GeneralDictionaryVariableExamples.compound_deferred : Yulang.GeneralDictionaryVariableTerms.lookup
    Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDeclarationExamples.wrap
    Yulang.GeneralDictionaryVariableExamples.singletonCapture 0 =
  none
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryVariableExamples.compound_deferred' depends on axioms: [propext, Quot.sound]
```

## 59. default_deferred

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryVariableExamples
- ソースファイル: lean/Yulang/GeneralDictionaryVariableExamples.lean
- 命題: 固定例の default RHS に対する lookup は none を返す。

### カーネル確認済みの型（#check @）

```lean
Yulang.GeneralDictionaryVariableExamples.default_deferred : Yulang.GeneralDictionaryVariableTerms.lookup
    Yulang.GeneralDictionaryOutputBinderExamples.defaultRoles Yulang.GeneralDictionaryOutputBinderExamples.defaultWrap
    Yulang.GeneralDictionaryVariableExamples.singletonCapture 0 =
  none
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryVariableExamples.default_deferred' depends on axioms: [propext, Quot.sound]
```

## 60. nonidentity_input_compiles

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryVariableExamples
- ソースファイル: lean/Yulang/GeneralDictionaryVariableExamples.lean
- 命題: 非恒等 source map の固定例で、単一点入力変数の compile は slot 2 の変数を返す。

### カーネル確認済みの型（#check @）

```lean
Yulang.GeneralDictionaryVariableExamples.nonidentity_input_compiles : Yulang.GeneralDictionaryVariableTerms.compile
    Yulang.GeneralDictionaryBinderLocationExamples.shiftedState Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDictionaryOutputBinderExamples.inputWrap Yulang.GeneralDictionaryVariableExamples.singletonCapture 0 =
  some (Yulang.Core.PresenceGeneration.TyTerm.var 2)
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryVariableExamples.nonidentity_input_compiles' depends on axioms: [propext, Quot.sound]
```

## 61. nonidentity_input_build

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryVariableExamples
- ソースファイル: lean/Yulang/GeneralDictionaryVariableExamples.lean
- 命題: 非恒等 source map の固定例で、入力変数版 build は指定した shiftedLocated を返す。

### カーネル確認済みの型（#check @）

```lean
Yulang.GeneralDictionaryVariableExamples.nonidentity_input_build : Yulang.GeneralDictionaryVariableTerms.build
    Yulang.GeneralDictionaryOutputBinderExamples.inputWrap Yulang.GeneralDictionaryVariableExamples.singletonCapture
    Yulang.GeneralDictionaryBinderLocationExamples.shiftedInputs =
  some Yulang.GeneralDictionaryBinderLocationExamples.shiftedLocated
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryVariableExamples.nonidentity_input_build' depends on axioms: [propext, Quot.sound]
```

## 62. compile_slot_exact

- 分類: 完全性
- ソースモジュール: Yulang.GeneralDictionaryVariableMaterialization
- ソースファイル: lean/Yulang/GeneralDictionaryVariableMaterialization.lean
- 命題: 関連方程式名に重複がないとき、任意の slot への変数として compile が成功することと、その slot の source ID の変数が Denotes を満たすことは同値。

### カーネル確認済みの型（#check @）

```lean
Yulang.GeneralDictionaryVariableMaterialization.compile_slot_exact : ∀ (roles : Yulang.Roles.RoleDecls)
  (state : Yulang.GeneralSourceState.State) (declaration : Yulang.GeneralDeclarations.Declaration)
  (capture : Yulang.GeneralDeclarationDemands.Capture),
  (List.map Yulang.GeneralDeclarations.Equation.name declaration.associated).Nodup →
    ∀ (name : Nat) (slot : Fin state.slots),
      Yulang.GeneralDictionaryVariableTerms.compile state roles declaration capture name =
          some (Yulang.Core.PresenceGeneration.TyTerm.var slot) ↔
        Yulang.GeneralDictionaryVariableTerms.Denotes roles declaration capture name
          (Yulang.Core.PresenceGeneration.TyTerm.var (state.source slot))
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryVariableMaterialization.compile_slot_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 63. compile_variable

- 分類: 健全性
- ソースモジュール: Yulang.GeneralDictionaryVariableMaterialization
- ソースファイル: lean/Yulang/GeneralDictionaryVariableMaterialization.lean
- 命題: 任意の compile 成功結果は何らかの slot の変数である。構成子項を生成するとは述べない。

### カーネル確認済みの型（#check @）

```lean
Yulang.GeneralDictionaryVariableMaterialization.compile_variable : ∀ (roles : Yulang.Roles.RoleDecls)
  (state : Yulang.GeneralSourceState.State) (declaration : Yulang.GeneralDeclarations.Declaration)
  (capture : Yulang.GeneralDeclarationDemands.Capture) (name : Nat)
  (term : Yulang.Core.PresenceGeneration.TyTerm (Fin state.slots)),
  Yulang.GeneralDictionaryVariableTerms.compile state roles declaration capture name = some term →
    ∃ slot, term = Yulang.Core.PresenceGeneration.TyTerm.var slot
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryVariableMaterialization.compile_variable' depends on axioms: [propext, Quot.sound]
```

## 64. build_exact

- 分類: 完全性
- ソースモジュール: Yulang.GeneralDictionaryVariableMaterialization
- ソースファイル: lean/Yulang/GeneralDictionaryVariableMaterialization.lean
- 命題: 関連方程式名が重複しない任意の宣言・capture・inputs・located について、build の成功は Materializes と同値。後者は lower／upper／head／target の保存と、各出力が実際の Denotes を持つ source slot 変数であることを独立に要求する。

### カーネル確認済みの型（#check @）

```lean
@Yulang.GeneralDictionaryVariableMaterialization.build_exact : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State} {demand : Yulang.GeneralSourceState.Demand roles}
  (declaration : Yulang.GeneralDeclarations.Declaration) (capture : Yulang.GeneralDeclarationDemands.Capture),
  (List.map Yulang.GeneralDeclarations.Equation.name declaration.associated).Nodup →
    ∀ (inputs : Yulang.GeneralDictionaryBinderLocations.Inputs state demand)
      (located : Yulang.GeneralDictionaryStateEquations.Located state demand),
      Yulang.GeneralDictionaryVariableTerms.build declaration capture inputs = some located ↔
        Yulang.GeneralDictionaryVariableMaterialization.Materializes declaration capture inputs located
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryVariableMaterialization.build_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 65. build_none_exact

- 分類: 完全性
- ソースモジュール: Yulang.GeneralDictionaryVariableMaterialization
- ソースファイル: lean/Yulang/GeneralDictionaryVariableMaterialization.lean
- 命題: 関連方程式名が重複しない場合、build が none を返すことと、同じ宣言・capture・inputs を Materializes する located が一つも存在しないことは同値。

### カーネル確認済みの型（#check @）

```lean
@Yulang.GeneralDictionaryVariableMaterialization.build_none_exact : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State} {demand : Yulang.GeneralSourceState.Demand roles}
  (declaration : Yulang.GeneralDeclarations.Declaration) (capture : Yulang.GeneralDeclarationDemands.Capture),
  (List.map Yulang.GeneralDeclarations.Equation.name declaration.associated).Nodup →
    ∀ (inputs : Yulang.GeneralDictionaryBinderLocations.Inputs state demand),
      Yulang.GeneralDictionaryVariableTerms.build declaration capture inputs = none ↔
        ∀ (located : Yulang.GeneralDictionaryStateEquations.Located state demand),
          ¬Yulang.GeneralDictionaryVariableMaterialization.Materializes declaration capture inputs located
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryVariableMaterialization.build_none_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 66. plan_lookup_exact

- 分類: 完全性
- ソースモジュール: Yulang.GeneralDictionaryVariableMaterialization
- ソースファイル: lean/Yulang/GeneralDictionaryVariableMaterialization.lean
- 命題: 検査済み registry の任意の lookup 結果について、成功は、ID・役割が一致する可視宣言、その capture に対する Materializes、および生成された子列との一致が同時に存在することと同値。

### カーネル確認済みの型（#check @）

```lean
@Yulang.GeneralDictionaryVariableMaterialization.plan_lookup_exact : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frame : Yulang.GeneralDictionaryEmissionPlans.Frame registry.roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles) (key : Nat)
  (inputs : Yulang.GeneralDictionaryBinderLocations.Inputs state root.demand)
  (result : Yulang.GeneralDictionaryVariablePlans.Result state root),
  Yulang.GeneralDictionaryVariablePlans.lookup registry checked frame root key inputs = some result ↔
    ∃ declaration present,
      declaration.id = key ∧
        declaration.role = root.demand.role ∧
          Yulang.GeneralDictionaryVariableMaterialization.Materializes declaration (frame.capture declaration.id) inputs
              result.located ∧
            result.children = Yulang.GeneralDictionaryEmissionPlans.children frame root declaration ⋯
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryVariableMaterialization.plan_lookup_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 67. bodyTerm_reorders

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryVariableOrder
- ソースファイル: lean/Yulang/GeneralDictionaryVariableOrder.lean
- 命題: DeclarationReorders を満たす二宣言について、同じ capture・body の bodyTerm 結果は等しい。

### カーネル確認済みの型（#check @）

```lean
@Yulang.GeneralDictionaryVariableOrder.bodyTerm_reorders : ∀ {first last : Yulang.GeneralDeclarations.Declaration},
  Yulang.GeneralRegistryReordering.DeclarationReorders first last →
    ∀ (capture : Yulang.GeneralDeclarationDemands.Capture) (body : Yulang.GeneralDictionaryAssociatedProvenance.Body),
      Yulang.GeneralDictionaryVariableTerms.bodyTerm first capture body =
        Yulang.GeneralDictionaryVariableTerms.bodyTerm last capture body
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryVariableOrder.bodyTerm_reorders' depends on axioms: [propext, Quot.sound]
```

## 68. term_lookup_reorders

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryVariableOrder
- ソースファイル: lean/Yulang/GeneralDictionaryVariableOrder.lean
- 命題: DeclarationReorders を満たす二宣言について、同じ roles・capture・名前の変数項 lookup 結果は等しい。

### カーネル確認済みの型（#check @）

```lean
@Yulang.GeneralDictionaryVariableOrder.term_lookup_reorders : ∀ {first last : Yulang.GeneralDeclarations.Declaration}
  (roles : Yulang.Roles.RoleDecls),
  Yulang.GeneralRegistryReordering.DeclarationReorders first last →
    ∀ (capture : Yulang.GeneralDeclarationDemands.Capture) (name : Nat),
      Yulang.GeneralDictionaryVariableTerms.lookup roles first capture name =
        Yulang.GeneralDictionaryVariableTerms.lookup roles last capture name
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryVariableOrder.term_lookup_reorders' depends on axioms: [propext, Quot.sound]
```

## 69. compile_reorders

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryVariableOrder
- ソースファイル: lean/Yulang/GeneralDictionaryVariableOrder.lean
- 命題: DeclarationReorders を満たす二宣言について、同じ roles・state・capture・名前の compile 結果は等しい。

### カーネル確認済みの型（#check @）

```lean
@Yulang.GeneralDictionaryVariableOrder.compile_reorders : ∀ {first last : Yulang.GeneralDeclarations.Declaration}
  (roles : Yulang.Roles.RoleDecls) (state : Yulang.GeneralSourceState.State),
  Yulang.GeneralRegistryReordering.DeclarationReorders first last →
    ∀ (capture : Yulang.GeneralDeclarationDemands.Capture) (name : Nat),
      Yulang.GeneralDictionaryVariableTerms.compile state roles first capture name =
        Yulang.GeneralDictionaryVariableTerms.compile state roles last capture name
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryVariableOrder.compile_reorders' depends on axioms: [propext, Quot.sound]
```

## 70. build_reorders

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryVariableOrder
- ソースファイル: lean/Yulang/GeneralDictionaryVariableOrder.lean
- 命題: DeclarationReorders を満たす二宣言について、同じ capture・inputs の build 結果は等しい。

### カーネル確認済みの型（#check @）

```lean
@Yulang.GeneralDictionaryVariableOrder.build_reorders : ∀ {state : Yulang.GeneralSourceState.State}
  {first last : Yulang.GeneralDeclarations.Declaration} {roles : Yulang.Roles.RoleDecls}
  {demand : Yulang.GeneralSourceState.Demand roles},
  Yulang.GeneralRegistryReordering.DeclarationReorders first last →
    ∀ (capture : Yulang.GeneralDeclarationDemands.Capture)
      (inputs : Yulang.GeneralDictionaryBinderLocations.Inputs state demand),
      Yulang.GeneralDictionaryVariableTerms.build first capture inputs =
        Yulang.GeneralDictionaryVariableTerms.build last capture inputs
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryVariableOrder.build_reorders' depends on axioms: [propext, Quot.sound]
```

## 71. lookup_reorders_forward

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryVariableOrder
- ソースファイル: lean/Yulang/GeneralDictionaryVariableOrder.lean
- 命題: 同じ constructors／roles を持つ検査済み二 registry が Reorders を満たすなら、同じ frame・根・key・inputs で最初の lookup が返す result を後の lookup も返す。

### カーネル確認済みの型（#check @）

```lean
@Yulang.GeneralDictionaryVariableOrder.lookup_reorders_forward : ∀ {state : Yulang.GeneralSourceState.State}
  (constructors : Yulang.GeneralDeclarationPatterns.Constructors) (roles : Yulang.Roles.RoleDecls)
  (first last : List Yulang.GeneralDeclarations.Declaration)
  (one : Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := first })
  (two : Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := last }),
  Yulang.GeneralRegistryReordering.Reorders { constructors := constructors, roles := roles, declarations := first }
      { constructors := constructors, roles := roles, declarations := last } →
    ∀ (frame : Yulang.GeneralDictionaryEmissionPlans.Frame roles)
      (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (key : Nat)
      (inputs : Yulang.GeneralDictionaryBinderLocations.Inputs state root.demand)
      (result : Yulang.GeneralDictionaryVariablePlans.Result state root),
      Yulang.GeneralDictionaryVariablePlans.lookup
            { constructors := constructors, roles := roles, declarations := first } one frame root key inputs =
          some result →
        Yulang.GeneralDictionaryVariablePlans.lookup
            { constructors := constructors, roles := roles, declarations := last } two frame root key inputs =
          some result
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryVariableOrder.lookup_reorders_forward' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 72. lookup_reorders

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryVariableOrder
- ソースファイル: lean/Yulang/GeneralDictionaryVariableOrder.lean
- 命題: 同じ constructors／roles を持つ検査済み二 registry が Reorders を満たすなら、同じ frame・根・key・inputs の lookup 結果全体が等しい。探索候補の選択や最終状態の順序独立性は主張しない。

### カーネル確認済みの型（#check @）

```lean
@Yulang.GeneralDictionaryVariableOrder.lookup_reorders : ∀ {state : Yulang.GeneralSourceState.State}
  (constructors : Yulang.GeneralDeclarationPatterns.Constructors) (roles : Yulang.Roles.RoleDecls)
  (first last : List Yulang.GeneralDeclarations.Declaration)
  (one : Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := first })
  (two : Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := last }),
  Yulang.GeneralRegistryReordering.Reorders { constructors := constructors, roles := roles, declarations := first }
      { constructors := constructors, roles := roles, declarations := last } →
    ∀ (frame : Yulang.GeneralDictionaryEmissionPlans.Frame roles)
      (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (key : Nat)
      (inputs : Yulang.GeneralDictionaryBinderLocations.Inputs state root.demand),
      Yulang.GeneralDictionaryVariablePlans.lookup
          { constructors := constructors, roles := roles, declarations := first } one frame root key inputs =
        Yulang.GeneralDictionaryVariablePlans.lookup
          { constructors := constructors, roles := roles, declarations := last } two frame root key inputs
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryVariableOrder.lookup_reorders' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 73. lookup_exact

- 分類: 完全性
- ソースモジュール: Yulang.GeneralDictionaryVariablePlans
- ソースファイル: lean/Yulang/GeneralDictionaryVariablePlans.lean
- 命題: 任意の検査済み registry・frame・根・key・inputs・result について、入力単一点も扱う変数 lookup がその result を返すことと、可視宣言が存在し、ID と役割が一致し、その capture で build が result.located を返し、子列が当該宣言の生成列に等しいことは同値。

### カーネル確認済みの型（#check @）

```lean
@Yulang.GeneralDictionaryVariablePlans.lookup_exact : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frame : Yulang.GeneralDictionaryEmissionPlans.Frame registry.roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles) (key : Nat)
  (inputs : Yulang.GeneralDictionaryBinderLocations.Inputs state root.demand)
  (result : Yulang.GeneralDictionaryVariablePlans.Result state root),
  Yulang.GeneralDictionaryVariablePlans.lookup registry checked frame root key inputs = some result ↔
    ∃ declaration present,
      declaration.id = key ∧
        declaration.role = root.demand.role ∧
          Yulang.GeneralDictionaryVariableTerms.build declaration (frame.capture declaration.id) inputs =
              some result.located ∧
            result.children = Yulang.GeneralDictionaryEmissionPlans.children frame root declaration ⋯
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryVariablePlans.lookup_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 74. build_head

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryVariablePlans
- ソースファイル: lean/Yulang/GeneralDictionaryVariablePlans.lean
- 命題: build が located を返した場合、その head は入力で与えた head に等しい。

### カーネル確認済みの型（#check @）

```lean
@Yulang.GeneralDictionaryVariablePlans.build_head : ∀ {state : Yulang.GeneralSourceState.State}
  {roles : Yulang.Roles.RoleDecls} {demand : Yulang.GeneralSourceState.Demand roles}
  (declaration : Yulang.GeneralDeclarations.Declaration) (capture : Yulang.GeneralDeclarationDemands.Capture)
  (inputs : Yulang.GeneralDictionaryBinderLocations.Inputs state demand)
  (located : Yulang.GeneralDictionaryStateEquations.Located state demand),
  Yulang.GeneralDictionaryVariableTerms.build declaration capture inputs = some located → located.head = inputs.head
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryVariablePlans.build_head' depends on axioms: [propext, Quot.sound]
```

## 75. lookup_plan

- 分類: 健全性
- ソースモジュール: Yulang.GeneralDictionaryVariablePlans
- ソースファイル: lean/Yulang/GeneralDictionaryVariablePlans.lean
- 命題: 入力単一点も扱う変数 lookup が result を返せば、その子列は指定した根と key の Plan を満たす。

### カーネル確認済みの型（#check @）

```lean
@Yulang.GeneralDictionaryVariablePlans.lookup_plan : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frame : Yulang.GeneralDictionaryEmissionPlans.Frame registry.roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles) (key : Nat)
  (inputs : Yulang.GeneralDictionaryBinderLocations.Inputs state root.demand)
  (result : Yulang.GeneralDictionaryVariablePlans.Result state root),
  Yulang.GeneralDictionaryVariablePlans.lookup registry checked frame root key inputs = some result →
    Yulang.GeneralDictionaryEmissionPlans.Plan registry checked frame root key result.children
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryVariablePlans.lookup_plan' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 76. lookup_terms

- 分類: 健全性
- ソースモジュール: Yulang.GeneralDictionaryVariablePlans
- ソースファイル: lean/Yulang/GeneralDictionaryVariablePlans.lean
- 命題: 入力単一点も扱う変数 lookup の成功に加え、該当 ID・役割の全可視宣言について supplied head が指定の HeadInstances を満たすと仮定すると、返された located は Terms を満たす。

### カーネル確認済みの型（#check @）

```lean
@Yulang.GeneralDictionaryVariablePlans.lookup_terms : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (heads : Yulang.GeneralDictionaryVariablePlans.HeadInstances registry.roles state)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles) (key : Nat)
  (inputs : Yulang.GeneralDictionaryBinderLocations.Inputs state root.demand)
  (result : Yulang.GeneralDictionaryVariablePlans.Result state root),
  Yulang.GeneralDictionaryVariablePlans.lookup registry checked (frames root) root key inputs = some result →
    (∀ (declaration : Yulang.GeneralDeclarations.Declaration),
        declaration ∈ registry.declarations →
          declaration.id = key →
            declaration.role = root.demand.role →
              heads root declaration ((frames root).capture declaration.id) inputs.head) →
      Yulang.GeneralDictionaryVariablePlans.Terms registry frames heads root key result.located
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryVariablePlans.lookup_terms' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 77. lookup_output_plan

- 分類: 健全性
- ソースモジュール: Yulang.GeneralDictionaryVariablePlans
- ソースファイル: lean/Yulang/GeneralDictionaryVariablePlans.lean
- 命題: 入力単一点も扱う変数 lookup の成功から、ID・役割が一致する同一の可視宣言が存在し、その宣言に由来する子列・出力の OutputPlan と、その capture に対する located の Interpreted が同時に成り立つ。

### カーネル確認済みの型（#check @）

```lean
@Yulang.GeneralDictionaryVariablePlans.lookup_output_plan : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frame : Yulang.GeneralDictionaryEmissionPlans.Frame registry.roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles) (key : Nat)
  (inputs : Yulang.GeneralDictionaryBinderLocations.Inputs state root.demand)
  (result : Yulang.GeneralDictionaryVariablePlans.Result state root),
  Yulang.GeneralDictionaryVariablePlans.lookup registry checked frame root key inputs = some result →
    ∃ declaration _present,
      declaration.id = key ∧
        declaration.role = root.demand.role ∧
          Yulang.GeneralDictionaryPlannedOutputs.OutputPlan registry checked frame root key
              (result.children,
                Yulang.GeneralDictionaryAssociatedProvenance.outputs registry.roles declaration root.demand) ∧
            Yulang.GeneralDictionaryVariableTerms.Interpreted declaration (frame.capture declaration.id) result.located
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryVariablePlans.lookup_output_plan' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 78. prepare_node_exact

- 分類: 完全性
- ソースモジュール: Yulang.GeneralDictionaryVariablePreparation
- ソースファイル: lean/Yulang/GeneralDictionaryVariablePreparation.lean
- 命題: 任意の node recipe の prepare 成功は、根の lookup 成功、すべての子 recipe の再帰的 prepare 成功、準備した子の根列と lookup の要求子列の完全一致、および返却木の対応する node 形状が同時に成り立つことと同値。

### カーネル確認済みの型（#check @）

```lean
@Yulang.GeneralDictionaryVariablePreparation.prepare_node_exact : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles) (key : Nat)
  (inputs : Yulang.GeneralDictionaryBinderLocations.Inputs state root.demand)
  (children : List (Yulang.GeneralDictionaryVariablePreparation.Recipe registry.roles state))
  (tree : Yulang.GeneralDictionaryTransactions.Prepared registry.roles state),
  Yulang.GeneralDictionaryVariablePreparation.prepare registry checked frames
        (Yulang.GeneralDictionaryVariablePreparation.Recipe.node root key inputs children) =
      some tree ↔
    ∃ result,
      Yulang.GeneralDictionaryVariablePlans.lookup registry checked (frames root) root key inputs = some result ∧
        ∃ prepared,
          List.mapM (Yulang.GeneralDictionaryVariablePreparation.prepare registry checked frames) children =
              some prepared ∧
            List.map Yulang.GeneralDictionaryTransactions.Prepared.root prepared = result.children ∧
              tree = Yulang.GeneralDictionaryTransactions.Prepared.node root key result.located prepared
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryVariablePreparation.prepare_node_exact' depends on axioms: [propext, Quot.sound]
```

## 79. prepare_root

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryVariablePreparation
- ソースファイル: lean/Yulang/GeneralDictionaryVariablePreparation.lean
- 命題: 任意の recipe の prepare が tree を返せば、tree の根は元 recipe の根に等しい。

### カーネル確認済みの型（#check @）

```lean
@Yulang.GeneralDictionaryVariablePreparation.prepare_root : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (recipe : Yulang.GeneralDictionaryVariablePreparation.Recipe registry.roles state)
  (tree : Yulang.GeneralDictionaryTransactions.Prepared registry.roles state),
  Yulang.GeneralDictionaryVariablePreparation.prepare registry checked frames recipe = some tree →
    tree.root = recipe.root
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryVariablePreparation.prepare_root' depends on axioms: [propext, Quot.sound]
```

## 80. prepare_built

- 分類: 健全性
- ソースモジュール: Yulang.GeneralDictionaryVariablePreparation
- ソースファイル: lean/Yulang/GeneralDictionaryVariablePreparation.lean
- 命題: recipe が明示的な Heads 条件を満たし prepare が成功した場合、結果木は同じ registry・frames・heads の Built を満たす。

### カーネル確認済みの型（#check @）

```lean
@Yulang.GeneralDictionaryVariablePreparation.prepare_built : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (heads : Yulang.GeneralDictionaryVariablePlans.HeadInstances registry.roles state)
  (recipe : Yulang.GeneralDictionaryVariablePreparation.Recipe registry.roles state),
  Yulang.GeneralDictionaryVariablePreparation.Heads registry frames heads recipe →
    ∀ (tree : Yulang.GeneralDictionaryTransactions.Prepared registry.roles state),
      Yulang.GeneralDictionaryVariablePreparation.prepare registry checked frames recipe = some tree →
        Yulang.GeneralDictionaryVariableTransactions.Built registry checked frames heads tree
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryVariablePreparation.prepare_built' depends on axioms: [propext, Quot.sound]
```

## 81. prepare_uniform

- 分類: 健全性
- ソースモジュール: Yulang.GeneralDictionaryVariablePreparation
- ソースファイル: lean/Yulang/GeneralDictionaryVariablePreparation.lean
- 命題: recipe の Heads 条件と prepare 成功を仮定すると、消去辞書から recipe の根への一つの Readback witness が存在し、記録を満たすすべての assignment について同じ witness が SourceInstance の Evidence を持つ。モデルの存在や任意 recipe の成功は主張しない。

### カーネル確認済みの型（#check @）

```lean
@Yulang.GeneralDictionaryVariablePreparation.prepare_uniform : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (heads : Yulang.GeneralDictionaryVariablePlans.HeadInstances registry.roles state)
  (recipe : Yulang.GeneralDictionaryVariablePreparation.Recipe registry.roles state),
  Yulang.GeneralDictionaryVariablePreparation.Heads registry frames heads recipe →
    ∀ (tree : Yulang.GeneralDictionaryTransactions.Prepared registry.roles state),
      Yulang.GeneralDictionaryVariablePreparation.prepare registry checked frames recipe = some tree →
        ∃ witness,
          Yulang.GeneralSourceDictionaries.Readback recipe.root (Yulang.GeneralSourceDictionaries.erase tree.dictionary)
              witness ∧
            ∀ (assignment : Yulang.GeneralSourceState.Assignment),
              Yulang.GeneralSourceState.Models (Yulang.GeneralDictionaryBatchRecording.record tree.items) assignment →
                Yulang.GeneralSourceDictionaries.Evidence
                  (Yulang.GeneralDictionaryVariableTransactions.SourceInstance registry checked frames heads assignment)
                  witness
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryVariablePreparation.prepare_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 82. singleton_value

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryVariableRealization
- ソースファイル: lean/Yulang/GeneralDictionaryVariableRealization.lean
- 命題: capture の入力両端が同じ source ID であり、値が assignment 上でその両端の部分型区間内にあるなら、その値は端点の値と同値である。

### カーネル確認済みの型（#check @）

```lean
Yulang.GeneralDictionaryVariableRealization.singleton_value : ∀ (capture : Yulang.GeneralDeclarationDemands.Capture)
  (assignment : Yulang.GeneralSourceState.Assignment) (binder : Nat) (value : Yulang.Common.Ty),
  (capture.inputs binder).fst = (capture.inputs binder).snd →
    Yulang.Common.Subtype (assignment (capture.inputs binder).fst).fst value ∧
        Yulang.Common.Subtype value (assignment (capture.inputs binder).snd).fst →
      Yulang.Common.Equivalent value (assignment (capture.inputs binder).fst).fst
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryVariableRealization.singleton_value' depends on axioms: [propext, Quot.sound]
```

## 83. denotes_realization

- 分類: 健全性
- ソースモジュール: Yulang.GeneralDictionaryVariableRealization
- ソースファイル: lean/Yulang/GeneralDictionaryVariableRealization.lean
- 命題: 与えた assignment と束縛子値が capture の Realizes 条件を満たし、名前の項が Denotes を満たすなら、明示的 RHS が変数に正規化される供給方程式と束縛子が存在し、その束縛子値は項の評価と同値になる。

### カーネル確認済みの型（#check @）

```lean
Yulang.GeneralDictionaryVariableRealization.denotes_realization : ∀ (roles : Yulang.Roles.RoleDecls)
  (declaration : Yulang.GeneralDeclarations.Declaration) (capture : Yulang.GeneralDeclarationDemands.Capture)
  (assignment : Yulang.GeneralSourceState.Assignment) (values : Nat → Yulang.Common.Ty),
  Yulang.GeneralDictionaryVariableRealization.Realizes declaration capture assignment values →
    ∀ (name : Nat) (term : Yulang.Core.PresenceGeneration.TyTerm Nat),
      Yulang.GeneralDictionaryVariableTerms.Denotes roles declaration capture name term →
        ∃ equation binder,
          Yulang.GeneralDictionaryAssociatedProvenance.Supplies roles declaration name
              (Yulang.GeneralDictionaryAssociatedProvenance.Body.explicit equation) ∧
            Yulang.GeneralDeclarationPatterns.normalize equation.rhs =
                Yulang.GeneralDeclarationPatterns.Pattern.var binder ∧
              Yulang.Common.Equivalent (values binder)
                (Yulang.Core.PresenceGeneration.TyTerm.eval Yulang.Common.model assignment term)
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryVariableRealization.denotes_realization' depends on axioms: [propext, Quot.sound]
```

## 84. built_output_realization

- 分類: 健全性
- ソースモジュール: Yulang.GeneralDictionaryVariableRealization
- ソースファイル: lean/Yulang/GeneralDictionaryVariableRealization.lean
- 命題: 関連方程式名が重複せず build が成功し、located の記録のモデルと capture を Realizes する束縛子値を与えると、各要求出力に変数 RHS の供給方程式と束縛子が存在し、要求先の値はその束縛子値と同値になる。

### カーネル確認済みの型（#check @）

```lean
@Yulang.GeneralDictionaryVariableRealization.built_output_realization : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State} {demand : Yulang.GeneralSourceState.Demand roles}
  (declaration : Yulang.GeneralDeclarations.Declaration) (capture : Yulang.GeneralDeclarationDemands.Capture),
  (List.map Yulang.GeneralDeclarations.Equation.name declaration.associated).Nodup →
    ∀ (inputs : Yulang.GeneralDictionaryBinderLocations.Inputs state demand)
      (located : Yulang.GeneralDictionaryStateEquations.Located state demand),
      Yulang.GeneralDictionaryVariableTerms.build declaration capture inputs = some located →
        ∀ (assignment : Yulang.GeneralSourceState.Assignment),
          Yulang.GeneralSourceState.Models (Yulang.GeneralDictionaryEquationRecording.record located) assignment →
            ∀ (values : Nat → Yulang.Common.Ty),
              Yulang.GeneralDictionaryVariableRealization.Realizes declaration capture assignment values →
                ∀ (index : Fin demand.outputs.length),
                  ∃ equation binder,
                    Yulang.GeneralDictionaryAssociatedProvenance.Supplies roles declaration demand.outputs[index].name
                        (Yulang.GeneralDictionaryAssociatedProvenance.Body.explicit equation) ∧
                      Yulang.GeneralDeclarationPatterns.normalize equation.rhs =
                          Yulang.GeneralDeclarationPatterns.Pattern.var binder ∧
                        Yulang.Common.Equivalent (assignment demand.outputs[index].target).fst (values binder)
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryVariableRealization.built_output_realization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 85. lookup_exact

- 分類: 完全性
- ソースモジュール: Yulang.GeneralDictionaryVariableTerms
- ソースファイル: lean/Yulang/GeneralDictionaryVariableTerms.lean
- 命題: 関連方程式名に重複がない任意の宣言・capture・名前・項について、lookup がその項を返すことと Denotes は同値。Denotes は実際の明示的 RHS が変数に正規化され、出力束縛子の capture または両端の source ID が等しい入力束縛子の capture に由来することを要求する。

### カーネル確認済みの型（#check @）

```lean
Yulang.GeneralDictionaryVariableTerms.lookup_exact : ∀ (roles : Yulang.Roles.RoleDecls)
  (declaration : Yulang.GeneralDeclarations.Declaration) (capture : Yulang.GeneralDeclarationDemands.Capture),
  (List.map Yulang.GeneralDeclarations.Equation.name declaration.associated).Nodup →
    ∀ (name : Nat) (term : Yulang.Core.PresenceGeneration.TyTerm Nat),
      Yulang.GeneralDictionaryVariableTerms.lookup roles declaration capture name = some term ↔
        Yulang.GeneralDictionaryVariableTerms.Denotes roles declaration capture name term
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryVariableTerms.lookup_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 86. output_lookup_preserved

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryVariableTerms
- ソースファイル: lean/Yulang/GeneralDictionaryVariableTerms.lean
- 命題: 関連方程式名が重複しないとき、旧出力束縛子専用 lookup の成功は同じ項を返す新 lookup の成功として保存される。

### カーネル確認済みの型（#check @）

```lean
Yulang.GeneralDictionaryVariableTerms.output_lookup_preserved : ∀ (roles : Yulang.Roles.RoleDecls)
  (declaration : Yulang.GeneralDeclarations.Declaration) (capture : Yulang.GeneralDeclarationDemands.Capture),
  (List.map Yulang.GeneralDeclarations.Equation.name declaration.associated).Nodup →
    ∀ (name : Nat) (term : Yulang.Core.PresenceGeneration.TyTerm Nat),
      Yulang.GeneralDictionaryOutputBinderTerms.lookup roles declaration capture name = some term →
        Yulang.GeneralDictionaryVariableTerms.lookup roles declaration capture name = some term
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryVariableTerms.output_lookup_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 87. compile_interpreted

- 分類: 健全性
- ソースモジュール: Yulang.GeneralDictionaryVariableTerms
- ソースファイル: lean/Yulang/GeneralDictionaryVariableTerms.lean
- 命題: 任意の compile 成功項を state の source map で持ち上げると、同じ名前の lookup 結果になる。

### カーネル確認済みの型（#check @）

```lean
Yulang.GeneralDictionaryVariableTerms.compile_interpreted : ∀ (state : Yulang.GeneralSourceState.State)
  (roles : Yulang.Roles.RoleDecls) (declaration : Yulang.GeneralDeclarations.Declaration)
  (capture : Yulang.GeneralDeclarationDemands.Capture) (name : Nat)
  (term : Yulang.Core.PresenceGeneration.TyTerm (Fin state.slots)),
  Yulang.GeneralDictionaryVariableTerms.compile state roles declaration capture name = some term →
    Yulang.GeneralDictionaryVariableTerms.lookup roles declaration capture name =
      some (Yulang.GeneralDictionaryStateEquations.liftType state term)
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryVariableTerms.compile_interpreted' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 88. build_interpreted

- 分類: 健全性
- ソースモジュール: Yulang.GeneralDictionaryVariableTerms
- ソースファイル: lean/Yulang/GeneralDictionaryVariableTerms.lean
- 命題: 任意の build 成功結果は、与えた宣言・capture に対する Interpreted を満たす。

### カーネル確認済みの型（#check @）

```lean
@Yulang.GeneralDictionaryVariableTerms.build_interpreted : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State} {demand : Yulang.GeneralSourceState.Demand roles}
  (declaration : Yulang.GeneralDeclarations.Declaration) (capture : Yulang.GeneralDeclarationDemands.Capture)
  (inputs : Yulang.GeneralDictionaryBinderLocations.Inputs state demand)
  (located : Yulang.GeneralDictionaryStateEquations.Located state demand),
  Yulang.GeneralDictionaryVariableTerms.build declaration capture inputs = some located →
    Yulang.GeneralDictionaryVariableTerms.Interpreted declaration capture located
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryVariableTerms.build_interpreted' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 89. build_head

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryVariableTerms
- ソースファイル: lean/Yulang/GeneralDictionaryVariableTerms.lean
- 命題: build が located を返した場合、その head は入力で与えた head に等しい。

### カーネル確認済みの型（#check @）

```lean
@Yulang.GeneralDictionaryVariableTerms.build_head : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State} {demand : Yulang.GeneralSourceState.Demand roles}
  (declaration : Yulang.GeneralDeclarations.Declaration) (capture : Yulang.GeneralDeclarationDemands.Capture)
  (inputs : Yulang.GeneralDictionaryBinderLocations.Inputs state demand)
  (located : Yulang.GeneralDictionaryStateEquations.Located state demand),
  Yulang.GeneralDictionaryVariableTerms.build declaration capture inputs = some located → located.head = inputs.head
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryVariableTerms.build_head' depends on axioms: [propext, Quot.sound]
```

## 90. build_output_denotes

- 分類: 健全性
- ソースモジュール: Yulang.GeneralDictionaryVariableTerms
- ソースファイル: lean/Yulang/GeneralDictionaryVariableTerms.lean
- 命題: 関連方程式名が重複せず build が成功した場合、各要求出力位置の方程式出力はその名前の Denotes を満たす。

### カーネル確認済みの型（#check @）

```lean
@Yulang.GeneralDictionaryVariableTerms.build_output_denotes : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State} {demand : Yulang.GeneralSourceState.Demand roles}
  (declaration : Yulang.GeneralDeclarations.Declaration) (capture : Yulang.GeneralDeclarationDemands.Capture),
  (List.map Yulang.GeneralDeclarations.Equation.name declaration.associated).Nodup →
    ∀ (inputs : Yulang.GeneralDictionaryBinderLocations.Inputs state demand)
      (located : Yulang.GeneralDictionaryStateEquations.Located state demand),
      Yulang.GeneralDictionaryVariableTerms.build declaration capture inputs = some located →
        ∀ (index : Fin demand.outputs.length),
          Yulang.GeneralDictionaryVariableTerms.Denotes roles declaration capture demand.outputs[index].name
            (located.equations.output index)
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryVariableTerms.build_output_denotes' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 91. built_output_models

- 分類: 健全性
- ソースモジュール: Yulang.GeneralDictionaryVariableTerms
- ソースファイル: lean/Yulang/GeneralDictionaryVariableTerms.lean
- 命題: 関連方程式名が重複せず build が成功し、その located の記録のモデルを与えた場合、各出力位置で Denotes が成り立ち、要求先の値は出力項の評価と同値になる。

### カーネル確認済みの型（#check @）

```lean
@Yulang.GeneralDictionaryVariableTerms.built_output_models : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State} {demand : Yulang.GeneralSourceState.Demand roles}
  (declaration : Yulang.GeneralDeclarations.Declaration) (capture : Yulang.GeneralDeclarationDemands.Capture),
  (List.map Yulang.GeneralDeclarations.Equation.name declaration.associated).Nodup →
    ∀ (inputs : Yulang.GeneralDictionaryBinderLocations.Inputs state demand)
      (located : Yulang.GeneralDictionaryStateEquations.Located state demand),
      Yulang.GeneralDictionaryVariableTerms.build declaration capture inputs = some located →
        ∀ (assignment : Yulang.GeneralSourceState.Assignment),
          Yulang.GeneralSourceState.Models (Yulang.GeneralDictionaryEquationRecording.record located) assignment →
            ∀ (index : Fin demand.outputs.length),
              Yulang.GeneralDictionaryVariableTerms.Denotes roles declaration capture demand.outputs[index].name
                  (located.equations.output index) ∧
                Yulang.Common.Equivalent (assignment demand.outputs[index].target).fst
                  (Yulang.Core.PresenceGeneration.TyTerm.eval Yulang.Common.model assignment
                    (located.equations.output index))
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryVariableTerms.built_output_models' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 92. built_valid

- 分類: 健全性
- ソースモジュール: Yulang.GeneralDictionaryVariableTransactions
- ソースファイル: lean/Yulang/GeneralDictionaryVariableTransactions.lean
- 命題: 任意の検査済み registry、frames、heads、準備木について、変数出力 Built なら、対応する Terms を用いた Valid が成り立つ。

### カーネル確認済みの型（#check @）

```lean
@Yulang.GeneralDictionaryVariableTransactions.built_valid : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (heads : Yulang.GeneralDictionaryVariablePlans.HeadInstances registry.roles state)
  (tree : Yulang.GeneralDictionaryTransactions.Prepared registry.roles state),
  Yulang.GeneralDictionaryVariableTransactions.Built registry checked frames heads tree →
    Yulang.GeneralDictionaryTransactions.Valid registry checked frames
      (Yulang.GeneralDictionaryVariablePlans.Terms registry frames heads) tree
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryVariableTransactions.built_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 93. transaction_stored

- 分類: 健全性
- ソースモジュール: Yulang.GeneralDictionaryVariableTransactions
- ソースファイル: lean/Yulang/GeneralDictionaryVariableTransactions.lean
- 命題: 明示的 frames／heads に対する 変数出力 Built を満たす木の辞書は、木の items で持ち上げた Terms と Plan に基づく StoredInstance の Evidence を持つ。

### カーネル確認済みの型（#check @）

```lean
@Yulang.GeneralDictionaryVariableTransactions.transaction_stored : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (heads : Yulang.GeneralDictionaryVariablePlans.HeadInstances registry.roles state)
  (tree : Yulang.GeneralDictionaryTransactions.Prepared registry.roles state),
  Yulang.GeneralDictionaryVariableTransactions.Built registry checked frames heads tree →
    Yulang.GeneralSourceDictionaries.Evidence
      (Yulang.GeneralDictionaryModelEvidence.StoredInstance
        (Yulang.GeneralDictionaryTransactions.PlannedAt registry checked frames
          (Yulang.GeneralDictionaryTransactions.LiftedTerms tree.items
            (Yulang.GeneralDictionaryVariablePlans.Terms registry frames heads))))
      tree.dictionary
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryVariableTransactions.transaction_stored' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 94. lifted_source_instance

- 分類: 健全性
- ソースモジュール: Yulang.GeneralDictionaryVariableTransactions
- ソースファイル: lean/Yulang/GeneralDictionaryVariableTransactions.lean
- 命題: 任意の items・assignment・根・key・子列について、持ち上げた 変数出力 Terms と Plan の ModelInstance があれば、対応する SourceInstance が成り立つ。

### カーネル確認済みの型（#check @）

```lean
@Yulang.GeneralDictionaryVariableTransactions.lifted_source_instance : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (heads : Yulang.GeneralDictionaryVariablePlans.HeadInstances registry.roles state)
  (items : List (Yulang.GeneralDictionaryBatchRecording.Item registry.roles state))
  (assignment : Yulang.GeneralSourceState.Assignment)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles) (key : Nat)
  (children : List (Yulang.GeneralSourceDictionaries.Occurrence registry.roles)),
  Yulang.GeneralDictionaryModelEvidence.ModelInstance
      (Yulang.GeneralDictionaryTransactions.PlannedAt registry checked frames
        (Yulang.GeneralDictionaryTransactions.LiftedTerms items
          (Yulang.GeneralDictionaryVariablePlans.Terms registry frames heads)))
      assignment root key children →
    Yulang.GeneralDictionaryVariableTransactions.SourceInstance registry checked frames heads assignment root key
      children
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryVariableTransactions.lifted_source_instance' depends on axioms: [propext, Quot.sound]
```

## 95. transaction_uniform

- 分類: 健全性
- ソースモジュール: Yulang.GeneralDictionaryVariableTransactions
- ソースファイル: lean/Yulang/GeneralDictionaryVariableTransactions.lean
- 命題: 明示的 frames／heads に対する 変数出力 Built を満たす木には、消去した辞書からの一つの Readback witness が存在し、記録した全 items を満たすすべての assignment で、その同じ witness が SourceInstance の Evidence を持つ。モデルの存在自体は結論に含まない。

### カーネル確認済みの型（#check @）

```lean
@Yulang.GeneralDictionaryVariableTransactions.transaction_uniform : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (heads : Yulang.GeneralDictionaryVariablePlans.HeadInstances registry.roles state)
  (tree : Yulang.GeneralDictionaryTransactions.Prepared registry.roles state),
  Yulang.GeneralDictionaryVariableTransactions.Built registry checked frames heads tree →
    ∃ witness,
      Yulang.GeneralSourceDictionaries.Readback tree.root (Yulang.GeneralSourceDictionaries.erase tree.dictionary)
          witness ∧
        ∀ (assignment : Yulang.GeneralSourceState.Assignment),
          Yulang.GeneralSourceState.Models (Yulang.GeneralDictionaryBatchRecording.record tree.items) assignment →
            Yulang.GeneralSourceDictionaries.Evidence
              (Yulang.GeneralDictionaryVariableTransactions.SourceInstance registry checked frames heads assignment)
              witness
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryVariableTransactions.transaction_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 96. source_instance_declaration

- 分類: 健全性
- ソースモジュール: Yulang.GeneralDictionaryVariableTransactions
- ソースファイル: lean/Yulang/GeneralDictionaryVariableTransactions.lean
- 命題: 任意の SourceInstance から、ID・役割が一致する可視宣言と located が存在し、子列が当該宣言の生成列に等しく、指定 heads、当該 capture の Interpreted、assignment における located の方程式成立を同時に満たす。

### カーネル確認済みの型（#check @）

```lean
@Yulang.GeneralDictionaryVariableTransactions.source_instance_declaration : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (heads : Yulang.GeneralDictionaryVariablePlans.HeadInstances registry.roles state)
  (assignment : Yulang.GeneralSourceState.Assignment)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles) (key : Nat)
  (children : List (Yulang.GeneralSourceDictionaries.Occurrence registry.roles)),
  Yulang.GeneralDictionaryVariableTransactions.SourceInstance registry checked frames heads assignment root key
      children →
    ∃ declaration present,
      declaration.id = key ∧
        declaration.role = root.demand.role ∧
          children = Yulang.GeneralDictionaryEmissionPlans.children (frames root) root declaration ⋯ ∧
            ∃ located,
              heads root declaration ((frames root).capture declaration.id) located.head ∧
                Yulang.GeneralDictionaryVariableTerms.Interpreted declaration ((frames root).capture declaration.id)
                    located ∧
                  located.equations.Holds assignment
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryVariableTransactions.source_instance_declaration' depends on axioms: [propext, Quot.sound]
```

## 97. source_output_denotes

- 分類: 健全性
- ソースモジュール: Yulang.GeneralDictionaryVariableTransactions
- ソースファイル: lean/Yulang/GeneralDictionaryVariableTransactions.lean
- 命題: 任意の SourceInstance と任意の要求出力位置について、ID・役割・子列の一致する可視宣言と出力項が存在し、その名前の 変数出力 Denotes が成り立ち、要求先の値はその項の assignment における評価と同値になる。

### カーネル確認済みの型（#check @）

```lean
@Yulang.GeneralDictionaryVariableTransactions.source_output_denotes : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (heads : Yulang.GeneralDictionaryVariablePlans.HeadInstances registry.roles state)
  (assignment : Yulang.GeneralSourceState.Assignment)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles) (key : Nat)
  (children : List (Yulang.GeneralSourceDictionaries.Occurrence registry.roles)),
  Yulang.GeneralDictionaryVariableTransactions.SourceInstance registry checked frames heads assignment root key
      children →
    ∀ (index : Fin root.demand.outputs.length),
      ∃ declaration present,
        declaration.id = key ∧
          declaration.role = root.demand.role ∧
            children = Yulang.GeneralDictionaryEmissionPlans.children (frames root) root declaration ⋯ ∧
              ∃ term,
                Yulang.GeneralDictionaryVariableTerms.Denotes registry.roles declaration
                    ((frames root).capture declaration.id) root.demand.outputs[index].name term ∧
                  Yulang.Common.Equivalent (assignment root.demand.outputs[index].target).fst
                    (Yulang.Core.PresenceGeneration.TyTerm.eval Yulang.Common.model assignment term)
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryVariableTransactions.source_output_denotes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 98. compileAt_exact

- 分類: 完全性
- ソースモジュール: Yulang.GeneralDictionaryVariableHeads
- ソースファイル: lean/Yulang/GeneralDictionaryVariableHeads.lean
- 命題: 任意の宣言・capture・位置・項について、compileAt の成功は DenotesAt と同値。実際の位置の head が入力変数に正規化され、capture 両端の source ID が同じで state 内に存在し、その slot の変数であることを要求する。

### カーネル確認済みの型（#check @）

```lean
Yulang.GeneralDictionaryVariableHeads.compileAt_exact : ∀ (state : Yulang.GeneralSourceState.State)
  (declaration : Yulang.GeneralDeclarations.Declaration) (capture : Yulang.GeneralDeclarationDemands.Capture)
  (index : Nat) (term : Yulang.Core.PresenceGeneration.TyTerm (Fin state.slots)),
  Yulang.GeneralDictionaryVariableHeads.compileAt state declaration capture index = some term ↔
    Yulang.GeneralDictionaryVariableHeads.DenotesAt state declaration capture index term
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryVariableHeads.compileAt_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 99. build_head_denotes

- 分類: 健全性
- ソースモジュール: Yulang.GeneralDictionaryVariableHeads
- ソースファイル: lean/Yulang/GeneralDictionaryVariableHeads.lean
- 命題: 検査済みで要求と役割が等しい宣言の headless build が成功した場合、返却 head は宣言の役割・長さと各位置の DenotesAt を含む HeadDenotes を満たす。

### カーネル確認済みの型（#check @）

```lean
@Yulang.GeneralDictionaryVariableHeads.build_head_denotes : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State} {demand : Yulang.GeneralSourceState.Demand roles}
  {constructors : Yulang.GeneralDeclarationPatterns.Constructors} (declaration : Yulang.GeneralDeclarations.Declaration)
  (checked : Yulang.GeneralDeclarations.DeclarationChecked constructors roles declaration)
  (sameRole : declaration.role = demand.role) (capture : Yulang.GeneralDeclarationDemands.Capture)
  (inputs : Yulang.GeneralDictionaryVariableHeads.HeadlessInputs state demand)
  (result : Yulang.GeneralDictionaryBinderLocations.Inputs state demand),
  Yulang.GeneralDictionaryVariableHeads.build declaration checked sameRole capture inputs = some result →
    Yulang.GeneralDictionaryVariableHeads.HeadDenotes declaration capture demand result.head
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryVariableHeads.build_head_denotes' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 100. build_preserves

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryVariableHeads
- ソースファイル: lean/Yulang/GeneralDictionaryVariableHeads.lean
- 命題: 検査済みで要求と役割が等しい宣言の headless build が成功した場合、lower／upper／target は入力のまま保存される。

### カーネル確認済みの型（#check @）

```lean
@Yulang.GeneralDictionaryVariableHeads.build_preserves : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State} {demand : Yulang.GeneralSourceState.Demand roles}
  {constructors : Yulang.GeneralDeclarationPatterns.Constructors} (declaration : Yulang.GeneralDeclarations.Declaration)
  (checked : Yulang.GeneralDeclarations.DeclarationChecked constructors roles declaration)
  (sameRole : declaration.role = demand.role) (capture : Yulang.GeneralDeclarationDemands.Capture)
  (inputs : Yulang.GeneralDictionaryVariableHeads.HeadlessInputs state demand)
  (result : Yulang.GeneralDictionaryBinderLocations.Inputs state demand),
  Yulang.GeneralDictionaryVariableHeads.build declaration checked sameRole capture inputs = some result →
    result.lower = inputs.lower ∧ result.upper = inputs.upper ∧ result.target = inputs.target
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryVariableHeads.build_preserves' depends on axioms: [propext, Quot.sound]
```

## 101. build_exact

- 分類: 完全性
- ソースモジュール: Yulang.GeneralDictionaryVariableHeads
- ソースファイル: lean/Yulang/GeneralDictionaryVariableHeads.lean
- 命題: 検査済みで要求と役割が等しい宣言について、headless inputs から build が result を返すことと、lower／upper／target の保存および result.head の HeadDenotes は同値。capture 自体の候補照合は仮定外であり検証しない。

### カーネル確認済みの型（#check @）

```lean
@Yulang.GeneralDictionaryVariableHeads.build_exact : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State} {demand : Yulang.GeneralSourceState.Demand roles}
  {constructors : Yulang.GeneralDeclarationPatterns.Constructors} (declaration : Yulang.GeneralDeclarations.Declaration)
  (checked : Yulang.GeneralDeclarations.DeclarationChecked constructors roles declaration)
  (sameRole : declaration.role = demand.role) (capture : Yulang.GeneralDeclarationDemands.Capture)
  (inputs : Yulang.GeneralDictionaryVariableHeads.HeadlessInputs state demand)
  (result : Yulang.GeneralDictionaryBinderLocations.Inputs state demand),
  Yulang.GeneralDictionaryVariableHeads.build declaration checked sameRole capture inputs = some result ↔
    result.lower = inputs.lower ∧
      result.upper = inputs.upper ∧
        result.target = inputs.target ∧
          Yulang.GeneralDictionaryVariableHeads.HeadDenotes declaration capture demand result.head
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryVariableHeads.build_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 102. denotesAt_realization

- 分類: 健全性
- ソースモジュール: Yulang.GeneralDictionaryVariableHeads
- ソースファイル: lean/Yulang/GeneralDictionaryVariableHeads.lean
- 命題: 与えた assignment と束縛子値が capture を Realizes し、ある位置の項が DenotesAt を満たすなら、その位置に変数へ正規化される実際の pattern と束縛子が存在し、束縛子値は source map で持ち上げた項の評価と同値になる。

### カーネル確認済みの型（#check @）

```lean
@Yulang.GeneralDictionaryVariableHeads.denotesAt_realization : ∀ {state : Yulang.GeneralSourceState.State}
  (declaration : Yulang.GeneralDeclarations.Declaration) (capture : Yulang.GeneralDeclarationDemands.Capture)
  (assignment : Yulang.GeneralSourceState.Assignment) (values : Nat → Yulang.Common.Ty),
  Yulang.GeneralDictionaryVariableRealization.Realizes declaration capture assignment values →
    ∀ (index : Nat) (term : Yulang.Core.PresenceGeneration.TyTerm (Fin state.slots)),
      Yulang.GeneralDictionaryVariableHeads.DenotesAt state declaration capture index term →
        ∃ pattern binder,
          declaration.head[index]? = some pattern ∧
            Yulang.GeneralDeclarationPatterns.normalize pattern = Yulang.GeneralDeclarationPatterns.Pattern.var binder ∧
              Yulang.Common.Equivalent (values binder)
                (Yulang.Core.PresenceGeneration.TyTerm.eval Yulang.Common.model assignment
                  (Yulang.GeneralDictionaryStateEquations.liftType state term))
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryVariableHeads.denotesAt_realization' depends on axioms: [propext, Quot.sound]
```

## 103. leaf_positional_compiles

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryHeadExamples
- ソースファイル: lean/Yulang/GeneralDictionaryHeadExamples.lean
- 命題: 固定例の leaf head の位置 0 は slot 0 の変数に compileAt される。

### カーネル確認済みの型（#check @）

```lean
Yulang.GeneralDictionaryHeadExamples.leaf_positional_compiles : Yulang.GeneralDictionaryVariableHeads.compileAt
    Yulang.GeneralDictionaryTerminalFixture.state Yulang.GeneralDictionaryTerminalFixture.leaf
    Yulang.GeneralDictionaryTerminalFixture.capture 0 =
  some (Yulang.Core.PresenceGeneration.TyTerm.var 0)
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryHeadExamples.leaf_positional_compiles' depends on axioms: [propext, Quot.sound]
```

## 104. leaf_head_denotes

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryHeadExamples
- ソースファイル: lean/Yulang/GeneralDictionaryHeadExamples.lean
- 命題: 固定例の childInputs.head は leaf・capture・childDemand に対する HeadDenotes を満たす。

### カーネル確認済みの型（#check @）

```lean
Yulang.GeneralDictionaryHeadExamples.leaf_head_denotes : Yulang.GeneralDictionaryVariableHeads.HeadDenotes
  Yulang.GeneralDictionaryTerminalFixture.leaf Yulang.GeneralDictionaryTerminalFixture.capture
  Yulang.GeneralDictionaryTerminalFixture.childDemand Yulang.GeneralDictionaryTerminalFixture.childInputs.head
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryHeadExamples.leaf_head_denotes' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 105. leaf_head_builds

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryHeadExamples
- ソースファイル: lean/Yulang/GeneralDictionaryHeadExamples.lean
- 命題: 固定例の検査済み leaf の headless build は childInputs を返す。

### カーネル確認済みの型（#check @）

```lean
Yulang.GeneralDictionaryHeadExamples.leaf_head_builds : Yulang.GeneralDictionaryVariableHeads.build
    Yulang.GeneralDictionaryTerminalFixture.leaf Yulang.GeneralDictionaryTerminalFixture.leaf_checked ⋯
    Yulang.GeneralDictionaryTerminalFixture.capture Yulang.GeneralDictionaryHeadExamples.childHeadless =
  some Yulang.GeneralDictionaryTerminalFixture.childInputs
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryHeadExamples.leaf_head_builds' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 106. leaf_concrete_head

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryHeadExamples
- ソースファイル: lean/Yulang/GeneralDictionaryHeadExamples.lean
- 命題: 固定例の child・leaf・capture・childInputs.head は具体的 heads 述語を満たす。

### カーネル確認済みの型（#check @）

```lean
Yulang.GeneralDictionaryHeadExamples.leaf_concrete_head : Yulang.GeneralDictionaryVariableHeads.heads
  Yulang.GeneralDictionaryTerminalFixture.registry.roles Yulang.GeneralDictionaryTerminalFixture.state
  Yulang.GeneralDictionaryTerminalFixture.child Yulang.GeneralDictionaryTerminalFixture.leaf
  Yulang.GeneralDictionaryTerminalFixture.capture Yulang.GeneralDictionaryTerminalFixture.childInputs.head
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryHeadExamples.leaf_concrete_head' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 107. nominal_root_defers

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryHeadExamples
- ソースファイル: lean/Yulang/GeneralDictionaryHeadExamples.lean
- 命題: 固定例の nominal な binderWrap 根の headless build は none を返す。

### カーネル確認済みの型（#check @）

```lean
Yulang.GeneralDictionaryHeadExamples.nominal_root_defers : Yulang.GeneralDictionaryVariableHeads.build
    Yulang.GeneralDictionaryOutputBinderExamples.binderWrap
    Yulang.GeneralDictionaryOutputBinderExamples.binderWrap_checked ⋯ Yulang.GeneralDictionaryTerminalFixture.capture
    Yulang.GeneralDictionaryHeadExamples.rootHeadless =
  none
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryHeadExamples.nominal_root_defers' depends on axioms: [propext, Quot.sound]
```

## 108. unequal_leaf_defers

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryHeadExamples
- ソースファイル: lean/Yulang/GeneralDictionaryHeadExamples.lean
- 命題: 固定例の leaf の入力両端 ID が異なる capture では headless build は none を返す。

### カーネル確認済みの型（#check @）

```lean
Yulang.GeneralDictionaryHeadExamples.unequal_leaf_defers : Yulang.GeneralDictionaryVariableHeads.build
    Yulang.GeneralDictionaryTerminalFixture.leaf Yulang.GeneralDictionaryTerminalFixture.leaf_checked ⋯
    Yulang.GeneralDictionaryHeadExamples.unequalCapture Yulang.GeneralDictionaryHeadExamples.childHeadless =
  none
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryHeadExamples.unequal_leaf_defers' depends on axioms: [propext, Quot.sound]
```

## 109. absent_source_defers

- 分類: 補助
- ソースモジュール: Yulang.GeneralDictionaryHeadExamples
- ソースファイル: lean/Yulang/GeneralDictionaryHeadExamples.lean
- 命題: 固定例の leaf の捕捉 source が state 内に存在しない capture では headless build は none を返す。

### カーネル確認済みの型（#check @）

```lean
Yulang.GeneralDictionaryHeadExamples.absent_source_defers : Yulang.GeneralDictionaryVariableHeads.build
    Yulang.GeneralDictionaryTerminalFixture.leaf Yulang.GeneralDictionaryTerminalFixture.leaf_checked ⋯
    Yulang.GeneralDictionaryHeadExamples.absentCapture Yulang.GeneralDictionaryHeadExamples.childHeadless =
  none
```

### 公理依存監査

```text
'Yulang.GeneralDictionaryHeadExamples.absent_source_defers' depends on axioms: [propext, Quot.sound]
```
