# Cycle128: public theorem inventory

98公開定理。量化子・前提を省かない正確な型を`#check @`で取得した。
一般B4 V3の12フィールドは未充填。主型性の完成定理はない。

## 1. `Yulang.GeneralDictionaryPayloadReconstruction.reconstruct_sound`
側: 補助。任意のchecked registry・frames・raw payload・root・返却treeで、再構成成功なら元のroot/payloadのReadbackと、全実宣言PlanのEvidenceがある。

```lean
Yulang.GeneralDictionaryPayloadReconstruction.reconstruct_sound : ∀ (registry : Yulang.GeneralDeclarations.Registry)
  (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (payload : Yulang.GeneralDictionaryReadback.Payload)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles)
  (tree : Yulang.GeneralSourceDictionaries.Dictionary registry.roles),
  Yulang.GeneralDictionaryPayloadReconstruction.reconstruct registry checked frames payload root = some tree →
    Yulang.GeneralSourceDictionaries.Readback root payload tree ∧
      Yulang.GeneralSourceDictionaries.Evidence
        (Yulang.GeneralDictionaryPayloadReconstruction.Rule registry checked frames) tree
```

## 2. `Yulang.GeneralDictionaryPayloadReconstruction.reconstructChildren_sound`
側: 補助。任意のraw子列・source義務列・返却tree列について、再構成成功ならroot列・消去payload列が完全一致し、各子にPlan Evidenceがある。

```lean
Yulang.GeneralDictionaryPayloadReconstruction.reconstructChildren_sound : ∀
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (payloads : List Yulang.GeneralDictionaryReadback.Payload)
  (roots : List (Yulang.GeneralSourceDictionaries.Occurrence registry.roles))
  (trees : List (Yulang.GeneralSourceDictionaries.Dictionary registry.roles)),
  Yulang.GeneralDictionaryPayloadReconstruction.reconstructChildren registry checked frames payloads roots =
      some trees →
    List.map Yulang.GeneralSourceDictionaries.Dictionary.root trees = roots ∧
      Yulang.GeneralSourceDictionaries.eraseChildren trees = payloads ∧
        ∀ (tree : Yulang.GeneralSourceDictionaries.Dictionary registry.roles),
          tree ∈ trees →
            Yulang.GeneralSourceDictionaries.Evidence
              (Yulang.GeneralDictionaryPayloadReconstruction.Rule registry checked frames) tree
```

## 3. `Yulang.GeneralDictionaryPayloadReconstruction.reconstruct_complete`
側: 補助／対応範囲の完全性。任意のsource辞書treeが全nodeで実Plan Evidenceを持つなら、その消去payloadとrootから同じtreeを再構成する。候補適用性の完全性ではない。

```lean
Yulang.GeneralDictionaryPayloadReconstruction.reconstruct_complete : ∀ (registry : Yulang.GeneralDeclarations.Registry)
  (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (tree : Yulang.GeneralSourceDictionaries.Dictionary registry.roles),
  Yulang.GeneralSourceDictionaries.Evidence (Yulang.GeneralDictionaryPayloadReconstruction.Rule registry checked frames)
      tree →
    Yulang.GeneralDictionaryPayloadReconstruction.reconstruct registry checked frames
        (Yulang.GeneralSourceDictionaries.erase tree) tree.root =
      some tree
```

## 4. `Yulang.GeneralDictionaryPayloadReconstruction.reconstructChildren_complete`
側: 補助／対応範囲の完全性。任意の全子tree列にPlan Evidenceがあれば、同じ消去payload列とroot列から同じ列が返る。

```lean
Yulang.GeneralDictionaryPayloadReconstruction.reconstructChildren_complete : ∀
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (trees : List (Yulang.GeneralSourceDictionaries.Dictionary registry.roles)),
  (∀ (tree : Yulang.GeneralSourceDictionaries.Dictionary registry.roles),
      tree ∈ trees →
        Yulang.GeneralSourceDictionaries.Evidence
          (Yulang.GeneralDictionaryPayloadReconstruction.Rule registry checked frames) tree) →
    Yulang.GeneralDictionaryPayloadReconstruction.reconstructChildren registry checked frames
        (Yulang.GeneralSourceDictionaries.eraseChildren trees)
        (List.map Yulang.GeneralSourceDictionaries.Dictionary.root trees) =
      some trees
```

## 5. `Yulang.GeneralDictionaryPayloadReconstruction.reconstruct_exact`
側: 補助／対応範囲の完全性。任意のchecked registry・frames・root・raw payload・treeについて、再構成成功と、Readbackおよび独立Plan Evidenceの連言が同値。

```lean
Yulang.GeneralDictionaryPayloadReconstruction.reconstruct_exact : ∀ (registry : Yulang.GeneralDeclarations.Registry)
  (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (payload : Yulang.GeneralDictionaryReadback.Payload)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles)
  (tree : Yulang.GeneralSourceDictionaries.Dictionary registry.roles),
  Yulang.GeneralDictionaryPayloadReconstruction.reconstruct registry checked frames payload root = some tree ↔
    Yulang.GeneralSourceDictionaries.Readback root payload tree ∧
      Yulang.GeneralSourceDictionaries.Evidence
        (Yulang.GeneralDictionaryPayloadReconstruction.Rule registry checked frames) tree
```

## 6. `Yulang.GeneralDictionaryPayloadReconstruction.reconstruct_exists_iff`
側: 補助／対応範囲の完全性。任意の固定入力で、何らかの再構成成功treeが存在することと、既存の再帰PayloadEvidence(Plan)が同値。

```lean
Yulang.GeneralDictionaryPayloadReconstruction.reconstruct_exists_iff : ∀
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (payload : Yulang.GeneralDictionaryReadback.Payload)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles),
  (∃ tree, Yulang.GeneralDictionaryPayloadReconstruction.reconstruct registry checked frames payload root = some tree) ↔
    Yulang.GeneralDictionaryReadback.PayloadEvidence
      (Yulang.GeneralDictionaryPayloadReconstruction.Rule registry checked frames) root payload
```

## 7. `Yulang.GeneralDictionaryPayloadReconstruction.reconstruct_none_iff`
側: 補助／対応範囲の完全性。任意の固定入力で、再構成noneと、PlanのPayloadEvidence不存在が同値。言語の拒否とは同一視しない。

```lean
Yulang.GeneralDictionaryPayloadReconstruction.reconstruct_none_iff : ∀ (registry : Yulang.GeneralDeclarations.Registry)
  (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (payload : Yulang.GeneralDictionaryReadback.Payload)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles),
  Yulang.GeneralDictionaryPayloadReconstruction.reconstruct registry checked frames payload root = none ↔
    ¬Yulang.GeneralDictionaryReadback.PayloadEvidence
        (Yulang.GeneralDictionaryPayloadReconstruction.Rule registry checked frames) root payload
```

## 8. `Yulang.GeneralDictionaryRecipeFidelity.localize_tree`
側: 補助。任意state・source recipe・localize成功結果で、位置を計算する前後のsource辞書が全体で一致する。

```lean
@Yulang.GeneralDictionaryRecipeFidelity.localize_tree : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralSourceState.State) (input : Yulang.GeneralDictionarySourceRecipe.Recipe roles)
  (output : Yulang.GeneralDictionaryHeadlessPreparation.Recipe roles state),
  Yulang.GeneralDictionarySourceRecipe.localize state input = some output →
    Yulang.GeneralDictionaryRecipeFidelity.headlessTree output = Yulang.GeneralDictionaryRecipeFidelity.sourceTree input
```

## 9. `Yulang.GeneralDictionaryRecipeFidelity.headless_prepare_tree`
側: 補助。任意のheadless準備成功で、返却辞書と入力recipeの全source treeが等しい。

```lean
@Yulang.GeneralDictionaryRecipeFidelity.headless_prepare_tree : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (input : Yulang.GeneralDictionaryHeadlessPreparation.Recipe registry.roles state)
  (output : Yulang.GeneralDictionaryTransactions.Prepared registry.roles state),
  Yulang.GeneralDictionaryHeadlessPreparation.prepare registry checked frames input = some output →
    output.dictionary = Yulang.GeneralDictionaryRecipeFidelity.headlessTree input
```

## 10. `Yulang.GeneralDictionaryRecipeFidelity.source_prepare_tree`
側: 補助。任意のsource準備成功で、位置/head/RHSの計算後も全source treeが等しい。

```lean
Yulang.GeneralDictionaryRecipeFidelity.source_prepare_tree : ∀ (registry : Yulang.GeneralDeclarations.Registry)
  (checked : Yulang.GeneralDeclarations.Checked registry) (state : Yulang.GeneralSourceState.State)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (input : Yulang.GeneralDictionarySourceRecipe.Recipe registry.roles)
  (output : Yulang.GeneralDictionaryTransactions.Prepared registry.roles state),
  Yulang.GeneralDictionarySourceRecipe.prepare registry checked state frames input = some output →
    output.dictionary = Yulang.GeneralDictionaryRecipeFidelity.sourceTree input
```

## 11. `Yulang.GeneralDictionaryRecipeFidelity.recipe_tree`
側: 補助。任意source辞書をrecipeへ移してtreeへ戻すと元の辞書に等しい。

```lean
@Yulang.GeneralDictionaryRecipeFidelity.recipe_tree : ∀ {roles : Yulang.Roles.RoleDecls}
  (tree : Yulang.GeneralSourceDictionaries.Dictionary roles),
  Yulang.GeneralDictionaryRecipeFidelity.sourceTree (Yulang.GeneralDictionaryRecipeFidelity.recipe tree) = tree
```

## 12. `Yulang.GeneralDictionaryRecipeFidelity.recipe_root`
側: 補助。任意source辞書をrecipeへ移してもroot occurrenceが等しい。

```lean
@Yulang.GeneralDictionaryRecipeFidelity.recipe_root : ∀ {roles : Yulang.Roles.RoleDecls}
  (tree : Yulang.GeneralSourceDictionaries.Dictionary roles),
  (Yulang.GeneralDictionaryRecipeFidelity.recipe tree).root = tree.root
```

## 13. `Yulang.GeneralDictionaryRecipeFidelity.prepare_recipe_tree`
側: 補助。任意source辞書由来recipeの準備が成功すれば、返却辞書はその入力辞書と等しい。

```lean
Yulang.GeneralDictionaryRecipeFidelity.prepare_recipe_tree : ∀ (registry : Yulang.GeneralDeclarations.Registry)
  (checked : Yulang.GeneralDeclarations.Checked registry) (state : Yulang.GeneralSourceState.State)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (input : Yulang.GeneralSourceDictionaries.Dictionary registry.roles)
  (output : Yulang.GeneralDictionaryTransactions.Prepared registry.roles state),
  Yulang.GeneralDictionarySourceRecipe.prepare registry checked state frames
        (Yulang.GeneralDictionaryRecipeFidelity.recipe input) =
      some output →
    output.dictionary = input
```

## 14. `Yulang.GeneralDictionaryPayloadPreparation.prepare_exact`
側: 補助／対応範囲の完全性。任意のraw準備入力と返却treeについて、成功は、source再構成成功とそのrecipeの準備成功を満たすsource treeの存在に分解される。

```lean
Yulang.GeneralDictionaryPayloadPreparation.prepare_exact : ∀ (registry : Yulang.GeneralDeclarations.Registry)
  (checked : Yulang.GeneralDeclarations.Checked registry) (state : Yulang.GeneralSourceState.State)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (payload : Yulang.GeneralDictionaryReadback.Payload)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles)
  (tree : Yulang.GeneralDictionaryTransactions.Prepared registry.roles state),
  Yulang.GeneralDictionaryPayloadPreparation.prepare registry checked state frames payload root = some tree ↔
    ∃ source,
      Yulang.GeneralDictionaryPayloadReconstruction.reconstruct registry checked frames payload root = some source ∧
        Yulang.GeneralDictionarySourceRecipe.prepare registry checked state frames
            (Yulang.GeneralDictionaryRecipeFidelity.recipe source) =
          some tree
```

## 15. `Yulang.GeneralDictionaryPayloadPreparation.prepare_readback`
側: 補助。任意のraw準備成功で、返却辞書は元のrootとraw payloadをReadbackする。

```lean
Yulang.GeneralDictionaryPayloadPreparation.prepare_readback : ∀ (registry : Yulang.GeneralDeclarations.Registry)
  (checked : Yulang.GeneralDeclarations.Checked registry) (state : Yulang.GeneralSourceState.State)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (payload : Yulang.GeneralDictionaryReadback.Payload)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles)
  (tree : Yulang.GeneralDictionaryTransactions.Prepared registry.roles state),
  Yulang.GeneralDictionaryPayloadPreparation.prepare registry checked state frames payload root = some tree →
    Yulang.GeneralSourceDictionaries.Readback root payload tree.dictionary
```

## 16. `Yulang.GeneralDictionaryPayloadPreparation.prepare_uniform_source`
側: 健全性。任意の準備成功について、一つの固定source witnessが元raw payloadをReadbackし、記録batchの全modelで独立Instance Evidenceを持つ。Common版と任意nominal版はそれぞれ型のModelsを参照。

```lean
Yulang.GeneralDictionaryPayloadPreparation.prepare_uniform_source : ∀ (registry : Yulang.GeneralDeclarations.Registry)
  (checked : Yulang.GeneralDeclarations.Checked registry) (state : Yulang.GeneralSourceState.State)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (payload : Yulang.GeneralDictionaryReadback.Payload)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles)
  (tree : Yulang.GeneralDictionaryTransactions.Prepared registry.roles state),
  Yulang.GeneralDictionaryPayloadPreparation.prepare registry checked state frames payload root = some tree →
    ∃ witness,
      Yulang.GeneralSourceDictionaries.Readback root payload witness ∧
        ∀ (assignment : Yulang.GeneralSourceState.Assignment),
          Yulang.GeneralSourceState.Models (Yulang.GeneralDictionaryBatchRecording.record tree.items) assignment →
            Yulang.GeneralSourceDictionaries.Evidence
              (Yulang.GeneralDictionaryHeadlessSourceEvidence.Instance registry checked frames assignment) witness
```

## 17. `Yulang.GeneralDictionaryPayloadPreparation.prepare_payload_evidence`
側: 健全性。任意の準備成功と記録状態のmodelについて、元のraw payload自体に独立InstanceのPayloadEvidenceがある。

```lean
Yulang.GeneralDictionaryPayloadPreparation.prepare_payload_evidence : ∀ (registry : Yulang.GeneralDeclarations.Registry)
  (checked : Yulang.GeneralDeclarations.Checked registry) (state : Yulang.GeneralSourceState.State)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (payload : Yulang.GeneralDictionaryReadback.Payload)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles)
  (tree : Yulang.GeneralDictionaryTransactions.Prepared registry.roles state),
  Yulang.GeneralDictionaryPayloadPreparation.prepare registry checked state frames payload root = some tree →
    ∀ (assignment : Yulang.GeneralSourceState.Assignment),
      Yulang.GeneralSourceState.Models (Yulang.GeneralDictionaryBatchRecording.record tree.items) assignment →
        Yulang.GeneralDictionaryReadback.PayloadEvidence
          (Yulang.GeneralDictionaryHeadlessSourceEvidence.Instance registry checked frames assignment) root payload
```

## 18. `Yulang.GeneralDictionaryPayloadReconstructionOrder.evidence_reorders`
側: 健全性。任意の許されたregistry Reorders・固定frames・source treeについて、実Plan Evidenceが前後で同値。

```lean
Yulang.GeneralDictionaryPayloadReconstructionOrder.evidence_reorders : ∀
  (constructors : Yulang.GeneralDeclarationPatterns.Constructors) (roles : Yulang.Roles.RoleDecls)
  (first last : List Yulang.GeneralDeclarations.Declaration)
  (one : Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := first })
  (two : Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := last }),
  Yulang.GeneralRegistryReordering.Reorders { constructors := constructors, roles := roles, declarations := first }
      { constructors := constructors, roles := roles, declarations := last } →
    ∀ (frames : Yulang.GeneralDictionaryTransactions.Frames roles)
      (tree : Yulang.GeneralSourceDictionaries.Dictionary roles),
      Yulang.GeneralSourceDictionaries.Evidence
          (Yulang.GeneralDictionaryPayloadReconstruction.Rule
            { constructors := constructors, roles := roles, declarations := first } one frames)
          tree ↔
        Yulang.GeneralSourceDictionaries.Evidence
          (Yulang.GeneralDictionaryPayloadReconstruction.Rule
            { constructors := constructors, roles := roles, declarations := last } two frames)
          tree
```

## 19. `Yulang.GeneralDictionaryPayloadReconstructionOrder.reconstruct_reorders`
側: 補助。任意のregistry Reordersと固定root/raw payload/framesについて、再構成のOption全体が等しい。

```lean
Yulang.GeneralDictionaryPayloadReconstructionOrder.reconstruct_reorders : ∀
  (constructors : Yulang.GeneralDeclarationPatterns.Constructors) (roles : Yulang.Roles.RoleDecls)
  (first last : List Yulang.GeneralDeclarations.Declaration)
  (one : Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := first })
  (two : Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := last }),
  Yulang.GeneralRegistryReordering.Reorders { constructors := constructors, roles := roles, declarations := first }
      { constructors := constructors, roles := roles, declarations := last } →
    ∀ (frames : Yulang.GeneralDictionaryTransactions.Frames roles) (payload : Yulang.GeneralDictionaryReadback.Payload)
      (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
      Yulang.GeneralDictionaryPayloadReconstruction.reconstruct
          { constructors := constructors, roles := roles, declarations := first } one frames payload root =
        Yulang.GeneralDictionaryPayloadReconstruction.reconstruct
          { constructors := constructors, roles := roles, declarations := last } two frames payload root
```

## 20. `Yulang.GeneralDictionaryPayloadReconstructionOrder.prepare_reorders`
側: 補助。任意のregistry Reordersと固定state/root/raw payload/framesについて、準備のOption全体が等しい。

```lean
Yulang.GeneralDictionaryPayloadReconstructionOrder.prepare_reorders : ∀
  (constructors : Yulang.GeneralDeclarationPatterns.Constructors) (roles : Yulang.Roles.RoleDecls)
  (first last : List Yulang.GeneralDeclarations.Declaration)
  (one : Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := first })
  (two : Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := last }),
  Yulang.GeneralRegistryReordering.Reorders { constructors := constructors, roles := roles, declarations := first }
      { constructors := constructors, roles := roles, declarations := last } →
    ∀ (state : Yulang.GeneralSourceState.State) (frames : Yulang.GeneralDictionaryTransactions.Frames roles)
      (payload : Yulang.GeneralDictionaryReadback.Payload) (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
      Yulang.GeneralDictionaryPayloadPreparation.prepare
          { constructors := constructors, roles := roles, declarations := first } one state frames payload root =
        Yulang.GeneralDictionaryPayloadPreparation.prepare
          { constructors := constructors, roles := roles, declarations := last } two state frames payload root
```

## 21. `Yulang.GeneralDictionaryPayloadReconstructionExamples.leaf_reconstructed`
側: 補助。実fixtureの終端raw keyから、その正確なsource occurrenceと空の子列を再構成する。

```lean
Yulang.GeneralDictionaryPayloadReconstructionExamples.leaf_reconstructed : Yulang.GeneralDictionaryPayloadReconstruction.reconstruct
    Yulang.GeneralDictionaryHeadlessFixture.registry Yulang.GeneralDictionaryHeadlessFixture.registry_checked
    (fun x => Yulang.GeneralDictionaryHeadlessFixture.frame) (Yulang.CommonRoleOutermostResolver.Dictionary.node 3 [])
    Yulang.GeneralDictionaryHeadlessFixture.child =
  some (Yulang.GeneralSourceDictionaries.Dictionary.node Yulang.GeneralDictionaryHeadlessFixture.child 3 [])
```

## 22. `Yulang.GeneralDictionaryPayloadReconstructionExamples.tree_reconstructed`
側: 補助。実fixtureのraw二node key木から、全source occurrenceを保持した正確な辞書treeが返る。計算frames版でも外部child recipeは不要。

```lean
Yulang.GeneralDictionaryPayloadReconstructionExamples.tree_reconstructed : Yulang.GeneralDictionaryPayloadReconstruction.reconstruct
    Yulang.GeneralDictionaryHeadlessFixture.registry Yulang.GeneralDictionaryHeadlessFixture.registry_checked
    (fun x => Yulang.GeneralDictionaryHeadlessFixture.frame)
    Yulang.GeneralDictionaryPayloadReconstructionExamples.payload Yulang.GeneralDictionaryHeadlessFixture.root =
  some Yulang.GeneralDictionaryPayloadReconstructionExamples.sourceTree
```

## 23. `Yulang.GeneralDictionaryPayloadReconstructionExamples.omitted_child_defers`
側: 補助。実fixtureで必要なraw子を落とすと再構成noneになる。未完成の辞書を成功にしない。

```lean
Yulang.GeneralDictionaryPayloadReconstructionExamples.omitted_child_defers : Yulang.GeneralDictionaryPayloadReconstruction.reconstruct
    Yulang.GeneralDictionaryHeadlessFixture.registry Yulang.GeneralDictionaryHeadlessFixture.registry_checked
    (fun x => Yulang.GeneralDictionaryHeadlessFixture.frame) (Yulang.CommonRoleOutermostResolver.Dictionary.node 2 [])
    Yulang.GeneralDictionaryHeadlessFixture.root =
  none
```

## 24. `Yulang.GeneralDictionaryPayloadReconstructionExamples.extra_child_defers`
側: 補助。実fixtureで余分なraw子を一つ追加すると再構成noneになる。重複を捨てて成功しない。

```lean
Yulang.GeneralDictionaryPayloadReconstructionExamples.extra_child_defers : Yulang.GeneralDictionaryPayloadReconstruction.reconstruct
    Yulang.GeneralDictionaryHeadlessFixture.registry Yulang.GeneralDictionaryHeadlessFixture.registry_checked
    (fun x => Yulang.GeneralDictionaryHeadlessFixture.frame)
    (Yulang.CommonRoleOutermostResolver.Dictionary.node 2
      [Yulang.CommonRoleOutermostResolver.Dictionary.node 3 [],
        Yulang.CommonRoleOutermostResolver.Dictionary.node 3 []])
    Yulang.GeneralDictionaryHeadlessFixture.root =
  none
```

## 25. `Yulang.GeneralDictionaryPayloadReconstructionExamples.wrong_role_key_defers`
側: 補助。実fixtureで別roleのvisible keyをrootに使うと再構成noneになる。

```lean
Yulang.GeneralDictionaryPayloadReconstructionExamples.wrong_role_key_defers : Yulang.GeneralDictionaryPayloadReconstruction.reconstruct
    Yulang.GeneralDictionaryHeadlessFixture.registry Yulang.GeneralDictionaryHeadlessFixture.registry_checked
    (fun x => Yulang.GeneralDictionaryHeadlessFixture.frame) (Yulang.CommonRoleOutermostResolver.Dictionary.node 3 [])
    Yulang.GeneralDictionaryHeadlessFixture.root =
  none
```

## 26. `Yulang.GeneralDictionaryPayloadReconstructionExamples.absent_key_defers`
側: 補助。実fixtureで存在しないkey99をrootに使うと再構成noneになる。

```lean
Yulang.GeneralDictionaryPayloadReconstructionExamples.absent_key_defers : Yulang.GeneralDictionaryPayloadReconstruction.reconstruct
    Yulang.GeneralDictionaryHeadlessFixture.registry Yulang.GeneralDictionaryHeadlessFixture.registry_checked
    (fun x => Yulang.GeneralDictionaryHeadlessFixture.frame) (Yulang.CommonRoleOutermostResolver.Dictionary.node 99 [])
    Yulang.GeneralDictionaryHeadlessFixture.root =
  none
```

## 27. `Yulang.GeneralDictionaryPayloadReconstructionExamples.source_identities_preserved`
側: 補助。実fixtureの再構成はsource identity9と20を保持し、列位置をsource identityにしない。

```lean
Yulang.GeneralDictionaryPayloadReconstructionExamples.source_identities_preserved : ∃ reconstructed,
  Yulang.GeneralDictionaryPayloadReconstruction.reconstruct Yulang.GeneralDictionaryHeadlessFixture.registry
        Yulang.GeneralDictionaryHeadlessFixture.registry_checked
        (fun x => Yulang.GeneralDictionaryHeadlessFixture.frame)
        Yulang.GeneralDictionaryPayloadReconstructionExamples.payload Yulang.GeneralDictionaryHeadlessFixture.root =
      some reconstructed ∧
    List.map (fun event => event.fst.identity) (Yulang.GeneralSourceDictionaries.observations reconstructed) = [9, 20]
```

## 28. `Yulang.GeneralDictionaryPayloadReconstructionExamples.source_readback`
側: 補助。実fixtureの返却source辞書が元root/raw payloadをReadbackする。Plan Evidence併記版は完全Planも述べる。

```lean
Yulang.GeneralDictionaryPayloadReconstructionExamples.source_readback : Yulang.GeneralSourceDictionaries.Readback
    Yulang.GeneralDictionaryHeadlessFixture.root Yulang.GeneralDictionaryPayloadReconstructionExamples.payload
    Yulang.GeneralDictionaryPayloadReconstructionExamples.sourceTree ∧
  Yulang.GeneralSourceDictionaries.Evidence
    (Yulang.GeneralDictionaryPayloadReconstruction.Rule Yulang.GeneralDictionaryHeadlessFixture.registry
      Yulang.GeneralDictionaryHeadlessFixture.registry_checked fun x => Yulang.GeneralDictionaryHeadlessFixture.frame)
    Yulang.GeneralDictionaryPayloadReconstructionExamples.sourceTree
```

## 29. `Yulang.GeneralDictionaryPayloadPreparationExamples.raw_tree_prepared`
側: 補助。実producer fixtureのraw key木だけから、既存の全Located packageを持つPrepared木が返る。

```lean
Yulang.GeneralDictionaryPayloadPreparationExamples.raw_tree_prepared : Yulang.GeneralDictionaryPayloadPreparation.prepare
    Yulang.GeneralDictionaryHeadlessFixture.registry Yulang.GeneralDictionaryHeadlessFixture.registry_checked
    Yulang.GeneralDictionaryHeadlessFixture.state (fun x => Yulang.GeneralDictionaryHeadlessFixture.frame)
    Yulang.GeneralDictionaryPayloadReconstructionExamples.payload Yulang.GeneralDictionaryHeadlessFixture.root =
  some Yulang.GeneralDictionaryHeadlessFixture.tree
```

## 30. `Yulang.GeneralDictionaryPayloadPreparationExamples.raw_uniform_source`
側: 健全性。実fixtureのraw payloadに一つのReadback witnessがあり、全joint Common modelで独立source Evidenceを持つ。

```lean
Yulang.GeneralDictionaryPayloadPreparationExamples.raw_uniform_source : ∃ witness,
  Yulang.GeneralSourceDictionaries.Readback Yulang.GeneralDictionaryHeadlessFixture.root
      Yulang.GeneralDictionaryPayloadReconstructionExamples.payload witness ∧
    ∀ (model : Yulang.GeneralSourceState.Assignment),
      Yulang.GeneralSourceState.Models
          (Yulang.GeneralDictionaryBatchRecording.record Yulang.GeneralDictionaryHeadlessFixture.tree.items) model →
        Yulang.GeneralSourceDictionaries.Evidence
          (Yulang.GeneralDictionaryHeadlessSourceEvidence.Instance Yulang.GeneralDictionaryHeadlessFixture.registry
            Yulang.GeneralDictionaryHeadlessFixture.registry_checked
            (fun x => Yulang.GeneralDictionaryHeadlessFixture.frame) model)
          witness
```

## 31. `Yulang.GeneralDictionaryPayloadPreparationExamples.raw_source_nonvacuous`
側: 補助。実fixtureで準備成功・明示的Common joint model・同modelの独立source Evidenceが同時に成立する。

```lean
Yulang.GeneralDictionaryPayloadPreparationExamples.raw_source_nonvacuous : Yulang.GeneralDictionaryPayloadPreparation.prepare
      Yulang.GeneralDictionaryHeadlessFixture.registry Yulang.GeneralDictionaryHeadlessFixture.registry_checked
      Yulang.GeneralDictionaryHeadlessFixture.state (fun x => Yulang.GeneralDictionaryHeadlessFixture.frame)
      Yulang.GeneralDictionaryPayloadReconstructionExamples.payload Yulang.GeneralDictionaryHeadlessFixture.root =
    some Yulang.GeneralDictionaryHeadlessFixture.tree ∧
  Yulang.GeneralSourceState.Models
      (Yulang.GeneralDictionaryBatchRecording.record Yulang.GeneralDictionaryHeadlessFixture.tree.items)
      Yulang.GeneralDictionaryHeadlessFixture.assignment ∧
    ∃ witness,
      Yulang.GeneralSourceDictionaries.Readback Yulang.GeneralDictionaryHeadlessFixture.root
          Yulang.GeneralDictionaryPayloadReconstructionExamples.payload witness ∧
        Yulang.GeneralSourceDictionaries.Evidence
          (Yulang.GeneralDictionaryHeadlessSourceEvidence.Instance Yulang.GeneralDictionaryHeadlessFixture.registry
            Yulang.GeneralDictionaryHeadlessFixture.registry_checked
            (fun x => Yulang.GeneralDictionaryHeadlessFixture.frame) Yulang.GeneralDictionaryHeadlessFixture.assignment)
          witness
```

## 32. `Yulang.GeneralDictionaryPayloadPreparationExamples.raw_payload_evidence`
側: 健全性。実fixtureの元raw payloadに、明示的Common assignmentで独立source PayloadEvidenceがある。

```lean
Yulang.GeneralDictionaryPayloadPreparationExamples.raw_payload_evidence : Yulang.GeneralDictionaryReadback.PayloadEvidence
  (Yulang.GeneralDictionaryHeadlessSourceEvidence.Instance Yulang.GeneralDictionaryHeadlessFixture.registry
    Yulang.GeneralDictionaryHeadlessFixture.registry_checked (fun x => Yulang.GeneralDictionaryHeadlessFixture.frame)
    Yulang.GeneralDictionaryHeadlessFixture.assignment)
  Yulang.GeneralDictionaryHeadlessFixture.root Yulang.GeneralDictionaryPayloadReconstructionExamples.payload
```

## 33. `Yulang.GeneralDictionaryPayloadPreparationExamples.raw_preparation_with_pending`
側: 補助。実fixtureでraw準備成功とRootPendingが同時に成立する。準備は候補解決ではない。

```lean
Yulang.GeneralDictionaryPayloadPreparationExamples.raw_preparation_with_pending : Yulang.GeneralDictionaryPayloadPreparation.prepare
      Yulang.GeneralDictionaryHeadlessFixture.registry Yulang.GeneralDictionaryHeadlessFixture.registry_checked
      Yulang.GeneralDictionaryHeadlessFixture.state (fun x => Yulang.GeneralDictionaryHeadlessFixture.frame)
      Yulang.GeneralDictionaryPayloadReconstructionExamples.payload Yulang.GeneralDictionaryHeadlessFixture.root =
    some Yulang.GeneralDictionaryHeadlessFixture.tree ∧
  Yulang.GeneralSourceState.RootPending Yulang.GeneralDictionaryHeadlessFixture.state
    Yulang.GeneralDictionaryHeadlessFixture.rootDemand Yulang.GeneralDictionaryHeadlessPendingBoundary.allInputs
```

## 34. `Yulang.GeneralDictionaryPayloadPreparationExamples.absent_output_preparation_defers`
側: 補助。実fixtureのoutput source slotが存在しないと、rawからの準備はnoneになる。新slotを勝手に割り当てない。

```lean
Yulang.GeneralDictionaryPayloadPreparationExamples.absent_output_preparation_defers : Yulang.GeneralDictionaryPayloadPreparation.prepare
    Yulang.GeneralDictionaryHeadlessFixture.registry Yulang.GeneralDictionaryHeadlessFixture.registry_checked
    Yulang.GeneralDictionaryHeadlessFixture.state (fun x => Yulang.GeneralDictionaryHeadlessFixture.frame)
    Yulang.GeneralDictionaryPayloadReconstructionExamples.payload
    Yulang.GeneralDictionarySourceRecipeExamples.absentOutputRoot =
  none
```

## 35. `Yulang.GeneralDictionaryNominalEquations.liftType_eval`
側: 補助。任意state・局所型term・任意full nominal assignmentで、sourceへの型term持上げ評価と局所assignment評価が等しい。

```lean
Yulang.GeneralDictionaryNominalEquations.liftType_eval : ∀ (state : Yulang.GeneralSourceState.State)
  (term : Yulang.Core.PresenceGeneration.TyTerm (Fin state.slots))
  (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.Core.PresenceGeneration.TyTerm.eval Yulang.CommonNominalFullCarrier.model assignment
      (Yulang.GeneralDictionaryStateEquations.liftType state term) =
    Yulang.Core.PresenceGeneration.TyTerm.eval Yulang.CommonNominalFullCarrier.model
      (Yulang.GeneralNominalCommonBridge.assignment state assignment) term
```

## 36. `Yulang.GeneralDictionaryNominalEquations.liftRow_eval`
側: 補助。任意state・局所row term・任意full nominal assignmentで、row source持上げ評価と局所assignment評価が等しい。型mapとrow mapを同一視しない。

```lean
Yulang.GeneralDictionaryNominalEquations.liftRow_eval : ∀ (state : Yulang.GeneralSourceState.State)
  (term : Yulang.Core.PresenceGeneration.RowTerm (Fin state.slots))
  (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.Core.PresenceGeneration.RowTerm.eval Yulang.CommonNominalFullCarrier.model assignment
      (Yulang.GeneralDictionaryStateEquations.liftRow state term) =
    Yulang.Core.PresenceGeneration.RowTerm.eval Yulang.CommonNominalFullCarrier.model
      (Yulang.GeneralNominalCommonBridge.assignment state assignment) term
```

## 37. `Yulang.GeneralDictionaryNominalEquations.recorded_holds`
側: 健全性。任意Located・実Recorded証拠・full nominal state modelについて、全head区間と繰返しoutput等式が成立する。

```lean
@Yulang.GeneralDictionaryNominalEquations.recorded_holds : ∀ {state : Yulang.GeneralSourceState.State}
  {roles : Yulang.Roles.RoleDecls} {demand : Yulang.GeneralSourceState.Demand roles}
  (located : Yulang.GeneralDictionaryStateEquations.Located state demand),
  Yulang.GeneralDictionaryStateEquations.Recorded located →
    ∀ (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.GeneralNominalCommonBridge.Models state assignment →
        Yulang.GeneralDictionaryNominalEquations.Holds located.equations assignment
```

## 38. `Yulang.GeneralDictionaryNominalEquations.append_models`
側: 健全性。任意state・追加atom列・full nominal assignmentについて、追加状態Modelsと元Modelsかつ追加全atomが同値。head/interval義務も保持する。

```lean
Yulang.GeneralDictionaryNominalEquations.append_models : ∀ (state : Yulang.GeneralSourceState.State)
  (atoms : List (Yulang.PresenceNormalForm.Atom (Fin state.slots)))
  (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalCommonBridge.Models (Yulang.GeneralDictionaryEquationRecording.append state atoms) assignment ↔
    Yulang.GeneralNominalCommonBridge.Models state assignment ∧
      Yulang.PresenceNormalForm.All Yulang.CommonNominalFullCarrier.model
        (Yulang.GeneralNominalCommonBridge.assignment state assignment) atoms
```

## 39. `Yulang.GeneralDictionaryNominalEquations.atoms_exact`
側: 補助／対応範囲の完全性。任意Located・full nominal assignmentについて、生成された全atomの成立と独立Holdsが同値。

```lean
@Yulang.GeneralDictionaryNominalEquations.atoms_exact : ∀ {state : Yulang.GeneralSourceState.State}
  {roles : Yulang.Roles.RoleDecls} {demand : Yulang.GeneralSourceState.Demand roles}
  (located : Yulang.GeneralDictionaryStateEquations.Located state demand)
  (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.PresenceNormalForm.All Yulang.CommonNominalFullCarrier.model
      (Yulang.GeneralNominalCommonBridge.assignment state assignment)
      (Yulang.GeneralDictionaryEquationRecording.atoms located) ↔
    Yulang.GeneralDictionaryNominalEquations.Holds located.equations assignment
```

## 40. `Yulang.GeneralDictionaryNominalEquations.batch_models`
側: 健全性。任意有限package列・full nominal assignmentについて、全batch記録のModelsと元Modelsかつ全package Holdsが同値。

```lean
@Yulang.GeneralDictionaryNominalEquations.batch_models : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State} (items : List (Yulang.GeneralDictionaryBatchRecording.Item roles state))
  (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalCommonBridge.Models (Yulang.GeneralDictionaryBatchRecording.record items) assignment ↔
    Yulang.GeneralNominalCommonBridge.Models state assignment ∧
      ∀ (item : Yulang.GeneralDictionaryBatchRecording.Item roles state),
        item ∈ items → Yulang.GeneralDictionaryNominalEquations.Holds item.located.equations assignment
```

## 41. `Yulang.GeneralDictionaryNominalEquations.batch_member_holds`
側: 健全性。任意batch memberとその全記録状態のfull nominal modelについて、そのmemberのsource等式が成立する。

```lean
@Yulang.GeneralDictionaryNominalEquations.batch_member_holds : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State} (items : List (Yulang.GeneralDictionaryBatchRecording.Item roles state))
  (item : Yulang.GeneralDictionaryBatchRecording.Item roles state),
  item ∈ items →
    ∀ (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.GeneralNominalCommonBridge.Models (Yulang.GeneralDictionaryBatchRecording.record items) assignment →
        Yulang.GeneralDictionaryNominalEquations.Holds item.located.equations assignment
```

## 42. `Yulang.GeneralDictionaryNominalExamples.base_model`
側: 補助。明示的な定数nominal73 assignmentがfixtureの元source状態を満たす。

```lean
Yulang.GeneralDictionaryNominalExamples.base_model : Yulang.GeneralNominalCommonBridge.Models
  Yulang.GeneralDictionaryHeadlessFixture.state Yulang.GeneralDictionaryNominalExamples.nominalAssignment
```

## 43. `Yulang.GeneralDictionaryNominalExamples.root_holds`
側: 健全性。同nominal assignmentが実fixture根の全head/output等式を満たす。

```lean
Yulang.GeneralDictionaryNominalExamples.root_holds : Yulang.GeneralDictionaryNominalEquations.Holds
  Yulang.GeneralDictionaryHeadlessFixture.rootLocated.equations
  Yulang.GeneralDictionaryNominalExamples.nominalAssignment
```

## 44. `Yulang.GeneralDictionaryNominalExamples.child_holds`
側: 健全性。同nominal assignmentが実fixture子の全head/output等式を満たす。

```lean
Yulang.GeneralDictionaryNominalExamples.child_holds : Yulang.GeneralDictionaryNominalEquations.Holds
  Yulang.GeneralDictionaryHeadlessFixture.childLocated.equations
  Yulang.GeneralDictionaryNominalExamples.nominalAssignment
```

## 45. `Yulang.GeneralDictionaryNominalExamples.joint_model`
側: 補助。同nominal assignmentが実fixture根と子の同時記録batchを満たす。

```lean
Yulang.GeneralDictionaryNominalExamples.joint_model : Yulang.GeneralNominalCommonBridge.Models
  (Yulang.GeneralDictionaryBatchRecording.record
    [Yulang.GeneralDictionaryHeadlessFixture.rootItem, Yulang.GeneralDictionaryHeadlessFixture.childItem])
  Yulang.GeneralDictionaryNominalExamples.nominalAssignment
```

## 46. `Yulang.GeneralDictionaryNominalExamples.tree_joint_model`
側: 補助。同nominal assignmentが実fixtureの全Prepared木の記録batchを満たす。

```lean
Yulang.GeneralDictionaryNominalExamples.tree_joint_model : Yulang.GeneralNominalCommonBridge.Models
  (Yulang.GeneralDictionaryBatchRecording.record Yulang.GeneralDictionaryHeadlessFixture.tree.items)
  Yulang.GeneralDictionaryNominalExamples.nominalAssignment
```

## 47. `Yulang.GeneralDictionaryNominalExamples.nominal_not_embedded_int`
側: 補助。展示したnominal73値は既存Common Intのfull carrierへの埋込みと等しくない。全Common像の外であるという主張ではない。

```lean
Yulang.GeneralDictionaryNominalExamples.nominal_not_embedded_int : Yulang.GeneralDictionaryNominalExamples.nominalValue ≠
  Yulang.CommonNominalFullModelMap.value (Yulang.CommonSyntax.Layer.base Yulang.Inference.Base.int)
```

## 48. `Yulang.GeneralDictionaryNominalRecording.liftAtom_exact`
側: 補助／対応範囲の完全性。任意局所atomと任意nominal assignmentについて、型/row別source mapで持ち上げたatomの成立と局所atomの成立が同値。

```lean
Yulang.GeneralDictionaryNominalRecording.liftAtom_exact : ∀ (state : Yulang.GeneralSourceState.State)
  (atom : Yulang.PresenceNormalForm.Atom (Fin state.slots)) (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.PresenceNormalForm.Atom.Holds Yulang.CommonNominalFullCarrier.model model
      (Yulang.GeneralDictionaryNominalRecording.liftAtom state atom) ↔
    Yulang.PresenceNormalForm.Atom.Holds Yulang.CommonNominalFullCarrier.model
      (Yulang.GeneralNominalCommonBridge.assignment state model) atom
```

## 49. `Yulang.GeneralDictionaryNominalRecording.liftAtoms_exact`
側: 補助／対応範囲の完全性。任意局所atom列について、上記同値が全列の連言に成立する。

```lean
Yulang.GeneralDictionaryNominalRecording.liftAtoms_exact : ∀ (state : Yulang.GeneralSourceState.State)
  (atoms : List (Yulang.PresenceNormalForm.Atom (Fin state.slots)))
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.PresenceNormalForm.All Yulang.CommonNominalFullCarrier.model model
      (List.map (Yulang.GeneralDictionaryNominalRecording.liftAtom state) atoms) ↔
    Yulang.PresenceNormalForm.All Yulang.CommonNominalFullCarrier.model
      (Yulang.GeneralNominalCommonBridge.assignment state model) atoms
```

## 50. `Yulang.GeneralDictionaryNominalRecording.record_models`
側: 健全性。任意full nominal state・局所dictionary package列・assignmentで、dictionary記録Modelsと元full Modelsかつ全package Holdsが同値。

```lean
@Yulang.GeneralDictionaryNominalRecording.record_models : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalState.State)
  (items : List (Yulang.GeneralDictionaryBatchRecording.Item roles state.base))
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models (Yulang.GeneralDictionaryNominalRecording.record state items) model ↔
    Yulang.GeneralNominalState.Models state model ∧
      ∀ (item : Yulang.GeneralDictionaryBatchRecording.Item roles state.base),
        item ∈ items → Yulang.GeneralDictionaryNominalEquations.Holds item.located.equations model
```

## 51. `Yulang.GeneralDictionaryNominalRecording.recorded_base_model`
側: 補助。任意full-state dictionary記録のmodelは、同じbase-slot batchのnominal Modelsでもある。

```lean
@Yulang.GeneralDictionaryNominalRecording.recorded_base_model : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalState.State)
  (items : List (Yulang.GeneralDictionaryBatchRecording.Item roles state.base))
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models (Yulang.GeneralDictionaryNominalRecording.record state items) model →
    Yulang.GeneralNominalCommonBridge.Models (Yulang.GeneralDictionaryBatchRecording.record items) model
```

## 52. `Yulang.GeneralDictionaryNominalRecording.record_preserves`
側: 健全性。任意full-state dictionary記録のmodelは元full-stateのmodelでもある。modelの存在や逆向き延長は結論しない。

```lean
@Yulang.GeneralDictionaryNominalRecording.record_preserves : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalState.State)
  (items : List (Yulang.GeneralDictionaryBatchRecording.Item roles state.base))
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models (Yulang.GeneralDictionaryNominalRecording.record state items) model →
    Yulang.GeneralNominalState.Models state model
```

## 53. `Yulang.GeneralDictionaryNominalRecording.record_pending`
側: 補助。任意full-state dictionary記録の前後で任意需要のRootPendingは同値。

```lean
@Yulang.GeneralDictionaryNominalRecording.record_pending : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalState.State)
  (items : List (Yulang.GeneralDictionaryBatchRecording.Item roles state.base))
  (demand : Yulang.GeneralSourceState.Demand roles),
  Yulang.GeneralNominalState.RootPending (Yulang.GeneralDictionaryNominalRecording.record state items) demand ↔
    Yulang.GeneralNominalState.RootPending state demand
```

## 54. `Yulang.GeneralDictionaryNominalRecording.record_order_models`
側: 健全性。任意package列のPermutationについて、全full-state model集合が同じ。

```lean
@Yulang.GeneralDictionaryNominalRecording.record_order_models : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalState.State)
  (first last : List (Yulang.GeneralDictionaryBatchRecording.Item roles state.base)),
  first.Perm last →
    ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.GeneralNominalState.Models (Yulang.GeneralDictionaryNominalRecording.record state first) model ↔
        Yulang.GeneralNominalState.Models (Yulang.GeneralDictionaryNominalRecording.record state last) model
```

## 55. `Yulang.GeneralDictionaryNominalSourceEvidence.realizes`
側: 健全性。任意checked宣言・HeadDenotes・captureと任意nominal assignmentについて、構成valuesが捕捉区間とoutput sourceを実現する。

```lean
@Yulang.GeneralDictionaryNominalSourceEvidence.realizes : ∀ {state : Yulang.GeneralSourceState.State}
  {constructors : Yulang.GeneralDeclarationPatterns.Constructors} {roles : Yulang.Roles.RoleDecls}
  (declaration : Yulang.GeneralDeclarations.Declaration),
  Yulang.GeneralDeclarations.DeclarationChecked constructors roles declaration →
    ∀ (capture : Yulang.GeneralDeclarationDemands.Capture) (demand : Yulang.GeneralSourceState.Demand roles)
      (head : Fin (roles demand.role).arity → Yulang.Core.PresenceGeneration.TyTerm (Fin state.slots)),
      Yulang.GeneralDictionaryVariableHeads.HeadDenotes declaration capture demand head →
        ∀ (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
          Yulang.GeneralDictionaryNominalSourceEvidence.Realizes declaration capture assignment
            (Yulang.GeneralDictionaryNominalSourceEvidence.values declaration capture assignment)
```

## 56. `Yulang.GeneralDictionaryNominalSourceEvidence.singleton_value`
側: 補助。任意の同一source IDの上下端と、その区間内のnominal値について、その値は端点と同値。

```lean
Yulang.GeneralDictionaryNominalSourceEvidence.singleton_value : ∀ (capture : Yulang.GeneralDeclarationDemands.Capture)
  (assignment : Yulang.GeneralNominalCommonBridge.Assignment) (binder : Nat)
  (value : Yulang.CommonNominalFullCarrier.Ty),
  (capture.inputs binder).fst = (capture.inputs binder).snd →
    Yulang.CommonNominalFullCarrier.Subtype (assignment (capture.inputs binder).fst).fst value ∧
        Yulang.CommonNominalFullCarrier.Subtype value (assignment (capture.inputs binder).snd).fst →
      Yulang.CommonNominalFullCarrier.Equivalent value (assignment (capture.inputs binder).fst).fst
```

## 57. `Yulang.GeneralDictionaryNominalSourceEvidence.head_realization`
側: 健全性。任意実positional変数headのDenotesAtとcapture実現について、実head patternとbinderが存在し、その値とsource term評価が同値。

```lean
@Yulang.GeneralDictionaryNominalSourceEvidence.head_realization : ∀ {state : Yulang.GeneralSourceState.State}
  (declaration : Yulang.GeneralDeclarations.Declaration) (capture : Yulang.GeneralDeclarationDemands.Capture)
  (assignment : Yulang.GeneralNominalCommonBridge.Assignment) (values : Nat → Yulang.CommonNominalFullCarrier.Ty),
  Yulang.GeneralDictionaryNominalSourceEvidence.Realizes declaration capture assignment values →
    ∀ (index : Nat) (term : Yulang.Core.PresenceGeneration.TyTerm (Fin state.slots)),
      Yulang.GeneralDictionaryVariableHeads.DenotesAt state declaration capture index term →
        ∃ pattern binder,
          declaration.head[index]? = some pattern ∧
            Yulang.GeneralDeclarationPatterns.normalize pattern = Yulang.GeneralDeclarationPatterns.Pattern.var binder ∧
              Yulang.CommonNominalFullCarrier.Equivalent (values binder)
                (Yulang.Core.PresenceGeneration.TyTerm.eval Yulang.CommonNominalFullCarrier.model assignment
                  (Yulang.GeneralDictionaryStateEquations.liftType state term))
```

## 58. `Yulang.GeneralDictionaryNominalSourceEvidence.output_realization`
側: 健全性。任意実RHS変数Denotesとcapture実現について、実associated式とbinderが存在し、その値とterm評価が同値。

```lean
Yulang.GeneralDictionaryNominalSourceEvidence.output_realization : ∀ (roles : Yulang.Roles.RoleDecls)
  (declaration : Yulang.GeneralDeclarations.Declaration) (capture : Yulang.GeneralDeclarationDemands.Capture)
  (assignment : Yulang.GeneralNominalCommonBridge.Assignment) (values : Nat → Yulang.CommonNominalFullCarrier.Ty),
  Yulang.GeneralDictionaryNominalSourceEvidence.Realizes declaration capture assignment values →
    ∀ (name : Nat) (term : Yulang.Core.PresenceGeneration.TyTerm Nat),
      Yulang.GeneralDictionaryVariableTerms.Denotes roles declaration capture name term →
        ∃ equation binder,
          Yulang.GeneralDictionaryAssociatedProvenance.Supplies roles declaration name
              (Yulang.GeneralDictionaryAssociatedProvenance.Body.explicit equation) ∧
            Yulang.GeneralDeclarationPatterns.normalize equation.rhs =
                Yulang.GeneralDeclarationPatterns.Pattern.var binder ∧
              Yulang.CommonNominalFullCarrier.Equivalent (values binder)
                (Yulang.Core.PresenceGeneration.TyTerm.eval Yulang.CommonNominalFullCarrier.model assignment term)
```

## 59. `Yulang.GeneralDictionaryNominalSourceEvidence.source_instance`
側: 健全性。任意checked registry・frames・nominal assignment・root/key/children・Locatedについて、実Plan、実head/RHS TermsとHoldsから独立source Instanceを導く。

```lean
@Yulang.GeneralDictionaryNominalSourceEvidence.source_instance : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (assignment : Yulang.GeneralNominalCommonBridge.Assignment)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles) (key : Nat)
  (children : List (Yulang.GeneralSourceDictionaries.Occurrence registry.roles))
  (located : Yulang.GeneralDictionaryStateEquations.Located state root.demand),
  Yulang.GeneralDictionaryEmissionPlans.Plan registry checked (frames root) root key children →
    Yulang.GeneralDictionaryVariablePlans.Terms registry frames
        (Yulang.GeneralDictionaryVariableHeads.heads registry.roles state) root key located →
      Yulang.GeneralDictionaryNominalEquations.Holds located.equations assignment →
        Yulang.GeneralDictionaryNominalSourceEvidence.Instance registry checked frames assignment root key children
```

## 60. `Yulang.GeneralDictionaryNominalSourceEvidence.transaction_evidence`
側: 健全性。任意Built木と任意joint nominal modelについて、その実返却source辞書に独立Instance Evidenceが成立する。

```lean
@Yulang.GeneralDictionaryNominalSourceEvidence.transaction_evidence : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (tree : Yulang.GeneralDictionaryTransactions.Prepared registry.roles state),
  Yulang.GeneralDictionaryVariableTransactions.Built registry checked frames
      (Yulang.GeneralDictionaryVariableHeads.heads registry.roles state) tree →
    ∀ (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.GeneralNominalCommonBridge.Models (Yulang.GeneralDictionaryBatchRecording.record tree.items) assignment →
        Yulang.GeneralSourceDictionaries.Evidence
          (Yulang.GeneralDictionaryNominalSourceEvidence.Instance registry checked frames assignment) tree.dictionary
```

## 61. `Yulang.GeneralDictionaryNominalSourceEvidence.prepare_uniform_source`
側: 健全性。任意の準備成功について、一つの固定source witnessが元raw payloadをReadbackし、記録batchの全modelで独立Instance Evidenceを持つ。Common版と任意nominal版はそれぞれ型のModelsを参照。

```lean
Yulang.GeneralDictionaryNominalSourceEvidence.prepare_uniform_source : ∀
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (state : Yulang.GeneralSourceState.State) (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (payload : Yulang.GeneralDictionaryReadback.Payload)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles)
  (tree : Yulang.GeneralDictionaryTransactions.Prepared registry.roles state),
  Yulang.GeneralDictionaryPayloadPreparation.prepare registry checked state frames payload root = some tree →
    ∃ witness,
      Yulang.GeneralSourceDictionaries.Readback root payload witness ∧
        ∀ (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
          Yulang.GeneralNominalCommonBridge.Models (Yulang.GeneralDictionaryBatchRecording.record tree.items)
              assignment →
            Yulang.GeneralSourceDictionaries.Evidence
              (Yulang.GeneralDictionaryNominalSourceEvidence.Instance registry checked frames assignment) witness
```

## 62. `Yulang.GeneralDictionaryNominalSourceExamples.raw_nominal_nonvacuous`
側: 補助。実raw fixtureで準備成功、nominal73のjoint model、元payloadのReadbackと独立source Evidenceが同時に成立する。

```lean
Yulang.GeneralDictionaryNominalSourceExamples.raw_nominal_nonvacuous : Yulang.GeneralDictionaryPayloadPreparation.prepare
      Yulang.GeneralDictionaryHeadlessFixture.registry Yulang.GeneralDictionaryHeadlessFixture.registry_checked
      Yulang.GeneralDictionaryHeadlessFixture.state (fun x => Yulang.GeneralDictionaryHeadlessFixture.frame)
      Yulang.GeneralDictionaryPayloadReconstructionExamples.payload Yulang.GeneralDictionaryHeadlessFixture.root =
    some Yulang.GeneralDictionaryHeadlessFixture.tree ∧
  Yulang.GeneralNominalCommonBridge.Models
      (Yulang.GeneralDictionaryBatchRecording.record Yulang.GeneralDictionaryHeadlessFixture.tree.items)
      Yulang.GeneralDictionaryNominalExamples.nominalAssignment ∧
    ∃ witness,
      Yulang.GeneralSourceDictionaries.Readback Yulang.GeneralDictionaryHeadlessFixture.root
          Yulang.GeneralDictionaryPayloadReconstructionExamples.payload witness ∧
        Yulang.GeneralSourceDictionaries.Evidence
          (Yulang.GeneralDictionaryNominalSourceEvidence.Instance Yulang.GeneralDictionaryHeadlessFixture.registry
            Yulang.GeneralDictionaryHeadlessFixture.registry_checked
            (fun x => Yulang.GeneralDictionaryHeadlessFixture.frame)
            Yulang.GeneralDictionaryNominalExamples.nominalAssignment)
          witness
```

## 63. `Yulang.GeneralDictionaryNominalSourceExamples.raw_nominal_payload_evidence`
側: 健全性。同nominal73 modelで、実fixtureの元raw payloadに独立source PayloadEvidenceがある。

```lean
Yulang.GeneralDictionaryNominalSourceExamples.raw_nominal_payload_evidence : Yulang.GeneralDictionaryReadback.PayloadEvidence
  (Yulang.GeneralDictionaryNominalSourceEvidence.Instance Yulang.GeneralDictionaryHeadlessFixture.registry
    Yulang.GeneralDictionaryHeadlessFixture.registry_checked (fun x => Yulang.GeneralDictionaryHeadlessFixture.frame)
    Yulang.GeneralDictionaryNominalExamples.nominalAssignment)
  Yulang.GeneralDictionaryHeadlessFixture.root Yulang.GeneralDictionaryPayloadReconstructionExamples.payload
```

## 64. `Yulang.GeneralDictionaryNominalStateEvidence.prepare_uniform`
側: 健全性。任意のfull-state上のraw準備成功で、一つのReadback witnessがあり、全full記録modelで元Modelsと独立Instance Evidenceを満たす。

```lean
Yulang.GeneralDictionaryNominalStateEvidence.prepare_uniform : ∀ (registry : Yulang.GeneralDeclarations.Registry)
  (checked : Yulang.GeneralDeclarations.Checked registry) (state : Yulang.GeneralNominalState.State)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (payload : Yulang.GeneralDictionaryReadback.Payload)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles)
  (tree : Yulang.GeneralDictionaryTransactions.Prepared registry.roles state.base),
  Yulang.GeneralDictionaryPayloadPreparation.prepare registry checked state.base frames payload root = some tree →
    ∃ witness,
      Yulang.GeneralSourceDictionaries.Readback root payload witness ∧
        ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
          Yulang.GeneralNominalState.Models (Yulang.GeneralDictionaryNominalRecording.record state tree.items) model →
            Yulang.GeneralNominalState.Models state model ∧
              Yulang.GeneralSourceDictionaries.Evidence
                (Yulang.GeneralDictionaryNominalSourceEvidence.Instance registry checked frames model) witness
```

## 65. `Yulang.GeneralDictionaryNominalStateEvidence.prepare_payload_evidence`
側: 健全性。任意の準備成功と記録状態のmodelについて、元のraw payload自体に独立InstanceのPayloadEvidenceがある。

```lean
Yulang.GeneralDictionaryNominalStateEvidence.prepare_payload_evidence : ∀
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (state : Yulang.GeneralNominalState.State) (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (payload : Yulang.GeneralDictionaryReadback.Payload)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles)
  (tree : Yulang.GeneralDictionaryTransactions.Prepared registry.roles state.base),
  Yulang.GeneralDictionaryPayloadPreparation.prepare registry checked state.base frames payload root = some tree →
    ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.GeneralNominalState.Models (Yulang.GeneralDictionaryNominalRecording.record state tree.items) model →
        Yulang.GeneralDictionaryReadback.PayloadEvidence
          (Yulang.GeneralDictionaryNominalSourceEvidence.Instance registry checked frames model) root payload
```

## 66. `Yulang.GeneralDictionaryNominalStateExamples.full_base_model`
側: 補助。展示したfull nominal stateをnominal73 assignmentが満たす。

```lean
Yulang.GeneralDictionaryNominalStateExamples.full_base_model : Yulang.GeneralNominalState.Models
  Yulang.GeneralDictionaryNominalStateExamples.fullState Yulang.GeneralDictionaryNominalExamples.nominalAssignment
```

## 67. `Yulang.GeneralDictionaryNominalStateExamples.full_record_model`
側: 補助。展示したfull nominal stateへの全dictionary記録を同じassignmentが満たす。

```lean
Yulang.GeneralDictionaryNominalStateExamples.full_record_model : Yulang.GeneralNominalState.Models
  (Yulang.GeneralDictionaryNominalRecording.record Yulang.GeneralDictionaryNominalStateExamples.fullState
    Yulang.GeneralDictionaryHeadlessFixture.tree.items)
  Yulang.GeneralDictionaryNominalExamples.nominalAssignment
```

## 68. `Yulang.GeneralDictionaryNominalStateExamples.full_nominal_nonvacuous`
側: 補助。展示したfull記録stateのmodelと、元raw payloadの独立nominal source Evidenceが同時に成立する。

```lean
Yulang.GeneralDictionaryNominalStateExamples.full_nominal_nonvacuous : Yulang.GeneralNominalState.Models
    (Yulang.GeneralDictionaryNominalRecording.record Yulang.GeneralDictionaryNominalStateExamples.fullState
      Yulang.GeneralDictionaryHeadlessFixture.tree.items)
    Yulang.GeneralDictionaryNominalExamples.nominalAssignment ∧
  Yulang.GeneralDictionaryReadback.PayloadEvidence
    (Yulang.GeneralDictionaryNominalSourceEvidence.Instance Yulang.GeneralDictionaryHeadlessFixture.registry
      Yulang.GeneralDictionaryHeadlessFixture.registry_checked (fun x => Yulang.GeneralDictionaryHeadlessFixture.frame)
      Yulang.GeneralDictionaryNominalExamples.nominalAssignment)
    Yulang.GeneralDictionaryHeadlessFixture.root Yulang.GeneralDictionaryPayloadReconstructionExamples.payload
```

## 69. `Yulang.GeneralDictionaryNominalStateExamples.full_root_pending`
側: 補助。展示したfull nominal stateで根はRootPending。model存在はknownnessを意味しない。

```lean
Yulang.GeneralDictionaryNominalStateExamples.full_root_pending : Yulang.GeneralNominalState.RootPending
  Yulang.GeneralDictionaryNominalStateExamples.fullState Yulang.GeneralDictionaryHeadlessFixture.rootDemand
```

## 70. `Yulang.GeneralDictionaryNominalStateExamples.recorded_root_pending`
側: 補助。同full stateのdictionary記録後も根はRootPending。

```lean
Yulang.GeneralDictionaryNominalStateExamples.recorded_root_pending : Yulang.GeneralNominalState.RootPending
  (Yulang.GeneralDictionaryNominalRecording.record Yulang.GeneralDictionaryNominalStateExamples.fullState
    Yulang.GeneralDictionaryHeadlessFixture.tree.items)
  Yulang.GeneralDictionaryHeadlessFixture.rootDemand
```

## 71. `Yulang.GeneralDictionaryNominalCandidateReadback.declaration_found`
側: 補助。任意checked registry・visible宣言・同key/roleのrootについて、有限検索はその実宣言を返す。

```lean
Yulang.GeneralDictionaryNominalCandidateReadback.declaration_found : ∀ (registry : Yulang.GeneralDeclarations.Registry),
  Yulang.GeneralDeclarations.Checked registry →
    ∀ (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles) (key : Nat)
      (selected : Yulang.GeneralDeclarations.Declaration),
      selected ∈ registry.declarations →
        selected.id = key →
          selected.role = root.demand.role →
            Yulang.GeneralDictionaryNominalCandidateReadback.declaration registry root key = some selected
```

## 72. `Yulang.GeneralDictionaryNominalCandidateReadback.bindings_found`
側: 補助。上記条件と実arguments取得成功で、計算bindingsは同じ実宣言のinspection report由来bindingsに等しい。

```lean
Yulang.GeneralDictionaryNominalCandidateReadback.bindings_found : ∀ (registry : Yulang.GeneralDeclarations.Registry),
  Yulang.GeneralDeclarations.Checked registry →
    ∀ (context : Yulang.GeneralNominalCandidates.Context)
      (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles) (key : Nat)
      (selected : Yulang.GeneralDeclarations.Declaration),
      selected ∈ registry.declarations →
        selected.id = key →
          selected.role = root.demand.role →
            ∀ (bounds : List (Yulang.GeneralNominalInspection.Bounds context.state)),
              Yulang.GeneralNominalCandidates.arguments context root = some bounds →
                Yulang.GeneralDictionaryNominalCandidateReadback.bindings registry context root key =
                  Yulang.GeneralNominalInspection.bindings context.state
                    (Yulang.GeneralNominalCandidates.report context selected bounds)
```

## 73. `Yulang.GeneralDictionaryNominalCandidateReadback.survivor_plan`
側: 補助。任意既存Survivorから、同registry/contextの実reportで計算したframes上の完全Planを得る。

```lean
Yulang.GeneralDictionaryNominalCandidateReadback.survivor_plan : ∀ (registry : Yulang.GeneralDeclarations.Registry)
  (checked : Yulang.GeneralDeclarations.Checked registry) (context : Yulang.GeneralNominalCandidates.Context)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles) (key : Nat)
  (children : List (Yulang.GeneralSourceDictionaries.Occurrence registry.roles)),
  Yulang.GeneralNominalCandidates.Survivor registry context root key children →
    Yulang.GeneralDictionaryEmissionPlans.Plan registry checked
      (Yulang.GeneralDictionaryNominalCandidateReadback.frames registry context root) root key children
```

## 74. `Yulang.GeneralDictionaryNominalCandidateReadback.evidence_plan`
側: 健全性。任意source辞書が同じContextで全nodeのSurvivor Evidenceを持つなら、計算frames上のPlan Evidenceを持つ。

```lean
Yulang.GeneralDictionaryNominalCandidateReadback.evidence_plan : ∀ (registry : Yulang.GeneralDeclarations.Registry)
  (checked : Yulang.GeneralDeclarations.Checked registry) (context : Yulang.GeneralNominalCandidates.Context)
  (tree : Yulang.GeneralSourceDictionaries.Dictionary registry.roles),
  Yulang.GeneralSourceDictionaries.Evidence (Yulang.GeneralNominalCandidates.Survivor registry context) tree →
    Yulang.GeneralSourceDictionaries.Evidence
      (Yulang.GeneralDictionaryPayloadReconstruction.Rule registry checked
        (Yulang.GeneralDictionaryNominalCandidateReadback.frames registry context))
      tree
```

## 75. `Yulang.GeneralDictionaryNominalCandidateReadback.reconstruct_candidate`
側: 補助。上記任意candidate Evidence木は、計算framesによって元raw payloadとrootから正確に再構成される。

```lean
Yulang.GeneralDictionaryNominalCandidateReadback.reconstruct_candidate : ∀
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (context : Yulang.GeneralNominalCandidates.Context)
  (tree : Yulang.GeneralSourceDictionaries.Dictionary registry.roles),
  Yulang.GeneralSourceDictionaries.Evidence (Yulang.GeneralNominalCandidates.Survivor registry context) tree →
    Yulang.GeneralDictionaryNominalCandidateReadback.reconstruct registry checked context
        (Yulang.GeneralSourceDictionaries.erase tree) tree.root =
      some tree
```

## 76. `Yulang.GeneralDictionaryNominalCandidateReadback.payload_candidate_readback`
側: 補助。任意raw candidate PayloadEvidenceから、計算再構成成功・元Readback・同ContextのCandidate Evidenceを持つ一つのsource treeを得る。

```lean
Yulang.GeneralDictionaryNominalCandidateReadback.payload_candidate_readback : ∀
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (context : Yulang.GeneralNominalCandidates.Context)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles)
  (payload : Yulang.GeneralDictionaryReadback.Payload),
  Yulang.GeneralDictionaryReadback.PayloadEvidence (Yulang.GeneralNominalCandidates.Survivor registry context) root
      payload →
    ∃ tree,
      Yulang.GeneralDictionaryNominalCandidateReadback.reconstruct registry checked context payload root = some tree ∧
        Yulang.GeneralSourceDictionaries.Readback root payload tree ∧
          Yulang.GeneralSourceDictionaries.Evidence (Yulang.GeneralNominalCandidates.Survivor registry context) tree
```

## 77. `Yulang.GeneralDictionaryNominalCandidateReadback.payload_candidate_unique`
側: 補助。上記条件で、同root/raw payloadの他の任意candidate Evidence witnessは返却treeに等しい。

```lean
Yulang.GeneralDictionaryNominalCandidateReadback.payload_candidate_unique : ∀
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (context : Yulang.GeneralNominalCandidates.Context)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles)
  (payload : Yulang.GeneralDictionaryReadback.Payload),
  Yulang.GeneralDictionaryReadback.PayloadEvidence (Yulang.GeneralNominalCandidates.Survivor registry context) root
      payload →
    ∃ tree,
      Yulang.GeneralDictionaryNominalCandidateReadback.reconstruct registry checked context payload root = some tree ∧
        Yulang.GeneralSourceDictionaries.Readback root payload tree ∧
          Yulang.GeneralSourceDictionaries.Evidence (Yulang.GeneralNominalCandidates.Survivor registry context) tree ∧
            ∀ (other : Yulang.GeneralSourceDictionaries.Dictionary registry.roles),
              Yulang.GeneralSourceDictionaries.Readback root payload other →
                Yulang.GeneralSourceDictionaries.Evidence (Yulang.GeneralNominalCandidates.Survivor registry context)
                    other →
                  other = tree
```

## 78. `Yulang.GeneralDictionaryNominalCandidateReadbackExamples.root_plan`
側: 補助。既存nominal Display fixtureの実Survivorから、計算frames上の完全root Planを得る。

```lean
Yulang.GeneralDictionaryNominalCandidateReadbackExamples.root_plan : Yulang.GeneralDictionaryEmissionPlans.Plan
  Yulang.GeneralNominalExamples.registry Yulang.GeneralNominalExamples.registry_checked
  (Yulang.GeneralDictionaryNominalCandidateReadback.frames Yulang.GeneralNominalExamples.registry
    (Yulang.GeneralNominalExamples.context true) Yulang.GeneralNominalExamples.displayRoot)
  Yulang.GeneralNominalExamples.displayRoot 1 [Yulang.GeneralNominalExamples.displayChild]
```

## 79. `Yulang.GeneralDictionaryNominalCandidateReadbackExamples.leaf_plan`
側: 補助。同fixtureのvisible terminal Int宣言から空子列のPlanを得る。leaf Survivorは証明していない。

```lean
Yulang.GeneralDictionaryNominalCandidateReadbackExamples.leaf_plan : Yulang.GeneralDictionaryEmissionPlans.Plan
  Yulang.GeneralNominalExamples.registry Yulang.GeneralNominalExamples.registry_checked
  (Yulang.GeneralDictionaryNominalCandidateReadback.frames Yulang.GeneralNominalExamples.registry
    (Yulang.GeneralNominalExamples.context true) Yulang.GeneralNominalExamples.displayChild)
  Yulang.GeneralNominalExamples.displayChild 3 []
```

## 80. `Yulang.GeneralDictionaryNominalCandidateReadbackExamples.source_plan_evidence`
側: 健全性。同fixtureの二node source tree全体にPlan Evidenceがある。完全candidate森林とは言わない。

```lean
Yulang.GeneralDictionaryNominalCandidateReadbackExamples.source_plan_evidence : Yulang.GeneralSourceDictionaries.Evidence
  (Yulang.GeneralDictionaryPayloadReconstruction.Rule Yulang.GeneralNominalExamples.registry
    Yulang.GeneralNominalExamples.registry_checked
    (Yulang.GeneralDictionaryNominalCandidateReadback.frames Yulang.GeneralNominalExamples.registry
      (Yulang.GeneralNominalExamples.context true)))
  Yulang.GeneralDictionaryNominalCandidateReadbackExamples.sourceTree
```

## 81. `Yulang.GeneralDictionaryNominalCandidateReadbackExamples.tree_reconstructed`
側: 補助。実fixtureのraw二node key木から、全source occurrenceを保持した正確な辞書treeが返る。計算frames版でも外部child recipeは不要。

```lean
Yulang.GeneralDictionaryNominalCandidateReadbackExamples.tree_reconstructed : Yulang.GeneralDictionaryNominalCandidateReadback.reconstruct
    Yulang.GeneralNominalExamples.registry Yulang.GeneralNominalExamples.registry_checked
    (Yulang.GeneralNominalExamples.context true) Yulang.GeneralDictionaryNominalCandidateReadbackExamples.payload
    Yulang.GeneralNominalExamples.displayRoot =
  some Yulang.GeneralDictionaryNominalCandidateReadbackExamples.sourceTree
```

## 82. `Yulang.GeneralDictionaryNominalCandidateReadbackExamples.omitted_child_defers`
側: 補助。実fixtureで必要なraw子を落とすと再構成noneになる。未完成の辞書を成功にしない。

```lean
Yulang.GeneralDictionaryNominalCandidateReadbackExamples.omitted_child_defers : Yulang.GeneralDictionaryNominalCandidateReadback.reconstruct
    Yulang.GeneralNominalExamples.registry Yulang.GeneralNominalExamples.registry_checked
    (Yulang.GeneralNominalExamples.context true) (Yulang.CommonRoleOutermostResolver.Dictionary.node 1 [])
    Yulang.GeneralNominalExamples.displayRoot =
  none
```

## 83. `Yulang.GeneralDictionaryNominalCandidateReadbackExamples.source_child_preserved`
側: 補助。同fixtureの計算再構成で、実displayChildのidentityと完全demandが観察列に保持される。

```lean
Yulang.GeneralDictionaryNominalCandidateReadbackExamples.source_child_preserved : ∃ result,
  Yulang.GeneralDictionaryNominalCandidateReadback.reconstruct Yulang.GeneralNominalExamples.registry
        Yulang.GeneralNominalExamples.registry_checked (Yulang.GeneralNominalExamples.context true)
        Yulang.GeneralDictionaryNominalCandidateReadbackExamples.payload Yulang.GeneralNominalExamples.displayRoot =
      some result ∧
    Yulang.GeneralSourceDictionaries.observations result =
      [(Yulang.GeneralNominalExamples.displayRoot, 1), (Yulang.GeneralNominalExamples.displayChild, 3)]
```

## 84. `Yulang.GeneralDictionaryNominalCandidateReadbackExamples.source_readback`
側: 補助。実fixtureの返却source辞書が元root/raw payloadをReadbackする。Plan Evidence併記版は完全Planも述べる。

```lean
Yulang.GeneralDictionaryNominalCandidateReadbackExamples.source_readback : Yulang.GeneralSourceDictionaries.Readback
  Yulang.GeneralNominalExamples.displayRoot Yulang.GeneralDictionaryNominalCandidateReadbackExamples.payload
  Yulang.GeneralDictionaryNominalCandidateReadbackExamples.sourceTree
```

## 85. `Yulang.GeneralDictionaryNominalCandidateEvidence.prepare_candidate_evidence`
側: 健全性。任意の同Contextのraw Candidate Evidenceと計算frames準備成功について、実返却辞書自体にそのCandidate Evidenceがある。

```lean
Yulang.GeneralDictionaryNominalCandidateEvidence.prepare_candidate_evidence : ∀
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (context : Yulang.GeneralNominalCandidates.Context) (payload : Yulang.GeneralDictionaryReadback.Payload)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles)
  (tree : Yulang.GeneralDictionaryTransactions.Prepared registry.roles context.state.base),
  Yulang.GeneralDictionaryReadback.PayloadEvidence (Yulang.GeneralNominalCandidates.Survivor registry context) root
      payload →
    Yulang.GeneralDictionaryNominalCandidateEvidence.prepare registry checked context payload root = some tree →
      Yulang.GeneralSourceDictionaries.Evidence (Yulang.GeneralNominalCandidates.Survivor registry context)
        tree.dictionary
```

## 86. `Yulang.GeneralDictionaryNominalCandidateEvidence.prepare_source_evidence`
側: 健全性。任意計算frames準備成功とfull記録modelについて、同じ実返却辞書に独立nominal Instance Evidenceがある。

```lean
Yulang.GeneralDictionaryNominalCandidateEvidence.prepare_source_evidence : ∀
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (context : Yulang.GeneralNominalCandidates.Context) (payload : Yulang.GeneralDictionaryReadback.Payload)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles)
  (tree : Yulang.GeneralDictionaryTransactions.Prepared registry.roles context.state.base),
  Yulang.GeneralDictionaryNominalCandidateEvidence.prepare registry checked context payload root = some tree →
    ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.GeneralNominalState.Models (Yulang.GeneralDictionaryNominalRecording.record context.state tree.items)
          model →
        Yulang.GeneralSourceDictionaries.Evidence
          (Yulang.GeneralDictionaryNominalSourceEvidence.Instance registry checked
            (Yulang.GeneralDictionaryNominalCandidateReadback.frames registry context) model)
          tree.dictionary
```

## 87. `Yulang.GeneralDictionaryNominalCandidateEvidence.prepare_uniform_joint`
側: 健全性。任意raw Candidate Evidenceと計算frames準備成功について、一つの固定witnessが元Readback・Candidate Evidenceを持ち、全full記録modelで元Modelsと独立source Evidenceを満たす。

```lean
Yulang.GeneralDictionaryNominalCandidateEvidence.prepare_uniform_joint : ∀
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (context : Yulang.GeneralNominalCandidates.Context) (payload : Yulang.GeneralDictionaryReadback.Payload)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles)
  (tree : Yulang.GeneralDictionaryTransactions.Prepared registry.roles context.state.base),
  Yulang.GeneralDictionaryReadback.PayloadEvidence (Yulang.GeneralNominalCandidates.Survivor registry context) root
      payload →
    Yulang.GeneralDictionaryNominalCandidateEvidence.prepare registry checked context payload root = some tree →
      ∃ witness,
        Yulang.GeneralSourceDictionaries.Readback root payload witness ∧
          Yulang.GeneralSourceDictionaries.Evidence (Yulang.GeneralNominalCandidates.Survivor registry context)
              witness ∧
            ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
              Yulang.GeneralNominalState.Models
                  (Yulang.GeneralDictionaryNominalRecording.record context.state tree.items) model →
                Yulang.GeneralNominalState.Models context.state model ∧
                  Yulang.GeneralSourceDictionaries.Evidence
                    (Yulang.GeneralDictionaryNominalSourceEvidence.Instance registry checked
                      (Yulang.GeneralDictionaryNominalCandidateReadback.frames registry context) model)
                    witness
```

## 88. `Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.terminal_checked`
側: 補助。展示したkey7・role0・変数head一つ・子なし宣言が既存DeclarationCheckedの全条件を満たす。

```lean
Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.terminal_checked : Yulang.GeneralDeclarations.DeclarationChecked
  Yulang.GeneralDeclarationExamples.constructors Yulang.GeneralDeclarationExamples.roles
  Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.terminal
```

## 89. `Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.registry_checked`
側: 補助。同singleton registryが既存Checkedを満たす。

```lean
Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.registry_checked : Yulang.GeneralDeclarations.Checked
  Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.registry
```

## 90. `Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.located`
側: 補助。同既存contextの根需要の実argument探索がsource区間(1,1)を返す。

```lean
Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.located : Yulang.GeneralNominalCandidates.arguments
    (Yulang.GeneralNominalExamples.context true) Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.root =
  some [(1, 1)]
```

## 91. `Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.report`
側: 補助。同実宣言のinspection reportはbinder0と区間(1,1)を捕捉・inspection記録する。

```lean
Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.report : Yulang.GeneralNominalCandidates.report
    (Yulang.GeneralNominalExamples.context true) Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.terminal
    [(1, 1)] =
  { captures := [(0, 1, 1)], inspected := [(1, 1)] }
```

## 92. `Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.survivor`
側: 補助。同registry/context/rootのkey7が全既存guardを満たす実Survivorである。outputsは空のまま。

```lean
Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.survivor : Yulang.GeneralNominalCandidates.Survivor
  Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.registry (Yulang.GeneralNominalExamples.context true)
  Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.root 7 []
```

## 93. `Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.candidate_payload`
側: 補助。同終端raw payloadは既存SurvivorのPayloadEvidenceを持つ。

```lean
Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.candidate_payload : Yulang.GeneralDictionaryReadback.PayloadEvidence
  (Yulang.GeneralNominalCandidates.Survivor Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.registry
    (Yulang.GeneralNominalExamples.context true))
  Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.root
  Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.payload
```

## 94. `Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.preparation_exists`
側: 補助。同raw payloadを実computedFramesで準備するとisSomeであり、条件付き定理の成功前提が空ではない。

```lean
Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.preparation_exists : (Yulang.GeneralDictionaryNominalCandidateEvidence.prepare
      Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.registry
      Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.registry_checked
      (Yulang.GeneralNominalExamples.context true) Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.payload
      Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.root).isSome =
  true
```

## 95. `Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.preparation_success`
側: 補助。同raw payloadの実準備結果は定義されたtreeである。

```lean
Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.preparation_success : Yulang.GeneralDictionaryNominalCandidateEvidence.prepare
    Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.registry
    Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.registry_checked
    (Yulang.GeneralNominalExamples.context true) Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.payload
    Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.root =
  some Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.tree
```

## 96. `Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.tree_items`
側: 補助。実準備したtreeのpackageは、実source需要とslot1へLocatedされた一件に正確に等しい。

```lean
Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.tree_items : Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.tree.items =
  [{ demand := Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.demand,
      located := Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.locatedTerms }]
```

## 97. `Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.recorded_model`
側: 補助。実準備packageをfull nominal stateへ記録した状態を既存の具体modelが満たす。

```lean
Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.recorded_model : Yulang.GeneralNominalState.Models
  (Yulang.GeneralDictionaryNominalRecording.record (Yulang.GeneralNominalExamples.state true)
    Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.tree.items)
  Yulang.GeneralNominalExamples.model
```

## 98. `Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.joint_nonvacuous`
側: 補助。同実raw payloadにcandidate Evidence、computed-frame準備成功、具体full記録modelが同時に成立し、一つのReadback witnessがcandidateと独立nominal source Evidenceを共に持つ。

```lean
Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.joint_nonvacuous : Yulang.GeneralDictionaryReadback.PayloadEvidence
    (Yulang.GeneralNominalCandidates.Survivor Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.registry
      (Yulang.GeneralNominalExamples.context true))
    Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.root
    Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.payload ∧
  Yulang.GeneralDictionaryNominalCandidateEvidence.prepare
        Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.registry
        Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.registry_checked
        (Yulang.GeneralNominalExamples.context true) Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.payload
        Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.root =
      some Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.tree ∧
    Yulang.GeneralNominalState.Models
        (Yulang.GeneralDictionaryNominalRecording.record (Yulang.GeneralNominalExamples.state true)
          Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.tree.items)
        Yulang.GeneralNominalExamples.model ∧
      ∃ witness,
        Yulang.GeneralSourceDictionaries.Readback Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.root
            Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.payload witness ∧
          Yulang.GeneralSourceDictionaries.Evidence
              (Yulang.GeneralNominalCandidates.Survivor
                Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.registry
                (Yulang.GeneralNominalExamples.context true))
              witness ∧
            Yulang.GeneralSourceDictionaries.Evidence
              (Yulang.GeneralDictionaryNominalSourceEvidence.Instance
                Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.registry
                Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.registry_checked
                (Yulang.GeneralDictionaryNominalCandidateReadback.frames
                  Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.registry
                  (Yulang.GeneralNominalExamples.context true))
                Yulang.GeneralNominalExamples.model)
              witness
```
