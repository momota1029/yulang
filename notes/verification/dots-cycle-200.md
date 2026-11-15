# Cycle 200 verification outputs

Tested local source `9970c1a7b`; source publication `5bc25be4c98ce284094b6ae105893ec18cfca04d`.
Commands from `lean/` except git checks from repository root. Each Lean command used a240s timeout. No full repository build or all-history audit ran.

## final-build

```sh
lake build --wfail Yulang.GeneralDictionaryMatScalarOutputs200 Yulang.GeneralDictionaryMatScalarFixture200 Yulang.GeneralDictionaryMatScalarConflict200 Yulang.GeneralDictionaryMatStableScalar200 Yulang.GeneralDictionaryMatSelectedScalar200
```

Exit: 0

```text
Build completed successfully (1079 jobs).
```

## terminal-build

```sh
lake build --wfail Yulang.GeneralDictionaryMatTerminalAssembly200
```

Exit: 0

```text
Build completed successfully (1020 jobs).
```

## final-MatScalarOutputs200

```sh
lake env lean --trust=0 -DwarningAsError=true Audit/MatScalarOutputs200.lean
```

Exit: 0

```text
Yulang.GeneralDictionaryMatScalarOutputs200.ScalarRequests (registry : Yulang.GeneralDeclarations.Registry)
  (context : Yulang.GeneralNominalRecursiveCandidates.Context)
  (requests : List Yulang.GeneralNominalMaterialization.Request) : Prop
Yulang.GeneralDictionaryMatScalarOutputs200.branch_of_total {roles : Yulang.Roles.RoleDecls}
  (plan : Yulang.GeneralNominalCenters.Plan roles) (assignment : Yulang.GeneralNominalCommonBridge.Assignment)
  (holds : Yulang.GeneralNominalCenteredHeadMatStepPackets.Holds plan assignment)
  (variables : Yulang.GeneralDictionaryVariableRequirements.VariableClauses plan.packet.declaration)
  (scalars :
    Yulang.GeneralDictionaryMatScalarOutputs200.ScalarRequests plan.packet.registry plan.packet.context
      (Yulang.GeneralNominalMaterialization.rootRequests plan.packet.declaration plan.packet.site.occurrence)) :
  Yulang.GeneralNominalRecursiveCandidates.BranchModels plan.packet.registry plan.packet.context
    plan.packet.site.occurrence plan.packet.declaration ⋯ plan.packet.bounds assignment
Yulang.GeneralDictionaryMatScalarOutputs200.evidence_of_recorded {roles : Yulang.Roles.RoleDecls}
  (plan : Yulang.GeneralNominalCenters.Plan roles) (state : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles)
  (framed :
    Yulang.GeneralNominalCenteredHeadOutputs.Frame plan.packet.registry state.core plan.packet.site.occurrence
      plan.packet.declaration.id plan)
  (recorded : plan ∈ state.core.plans) (assignment : Yulang.GeneralNominalCommonBridge.Assignment)
  (models : Yulang.GeneralNominalCenteredHeadMatStepJournal.Models state assignment)
  (variables : Yulang.GeneralDictionaryVariableRequirements.VariableClauses plan.packet.declaration)
  (defined : Yulang.GeneralNominalMaterialization.RootDefined plan.packet.declaration plan.packet.site.occurrence)
  (scalars :
    Yulang.GeneralDictionaryMatScalarOutputs200.ScalarRequests plan.packet.registry plan.packet.context
      (Yulang.GeneralNominalMaterialization.rootRequests plan.packet.declaration plan.packet.site.occurrence))
  (dictionaries : List Yulang.CommonRoleOutermostResolver.Dictionary)
  (children :
    Yulang.CommonRoleOutermostResolver.All₂
      (fun child dictionary =>
        (Yulang.GeneralNominalCenteredHeadMatStepBoundary.boundary roles).Evidence plan.packet.registry state assignment
          child dictionary)
      plan.packet.children dictionaries) :
  (Yulang.GeneralNominalCenteredHeadMatStepBoundary.boundary roles).Evidence plan.packet.registry state assignment
    plan.packet.site.occurrence
    (Yulang.CommonRoleOutermostResolver.Dictionary.node plan.packet.declaration.id dictionaries)
Yulang.GeneralDictionaryMatScalarFixture200.positive_nonempty_regression :
  Yulang.GeneralDictionaryMatScalarFixture200.root.demand.outputs ≠ [] ∧
    (Yulang.GeneralNominalCenteredHeadMatStepBoundary.boundary
            Yulang.GeneralDictionaryMatScalarFixture200.roles).Initial
        Yulang.GeneralDictionaryMatScalarFixture200.registry Yulang.GeneralDictionaryMatScalarFixture200.root
        Yulang.GeneralDictionaryMatScalarFixture200.start ∧
      Yulang.GeneralNominalCenteredHeadMatStepJournal.Models Yulang.GeneralDictionaryMatScalarFixture200.start
          Yulang.GeneralDictionaryMatScalarFixture200.model ∧
        Yulang.GeneralNominalCenteredHeadMatStepPackets.Holds Yulang.GeneralDictionaryMatScalarFixture200.plan
            Yulang.GeneralDictionaryMatScalarFixture200.model ∧
          (Yulang.GeneralNominalCenteredHeadMatStepBoundary.boundary
                Yulang.GeneralDictionaryMatScalarFixture200.roles).Evidence
            Yulang.GeneralDictionaryMatScalarFixture200.registry Yulang.GeneralDictionaryMatScalarFixture200.start
            Yulang.GeneralDictionaryMatScalarFixture200.model Yulang.GeneralDictionaryMatScalarFixture200.root
            (Yulang.CommonRoleOutermostResolver.Dictionary.node 37 [])
'Yulang.GeneralDictionaryMatScalarOutputs200.scalar_schema' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryMatScalarOutputs200.requests_root' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryMatScalarOutputs200.materialization_of_total' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryMatScalarOutputs200.branch_of_total' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryMatScalarOutputs200.instance_of_total' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryMatScalarOutputs200.evidence_of_frame_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryMatScalarOutputs200.evidence_of_recorded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryMatScalarFixture200.total_holds' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryMatScalarFixture200.positive_nonempty_regression' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## final-MatScalarConflict200

```sh
lake env lean --trust=0 -DwarningAsError=true Audit/MatScalarConflict200.lean
```

Exit: 0

```text
Yulang.GeneralDictionaryMatScalarConflict200.source_not_total :
  Yulang.GeneralNominalCenteredHeadMatStepJournal.Models Yulang.GeneralDictionaryMatScalarConflict200.start
      Yulang.GeneralDictionaryMatScalarConflict200.model ∧
    Yulang.GeneralNominalCenteredHeadOutputs.Frame Yulang.GeneralDictionaryMatScalarConflict200.registry
        Yulang.GeneralDictionaryMatScalarConflict200.start.core Yulang.GeneralDictionaryMatScalarConflict200.root 37
        Yulang.GeneralDictionaryMatScalarConflict200.plan ∧
      Yulang.GeneralDictionaryMatScalarOutputs200.ScalarRequests Yulang.GeneralDictionaryMatScalarConflict200.registry
          Yulang.GeneralDictionaryMatScalarConflict200.context
          (Yulang.GeneralNominalMaterialization.rootRequests Yulang.GeneralDictionaryMatScalarConflict200.declaration
            Yulang.GeneralDictionaryMatScalarConflict200.root) ∧
        ¬Yulang.GeneralNominalCenteredHeadMatStepPackets.Holds Yulang.GeneralDictionaryMatScalarConflict200.plan
            Yulang.GeneralDictionaryMatScalarConflict200.model
'Yulang.GeneralDictionaryMatScalarConflict200.scalar_requests' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryMatScalarConflict200.no_total_holds' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryMatScalarConflict200.no_evidence' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryMatScalarConflict200.source_not_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## final-MatScalarScope200

```sh
lake env lean --trust=0 -DwarningAsError=true Audit/MatScalarScope200.lean
```

Exit: 0

```text
Yulang.GeneralNominalCenteredHeadMatStepAvailability.selected_frame {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles}
  {registry : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Registry}
  {root focus : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Demand} {key : Nat}
  {children : List (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Demand}
  (reachable :
    Yulang.B4TargetV6.Reachable (Yulang.GeneralNominalCenteredHeadMatStepBoundary.boundary roles) registry root state)
  (selected :
    Yulang.GeneralNominalCenteredHeadMatStepBoundary.Local registry state focus
      (Yulang.CommonRoleOutermostResolver.Frontier.selected key children)) :
  ∃ plan,
    Yulang.GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key plan ∧ plan.packet.children = children
Yulang.GeneralNominalCenteredHeadMatStepAvailability.selected_effect {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles} {registry : Yulang.GeneralDeclarations.Registry}
  {root focus : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Demand} {key : Nat}
  {children : List (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Demand}
  (checked : Yulang.GeneralDeclarations.Checked registry)
  (reachable :
    Yulang.B4TargetV6.Reachable (Yulang.GeneralNominalCenteredHeadMatStepBoundary.boundary roles) registry root state)
  (selected :
    Yulang.GeneralNominalCenteredHeadMatStepBoundary.Local registry state focus
      (Yulang.CommonRoleOutermostResolver.Frontier.selected key children)) :
  ∃ effect,
    effect.registry = registry ∧
      effect.snapshot = state.core ∧
        effect.plan.packet.site.occurrence = focus ∧
          effect.plan.packet.declaration.id = key ∧ effect.plan.packet.children = children
Yulang.GeneralNominalCenteredHeadMatCompletionCollision.not_selectedCompletion :
  ¬Yulang.GeneralNominalCenteredHeadMatStepCompletion.SelectedCompletion
      Yulang.GeneralNominalCenteredHeadMatCompletionCollisionSource.roles
Yulang.GeneralNominalCenteredHeadMatCompletionCollision.stable_selected_counterexample :
  (Yulang.GeneralNominalCenteredHeadMatStepBoundary.boundary
          Yulang.GeneralNominalCenteredHeadMatCompletionCollisionSource.roles).Checked
      Yulang.GeneralNominalCenteredHeadMatCompletionCollisionSource.registry ∧
    (Yulang.GeneralNominalCenteredHeadMatStepBoundary.boundary
            Yulang.GeneralNominalCenteredHeadMatCompletionCollisionSource.roles).Initial
        Yulang.GeneralNominalCenteredHeadMatCompletionCollisionSource.registry
        Yulang.GeneralNominalCenteredHeadMatCompletionCollisionSource.root
        Yulang.GeneralNominalCenteredHeadMatCompletionCollisionSource.start ∧
      Yulang.B4TargetV6.Reachable
          (Yulang.GeneralNominalCenteredHeadMatStepBoundary.boundary
            Yulang.GeneralNominalCenteredHeadMatCompletionCollisionSource.roles)
          Yulang.GeneralNominalCenteredHeadMatCompletionCollisionSource.registry
          Yulang.GeneralNominalCenteredHeadMatCompletionCollisionSource.root
          Yulang.GeneralNominalCenteredHeadMatCompletionCollisionSource.start ∧
        Yulang.GeneralNominalCenteredHeadMatStepKernel.Stable
            Yulang.GeneralNominalCenteredHeadMatCompletionCollisionSource.registry
            Yulang.GeneralNominalCenteredHeadMatCompletionCollisionSource.start
            Yulang.GeneralNominalCenteredHeadMatCompletionCollisionSource.root ∧
          Yulang.GeneralNominalCenteredHeadMatStepBoundary.Local
              Yulang.GeneralNominalCenteredHeadMatCompletionCollisionSource.registry
              Yulang.GeneralNominalCenteredHeadMatCompletionCollisionSource.start
              Yulang.GeneralNominalCenteredHeadMatCompletionCollisionSource.root
              (Yulang.CommonRoleOutermostResolver.Frontier.selected 37
                Yulang.GeneralNominalCenteredHeadMatCompletionCollisionSource.children) ∧
            Yulang.GeneralNominalCenteredHeadMatCompletionCollisionSource.children.length = 2 ∧
              (∃ assignment,
                  Yulang.GeneralNominalCenteredHeadMatStepJournal.Models
                      Yulang.GeneralNominalCenteredHeadMatCompletionCollisionSource.start assignment ∧
                    Yulang.GeneralNominalCenteredHeadMatCompletionCollisionLocal.effect.Holds assignment) ∧
                (∃ assignment,
                    Yulang.GeneralNominalCenteredHeadMatStepJournal.Models
                        Yulang.GeneralNominalCenteredHeadMatCompletionCollisionSource.start assignment ∧
                      Yulang.GeneralNominalCenteredHeadMatStepLocal.ChosenHead
                        Yulang.GeneralNominalCenteredHeadMatCompletionCollisionSource.registry
                        Yulang.GeneralNominalCenteredHeadMatCompletionCollisionSource.start
                        Yulang.GeneralNominalCenteredHeadMatCompletionCollisionSource.root 37 assignment) ∧
                  ¬Yulang.GeneralNominalCenteredHeadMatStepLocal.OutputConflict
                        Yulang.GeneralNominalCenteredHeadMatCompletionCollisionSource.registry
                        Yulang.GeneralNominalCenteredHeadMatCompletionCollisionSource.start
                        Yulang.GeneralNominalCenteredHeadMatCompletionCollisionSource.root 37 ∧
                    Yulang.GeneralNominalCycleSteps.ChoiceCompatible
                        Yulang.GeneralNominalCenteredHeadMatCompletionCollisionSource.start.core.erased.current
                        Yulang.GeneralNominalCenteredHeadMatCompletionCollisionLocal.effect.plan.packet ∧
                      (∀
                          (candidate :
                            Yulang.GeneralNominalCenteredHeadMatStepJournal.Effect
                              Yulang.GeneralNominalCenteredHeadMatCompletionCollisionSource.roles),
                          candidate.plan.packet.site.occurrence =
                              Yulang.GeneralNominalCenteredHeadMatCompletionCollisionSource.root →
                            ¬Yulang.GeneralNominalCenteredHeadMatStepKernel.Installable
                                Yulang.GeneralNominalCenteredHeadMatCompletionCollisionSource.registry
                                Yulang.GeneralNominalCenteredHeadMatCompletionCollisionSource.start candidate) ∧
                        ∀
                          (child :
                            Yulang.GeneralSourceDictionaries.Occurrence
                              Yulang.GeneralNominalCenteredHeadMatCompletionCollisionSource.roles),
                          child ∈ Yulang.GeneralNominalCenteredHeadMatCompletionCollisionSource.children →
                            ¬Yulang.GeneralNominalSaturationState.Generated
                                Yulang.GeneralNominalCenteredHeadMatCompletionCollisionSource.start.core.erased.current
                                Yulang.GeneralNominalCenteredHeadMatCompletionCollisionSource.root child
```

## final-MatStableScalar200

```sh
lake env lean --trust=0 -DwarningAsError=true Audit/MatStableScalar200.lean
```

Exit: 0

```text
Yulang.GeneralDictionaryMatStableScalar200.evidence_of_stable_extension {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {state : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles}
  {root : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Demand}
  {children : List (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Demand}
  (effect : Yulang.GeneralNominalCenteredHeadMatStepJournal.Effect roles)
  (reachable :
    Yulang.B4TargetV6.Reachable (Yulang.GeneralNominalCenteredHeadMatStepBoundary.boundary roles) registry root state)
  (stable : Yulang.GeneralNominalCenteredHeadMatStepKernel.Stable registry state effect.plan.packet.site.occurrence)
  (selected :
    Yulang.GeneralNominalCenteredHeadMatStepBoundary.Local registry state effect.plan.packet.site.occurrence
      (Yulang.CommonRoleOutermostResolver.Frontier.selected effect.plan.packet.declaration.id children))
  (registryEq : effect.registry = registry) (snapshot : effect.snapshot = state.core)
  (extension : Yulang.GeneralNominalCenteredHeadMatStepAvailability.Extension state effect)
  (variables : Yulang.GeneralDictionaryVariableRequirements.VariableClauses effect.plan.packet.declaration)
  (defined :
    Yulang.GeneralNominalMaterialization.RootDefined effect.plan.packet.declaration effect.plan.packet.site.occurrence)
  (scalars :
    Yulang.GeneralDictionaryMatScalarOutputs200.ScalarRequests effect.plan.packet.registry effect.plan.packet.context
      (Yulang.GeneralNominalMaterialization.rootRequests effect.plan.packet.declaration
        effect.plan.packet.site.occurrence))
  (assignment : Yulang.GeneralNominalCommonBridge.Assignment)
  (models : Yulang.GeneralNominalCenteredHeadMatStepJournal.Models state assignment)
  (dictionaries : List Yulang.CommonRoleOutermostResolver.Dictionary)
  (childEvidence :
    Yulang.CommonRoleOutermostResolver.All₂
      (fun child dictionary =>
        (Yulang.GeneralNominalCenteredHeadMatStepBoundary.boundary roles).Evidence registry state assignment child
          dictionary)
      effect.plan.packet.children dictionaries) :
  (Yulang.GeneralNominalCenteredHeadMatStepBoundary.boundary roles).Evidence registry state assignment
    effect.plan.packet.site.occurrence
    (Yulang.CommonRoleOutermostResolver.Dictionary.node effect.plan.packet.declaration.id dictionaries)
Yulang.GeneralDictionaryMatStableScalar200.evidence_of_common_model {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {state : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles}
  {root : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Demand}
  {children : List (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Demand}
  (effect : Yulang.GeneralNominalCenteredHeadMatStepJournal.Effect roles)
  (checked : Yulang.GeneralDeclarations.Checked registry)
  (reachable :
    Yulang.B4TargetV6.Reachable (Yulang.GeneralNominalCenteredHeadMatStepBoundary.boundary roles) registry root state)
  (stable : Yulang.GeneralNominalCenteredHeadMatStepKernel.Stable registry state effect.plan.packet.site.occurrence)
  (selected :
    Yulang.GeneralNominalCenteredHeadMatStepBoundary.Local registry state effect.plan.packet.site.occurrence
      (Yulang.CommonRoleOutermostResolver.Frontier.selected effect.plan.packet.declaration.id children))
  (registryEq : effect.registry = registry) (snapshot : effect.snapshot = state.core)
  (choice : Yulang.GeneralNominalCycleSteps.ChoiceCompatible state.core.erased.current effect.plan.packet)
  (common :
    ∃ model,
      Yulang.GeneralNominalCenteredHeadMatStepJournal.Models state model ∧
        Yulang.GeneralNominalCenteredHeadMatStepPackets.Holds effect.plan model ∧ effect.Holds model)
  (variables : Yulang.GeneralDictionaryVariableRequirements.VariableClauses effect.plan.packet.declaration)
  (defined :
    Yulang.GeneralNominalMaterialization.RootDefined effect.plan.packet.declaration effect.plan.packet.site.occurrence)
  (scalars :
    Yulang.GeneralDictionaryMatScalarOutputs200.ScalarRequests effect.plan.packet.registry effect.plan.packet.context
      (Yulang.GeneralNominalMaterialization.rootRequests effect.plan.packet.declaration
        effect.plan.packet.site.occurrence))
  (assignment : Yulang.GeneralNominalCommonBridge.Assignment)
  (models : Yulang.GeneralNominalCenteredHeadMatStepJournal.Models state assignment)
  (dictionaries : List Yulang.CommonRoleOutermostResolver.Dictionary)
  (childEvidence :
    Yulang.CommonRoleOutermostResolver.All₂
      (fun child dictionary =>
        (Yulang.GeneralNominalCenteredHeadMatStepBoundary.boundary roles).Evidence registry state assignment child
          dictionary)
      effect.plan.packet.children dictionaries) :
  (Yulang.GeneralNominalCenteredHeadMatStepBoundary.boundary roles).Evidence registry state assignment
    effect.plan.packet.site.occurrence
    (Yulang.CommonRoleOutermostResolver.Dictionary.node effect.plan.packet.declaration.id dictionaries)
'Yulang.GeneralDictionaryMatStableScalar200.evidence_of_stable_extension' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryMatStableScalar200.evidence_of_common_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## final-MatSelectedScalar200

```sh
lake env lean --trust=0 -DwarningAsError=true Audit/MatSelectedScalar200.lean
```

Exit: 0

```text
Yulang.GeneralDictionaryMatSelectedScalar200.evidence_of_selected_common_model {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {state : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles}
  {root : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Demand}
  {children : List (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Demand}
  (effect : Yulang.GeneralNominalCenteredHeadMatStepJournal.Effect roles)
  (checked : Yulang.GeneralDeclarations.Checked registry)
  (reachable :
    Yulang.B4TargetV6.Reachable (Yulang.GeneralNominalCenteredHeadMatStepBoundary.boundary roles) registry root state)
  (stable : Yulang.GeneralNominalCenteredHeadMatStepKernel.Stable registry state effect.plan.packet.site.occurrence)
  (selected :
    Yulang.GeneralNominalCenteredHeadMatStepBoundary.Local registry state effect.plan.packet.site.occurrence
      (Yulang.CommonRoleOutermostResolver.Frontier.selected effect.plan.packet.declaration.id children))
  (registryEq : effect.registry = registry) (snapshot : effect.snapshot = state.core)
  (choice : Yulang.GeneralNominalCycleSteps.ChoiceCompatible state.core.erased.current effect.plan.packet)
  (common :
    ∃ model,
      Yulang.GeneralNominalCenteredHeadMatStepJournal.Models state model ∧
        Yulang.GeneralNominalCenteredHeadMatStepPackets.Holds effect.plan model ∧ effect.Holds model)
  (variables : Yulang.GeneralDictionaryVariableRequirements.VariableClauses effect.plan.packet.declaration)
  (defined :
    Yulang.GeneralNominalMaterialization.RootDefined effect.plan.packet.declaration effect.plan.packet.site.occurrence)
  (scalars :
    Yulang.GeneralDictionaryMatScalarOutputs200.ScalarRequests effect.plan.packet.registry effect.plan.packet.context
      (Yulang.GeneralNominalMaterialization.rootRequests effect.plan.packet.declaration
        effect.plan.packet.site.occurrence))
  (assignment : Yulang.GeneralNominalCommonBridge.Assignment)
  (models : Yulang.GeneralNominalCenteredHeadMatStepJournal.Models state assignment)
  (dictionaries : List Yulang.CommonRoleOutermostResolver.Dictionary)
  (childEvidence :
    Yulang.CommonRoleOutermostResolver.All₂
      (fun child dictionary =>
        (Yulang.GeneralNominalCenteredHeadMatStepBoundary.boundary roles).Evidence registry state assignment child
          dictionary)
      children dictionaries) :
  (Yulang.GeneralNominalCenteredHeadMatStepBoundary.boundary roles).Evidence registry state assignment
    effect.plan.packet.site.occurrence
    (Yulang.CommonRoleOutermostResolver.Dictionary.node effect.plan.packet.declaration.id dictionaries)
'Yulang.GeneralDictionaryMatSelectedScalar200.selected_children' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryMatSelectedScalar200.evidence_of_selected_common_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## terminal-audit

```sh
lake env lean --trust=0 -DwarningAsError=true Audit/MatTerminalAssembly200.lean
```

Exit: 0

```text
Yulang.GeneralDictionaryMatTerminalAssembly200.holds_of_head_class {roles : Yulang.Roles.RoleDecls}
  (plan : Yulang.GeneralNominalCenters.Plan roles) (state : Yulang.GeneralNominalCenteredSteps.State roles)
  (recorded : plan.packet.site ∈ state.erased.current.sites) (assignment : Yulang.GeneralNominalCommonBridge.Assignment)
  (headModels :
    Yulang.GeneralNominalCenteredHeadCandidates.HeadModels plan.packet.registry plan.packet.context
      plan.packet.site.occurrence plan.packet.declaration plan.packet.bounds assignment)
  (headEquations : Yulang.GeneralNominalCenteredHeadOutputs.HeadEquations plan assignment)
  (effects : Yulang.GeneralNominalCenteredHeadMatEffects.ClassEffects state plan.packet.site.occurrence plan assignment)
  (terminal : plan.packet.declaration.requirements = []) :
  Yulang.GeneralNominalCenteredHeadMatStepPackets.Holds plan assignment
Yulang.GeneralDictionaryMatTerminalAssembly200.evidence_of_terminal_common_head {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry}
  {root : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Demand}
  {children : List (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Demand}
  (effect : Yulang.GeneralNominalCenteredHeadMatStepJournal.Effect roles)
  (state : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles)
  (checked : Yulang.GeneralDeclarations.Checked registry)
  (reachable :
    Yulang.B4TargetV6.Reachable (Yulang.GeneralNominalCenteredHeadMatStepBoundary.boundary roles) registry root state)
  (stable : Yulang.GeneralNominalCenteredHeadMatStepKernel.Stable registry state effect.plan.packet.site.occurrence)
  (selected :
    Yulang.GeneralNominalCenteredHeadMatStepBoundary.Local registry state effect.plan.packet.site.occurrence
      (Yulang.CommonRoleOutermostResolver.Frontier.selected effect.plan.packet.declaration.id children))
  (registryEq : effect.registry = registry) (snapshot : effect.snapshot = state.core)
  (choice : Yulang.GeneralNominalCycleSteps.ChoiceCompatible state.core.erased.current effect.plan.packet)
  (common :
    ∃ model,
      Yulang.GeneralNominalCenteredHeadMatStepJournal.Models state model ∧
        Yulang.GeneralNominalCenteredHeadCandidates.HeadModels effect.plan.packet.registry effect.plan.packet.context
            effect.plan.packet.site.occurrence effect.plan.packet.declaration effect.plan.packet.bounds model ∧
          effect.Holds model)
  (terminal : effect.plan.packet.declaration.requirements = [])
  (defined :
    Yulang.GeneralNominalMaterialization.RootDefined effect.plan.packet.declaration effect.plan.packet.site.occurrence)
  (scalars :
    Yulang.GeneralDictionaryMatScalarOutputs200.ScalarRequests effect.plan.packet.registry effect.plan.packet.context
      (Yulang.GeneralNominalMaterialization.rootRequests effect.plan.packet.declaration
        effect.plan.packet.site.occurrence))
  (assignment : Yulang.GeneralNominalCommonBridge.Assignment)
  (models : Yulang.GeneralNominalCenteredHeadMatStepJournal.Models state assignment) :
  (Yulang.GeneralNominalCenteredHeadMatStepBoundary.boundary roles).Evidence registry state assignment
    effect.plan.packet.site.occurrence
    (Yulang.CommonRoleOutermostResolver.Dictionary.node effect.plan.packet.declaration.id [])
'Yulang.GeneralDictionaryMatTerminalAssembly200.generated_holds' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryMatTerminalAssembly200.terminal_requests' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryMatTerminalAssembly200.outputs_of_class' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryMatTerminalAssembly200.holds_of_head_class' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryMatTerminalAssembly200.evidence_of_terminal_common_head' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## all-module-gate

```sh
lake env lean --trust=0 -DwarningAsError=true <CompleteGate.lean>
```

Exit: 0

```text
AXIOM-GATE-PASS: 110 declarations
```

## diff-check

```sh
git diff --check
```

Exit: 0

```text
```

## final-source-readback

```sh
git diff --exit-code origin/work/dots-main 9970c1a7b -- . :!notes/heartbeat/dots-main.md
```

Exit: 0

```text
```

## All-new-module gate source

The gate is a read-only declaration dependency inspection, not a proof shortcut.

```lean
import Yulang.GeneralDictionaryMatScalarOutputs200
import Yulang.GeneralDictionaryMatScalarFixture200
import Yulang.GeneralDictionaryMatScalarConflict200
import Yulang.GeneralDictionaryMatStableScalar200
import Yulang.GeneralDictionaryMatSelectedScalar200
import Yulang.GeneralDictionaryMatTerminalAssembly200
import Lean
open Lean Elab Command in
run_cmd do
  let e ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules := #[`Yulang.GeneralDictionaryMatScalarOutputs200,`Yulang.GeneralDictionaryMatScalarFixture200,`Yulang.GeneralDictionaryMatScalarConflict200,`Yulang.GeneralDictionaryMatStableScalar200,`Yulang.GeneralDictionaryMatSelectedScalar200,`Yulang.GeneralDictionaryMatTerminalAssembly200]
  let mut count : Nat := 0
  for (n, _) in e.constants.toList do
    if let some i := e.getModuleIdxFor? n then
      if modules.contains e.header.moduleNames[i.toNat]! then
        count := count + 1
        for a in ← collectAxioms n do
          unless allowed.contains a do throwError "bad axiom {n}: {a}"
  if count == 0 then throwError "empty audit"
  logInfo m!"AXIOM-GATE-PASS: {count} declarations"
```

## Corrected command failures

An initial invocation of the wrapper without `bash` exited126 (not executable). It was rerun through `bash`. One mistaken audit filename exited1; the actual `Audit/MatScalarOutputs200.lean` was then checked successfully, including the final rerun above. No final proof/test failure remains.

```text
no such file or directory (error code: 2)
  file: Audit/Cycle200ScalarOutputs.lean
```
