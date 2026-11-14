# Cycle174 exact public types

```text
@Yulang.GeneralDictionaryAgreedComposition174.Remaining : {roles : Yulang.Roles.RoleDecls} →
  Bool → Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles → Prop
@Yulang.GeneralDictionaryAgreedComposition174.policy_at : ∀ {roles : Yulang.Roles.RoleDecls} {defer : Bool}
  {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles},
  Yulang.GeneralDictionaryAgreedComposition174.Remaining defer gap →
    ∀ (registry : Yulang.GeneralDeclarations.Registry),
      (Yulang.GeneralNominalActualAgreedBoundary.boundary defer gap).Checked registry →
        ∀ (state : Yulang.GeneralNominalSupport.Tracked roles)
          (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
          Yulang.B4TargetV5.Reachable (Yulang.GeneralNominalActualAgreedBoundary.boundary defer gap) registry root
              state →
            ∀ (focus : Yulang.GeneralSourceDictionaries.Occurrence roles), defer = true ∨ ¬gap registry state focus
@Yulang.GeneralDictionaryAgreedComposition174.evidenceNode : ∀ {roles : Yulang.Roles.RoleDecls} {defer : Bool}
  {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles},
  Yulang.GeneralDictionaryAgreedComposition174.Remaining defer gap →
    Yulang.B4SkeletonV5.EvidenceNode (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap)
@Yulang.GeneralDictionaryAgreedComposition174.generatedChildren : ∀ {roles : Yulang.Roles.RoleDecls} {defer : Bool}
  {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles},
  Yulang.GeneralDictionaryAgreedComposition174.Remaining defer gap →
    Yulang.B4SkeletonV5.GeneratedChildren (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap)
@Yulang.GeneralDictionaryAgreedComposition174.generatedChildren_pending : ∀ {roles : Yulang.Roles.RoleDecls}
  {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles},
  Yulang.B4SkeletonV5.GeneratedChildren (Yulang.GeneralDictionaryAgreedGround174.boundary true gap)
@Yulang.GeneralDictionaryAgreedComposition174.bridges : ∀ {roles : Yulang.Roles.RoleDecls} (defer : Bool)
  (gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles),
  Yulang.GeneralDictionaryAgreedComposition174.Remaining defer gap →
    Yulang.B4SkeletonV5.B4Bridges (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap)
      (Yulang.GeneralDictionaryAgreedGround174.executor defer gap)
      (Yulang.GeneralNominalActualAgreedBoundary.frontiers defer gap)
@Yulang.GeneralDictionaryAgreedComposition174.statement : ∀ {roles : Yulang.Roles.RoleDecls} (defer : Bool)
  (gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles),
  Yulang.GeneralDictionaryAgreedComposition174.Remaining defer gap →
    Yulang.B4TargetV5.Statement (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap)
      (Yulang.GeneralDictionaryAgreedGround174.executor defer gap)
Yulang.GeneralDictionaryAgreedEdge174.RoleStratified : Yulang.GeneralDeclarations.Registry → (Nat → Nat) → Prop
@Yulang.GeneralDictionaryAgreedEdge174.selected_child_role : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {state : Yulang.GeneralNominalSupport.Tracked roles} {defer : Bool}
  {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles}
  {parent : (Yulang.GeneralNominalActualAgreedLocal.vocabulary roles).Demand} {key : Nat}
  {children : List (Yulang.GeneralNominalActualAgreedLocal.vocabulary roles).Demand}
  {child : (Yulang.GeneralNominalActualAgreedLocal.vocabulary roles).Demand},
  Yulang.GeneralNominalActualAgreedLocal.Local defer gap registry state parent
      (Yulang.CommonRoleOutermostResolver.Frontier.selected key children) →
    child ∈ children →
      ∃ declaration,
        declaration ∈ registry.declarations ∧
          ∃ clause,
            clause ∈ declaration.requirements ∧ declaration.role = parent.demand.role ∧ clause.role = child.demand.role
@Yulang.GeneralDictionaryAgreedEdge174.child_role_decreases : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {state : Yulang.GeneralNominalSupport.Tracked roles} {defer : Bool}
  {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles} {rank : Nat → Nat}
  {child parent : (Yulang.GeneralNominalActualAgreedLocal.vocabulary roles).Demand},
  Yulang.GeneralDictionaryAgreedEdge174.RoleStratified registry rank →
    Yulang.CommonRoleOutermostResolver.Child (Yulang.GeneralNominalActualAgreedLocal.Local defer gap registry state)
        child parent →
      rank child.demand.role < rank parent.demand.role
@Yulang.GeneralDictionaryAgreedEdge174.whereAccessible : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {state : Yulang.GeneralNominalSupport.Tracked roles} {defer : Bool}
  {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles} {rank : Nat → Nat},
  Yulang.GeneralDictionaryAgreedEdge174.RoleStratified registry rank →
    ∀ (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
      Acc
        (Yulang.CommonRoleOutermostResolver.Child
          (Yulang.GeneralNominalActualAgreedLocal.Local defer gap registry state))
        root
@Yulang.GeneralDictionaryAgreedEdge174.boundary_whereAccessible : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {state : Yulang.GeneralNominalSupport.Tracked roles} {defer : Bool}
  {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles} {rank : Nat → Nat},
  Yulang.GeneralDictionaryAgreedEdge174.RoleStratified registry rank →
    ∀ (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
      Acc
        (Yulang.CommonRoleOutermostResolver.Child
          (Yulang.B4TargetV3.Local (Yulang.GeneralNominalActualAgreedBoundary.boundary defer gap).toSourceBoundary
            registry state))
        root
@Yulang.GeneralDictionaryAgreedEdge174.leaves_stratified : ∀ {registry : Yulang.GeneralDeclarations.Registry},
  (∀ (declaration : Yulang.GeneralDeclarations.Declaration),
      declaration ∈ registry.declarations → declaration.requirements = []) →
    Yulang.GeneralDictionaryAgreedEdge174.RoleStratified registry fun x => 0
@Yulang.GeneralDictionaryAgreedEdge174.leaf_whereAccessible : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {state : Yulang.GeneralNominalSupport.Tracked roles} {defer : Bool}
  {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles},
  (∀ (declaration : Yulang.GeneralDeclarations.Declaration),
      declaration ∈ registry.declarations → declaration.requirements = []) →
    ∀ (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
      Acc
        (Yulang.CommonRoleOutermostResolver.Child
          (Yulang.B4TargetV3.Local (Yulang.GeneralNominalActualAgreedBoundary.boundary defer gap).toSourceBoundary
            registry state))
        root
@Yulang.GeneralDictionaryAgreedEdge174.stratified_reorders : ∀ {registry other : Yulang.GeneralDeclarations.Registry}
  {rank : Nat → Nat},
  Yulang.GeneralRegistryReordering.Reorders registry other →
    Yulang.GeneralDictionaryAgreedEdge174.RoleStratified registry rank →
      Yulang.GeneralDictionaryAgreedEdge174.RoleStratified other rank
@Yulang.GeneralDictionaryAgreedEdge174.Descent : {roles : Yulang.Roles.RoleDecls} →
  Bool →
    Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles →
      Yulang.GeneralDeclarations.Registry →
        Yulang.GeneralNominalSupport.Tracked roles →
          Yulang.GeneralSourceDictionaries.Occurrence roles →
            Nat → Yulang.GeneralSourceDictionaries.Occurrence roles → Prop
@Yulang.GeneralDictionaryAgreedEdge174.descent_bounded : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {state : Yulang.GeneralNominalSupport.Tracked roles} {defer : Bool}
  {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles} {rank : Nat → Nat}
  {root : Yulang.GeneralSourceDictionaries.Occurrence roles} {depth : Nat}
  {child : Yulang.GeneralSourceDictionaries.Occurrence roles},
  Yulang.GeneralDictionaryAgreedEdge174.RoleStratified registry rank →
    Yulang.GeneralDictionaryAgreedEdge174.Descent defer gap registry state root depth child →
      depth + rank child.demand.role ≤ rank root.demand.role
@Yulang.GeneralDictionaryAgreedEvidence174.RecordedExtensions : {roles : Yulang.Roles.RoleDecls} →
  Yulang.GeneralNominalSupport.Tracked roles → Prop
@Yulang.GeneralDictionaryAgreedEvidence174.selected_instance : ∀ {roles : Yulang.Roles.RoleDecls} {defer : Bool}
  {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles} {registry : Yulang.GeneralDeclarations.Registry}
  {state : Yulang.GeneralNominalSupport.Tracked roles} {root focus : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {key : Nat} {children : List (Yulang.GeneralNominalActualAgreedLocal.vocabulary roles).Demand},
  Yulang.GeneralNominalActualInspectionSteps.SourceFormed registry root state →
    Yulang.GeneralDictionaryAgreedEvidence174.RecordedExtensions state →
      defer = true ∨ ¬gap registry state focus →
        (Yulang.GeneralNominalActualAgreedBoundary.boundary defer gap).Stable registry state focus →
          Yulang.GeneralNominalActualAgreedLocal.Local defer gap registry state focus
              (Yulang.CommonRoleOutermostResolver.Frontier.selected key children) →
            ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
              Yulang.GeneralNominalSaturationState.Models state.current model →
                Yulang.GeneralDictionaryRecursiveEvidence.Instance registry state.current.context model focus key
                  children
@Yulang.GeneralDictionaryAgreedEvidence174.selected_evidence : ∀ {roles : Yulang.Roles.RoleDecls} {defer : Bool}
  {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles} {registry : Yulang.GeneralDeclarations.Registry}
  {state : Yulang.GeneralNominalSupport.Tracked roles} {root focus : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {key : Nat} {children : List (Yulang.GeneralNominalActualAgreedLocal.vocabulary roles).Demand},
  Yulang.GeneralNominalActualInspectionSteps.SourceFormed registry root state →
    Yulang.GeneralDictionaryAgreedEvidence174.RecordedExtensions state →
      defer = true ∨ ¬gap registry state focus →
        (Yulang.GeneralNominalActualAgreedBoundary.boundary defer gap).Stable registry state focus →
          Yulang.GeneralNominalActualAgreedLocal.Local defer gap registry state focus
              (Yulang.CommonRoleOutermostResolver.Frontier.selected key children) →
            ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
              Yulang.GeneralNominalSaturationState.Models state.current model →
                ∀ (dictionaries : List Yulang.GeneralDictionaryReadback.Payload),
                  Yulang.CommonRoleOutermostResolver.All₂
                      (Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context model) children
                      dictionaries →
                    Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context model focus
                      (Yulang.CommonRoleOutermostResolver.Dictionary.node key dictionaries)
@Yulang.GeneralDictionaryAgreedEvidence174.ReachableRecordedExtensions : {roles : Yulang.Roles.RoleDecls} →
  Bool → Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles → Prop
@Yulang.GeneralDictionaryAgreedEvidence174.evidenceNode_of_policy : ∀ {roles : Yulang.Roles.RoleDecls} {defer : Bool}
  {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles},
  Yulang.GeneralDictionaryAgreedEvidence174.ReachableRecordedExtensions defer gap →
    (∀ (registry : (Yulang.GeneralNominalActualAgreedBoundary.vocabulary roles).Registry),
        (Yulang.GeneralNominalActualAgreedBoundary.boundary defer gap).Checked registry →
          ∀ (state : (Yulang.GeneralNominalActualAgreedBoundary.vocabulary roles).State)
            (root : (Yulang.GeneralNominalActualAgreedBoundary.vocabulary roles).Demand),
            Yulang.B4TargetV5.Reachable (Yulang.GeneralNominalActualAgreedBoundary.boundary defer gap) registry root
                state →
              ∀ (demand : Yulang.GeneralSourceDictionaries.Occurrence roles),
                defer = true ∨ ¬gap registry state demand) →
      Yulang.B4SkeletonV5.EvidenceNode (Yulang.GeneralNominalActualAgreedBoundary.boundary defer gap)
@Yulang.GeneralDictionaryAgreedEvidence174.evidenceNode_pending : ∀ {roles : Yulang.Roles.RoleDecls}
  {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles},
  Yulang.GeneralDictionaryAgreedEvidence174.ReachableRecordedExtensions true gap →
    Yulang.B4SkeletonV5.EvidenceNode (Yulang.GeneralNominalActualAgreedBoundary.boundary true gap)
@Yulang.GeneralDictionaryAgreedEvidence174.evidenceNode_complete : ∀ {roles : Yulang.Roles.RoleDecls}
  {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles},
  Yulang.GeneralDictionaryAgreedEvidence174.ReachableRecordedExtensions false gap →
    Yulang.GeneralNominalActualAgreedBoundary.GapFree gap →
      Yulang.B4SkeletonV5.EvidenceNode (Yulang.GeneralNominalActualAgreedBoundary.boundary false gap)
@Yulang.GeneralDictionaryAgreedEvidence174.OrdinaryAt : {roles : Yulang.Roles.RoleDecls} →
  Yulang.GeneralDeclarations.Registry →
    Yulang.GeneralNominalSupport.Tracked roles →
      Yulang.GeneralSourceDictionaries.Occurrence roles → Yulang.GeneralNominalSupport.Tracked roles → Prop
@Yulang.GeneralDictionaryAgreedEvidence174.OrdinaryStep : {roles : Yulang.Roles.RoleDecls} →
  Yulang.GeneralDeclarations.Registry →
    Yulang.GeneralSourceDictionaries.Occurrence roles →
      Yulang.GeneralNominalSupport.Tracked roles → Yulang.GeneralNominalSupport.Tracked roles → Prop
@Yulang.GeneralDictionaryAgreedEvidence174.ordinary_at_actual : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {focus : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {before after : Yulang.GeneralNominalSupport.Tracked roles},
  Yulang.GeneralDictionaryAgreedEvidence174.OrdinaryAt registry before focus after →
    Yulang.GeneralNominalActualInspectionSteps.At registry before focus after
@Yulang.GeneralDictionaryAgreedEvidence174.ordinary_step_actual : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {before after : Yulang.GeneralNominalSupport.Tracked roles},
  Yulang.GeneralDictionaryAgreedEvidence174.OrdinaryStep registry root before after →
    Yulang.GeneralNominalActualInspectionSteps.Step registry root before after
@Yulang.GeneralDictionaryAgreedEvidence174.ordinary_at_extension : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {focus : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {before after : Yulang.GeneralNominalSupport.Tracked roles},
  Yulang.GeneralDictionaryAgreedEvidence174.OrdinaryAt registry before focus after →
    Yulang.GeneralDictionaryOrdinaryTrace.Extension before.current.context after.current.context
@Yulang.GeneralDictionaryAgreedEvidence174.ordinary_steps_actual : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {before after : Yulang.GeneralNominalSupport.Tracked roles},
  Yulang.B4Target.Steps (Yulang.GeneralDictionaryAgreedEvidence174.OrdinaryStep registry root) before after →
    Yulang.B4Target.Steps (Yulang.GeneralNominalActualInspectionSteps.Step registry root) before after
@Yulang.GeneralDictionaryAgreedEvidence174.ordinary_packets_extension : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {before after : Yulang.GeneralNominalSupport.Tracked roles},
  Yulang.GeneralDictionaryAgreedEvidence174.RecordedExtensions before →
    Yulang.B4Target.Steps (Yulang.GeneralDictionaryAgreedEvidence174.OrdinaryStep registry root) before after →
      Yulang.GeneralDictionaryAgreedEvidence174.RecordedExtensions after
@Yulang.GeneralDictionaryAgreedEvidence174.ordinary_initial_extensions : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {state : Yulang.GeneralNominalSupport.Tracked roles}
  {root : Yulang.GeneralSourceDictionaries.Occurrence roles} (context : Yulang.GeneralNominalCandidates.Context),
  Yulang.B4Target.Steps (Yulang.GeneralDictionaryAgreedEvidence174.OrdinaryStep registry root)
      (Yulang.GeneralNominalSupport.initial context root) state →
    Yulang.GeneralDictionaryAgreedEvidence174.RecordedExtensions state
@Yulang.GeneralDictionaryAgreedEvidence174.ordinary_initial_formed : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {state : Yulang.GeneralNominalSupport.Tracked roles}
  {root : Yulang.GeneralSourceDictionaries.Occurrence roles} (context : Yulang.GeneralNominalCandidates.Context),
  Yulang.GeneralNominalSourceFormation.InitialSource registry context root →
    Yulang.B4Target.Steps (Yulang.GeneralDictionaryAgreedEvidence174.OrdinaryStep registry root)
        (Yulang.GeneralNominalSupport.initial context root) state →
      Yulang.GeneralNominalActualInspectionSteps.SourceFormed registry root state
@Yulang.GeneralDictionaryAgreedEvidence174.ordinary_initial_selected_evidence : ∀ {roles : Yulang.Roles.RoleDecls}
  {defer : Bool} {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles}
  {registry : Yulang.GeneralDeclarations.Registry} {state : Yulang.GeneralNominalSupport.Tracked roles}
  {root focus : Yulang.GeneralSourceDictionaries.Occurrence roles} {key : Nat}
  {children : List (Yulang.GeneralNominalActualAgreedLocal.vocabulary roles).Demand}
  (context : Yulang.GeneralNominalCandidates.Context),
  Yulang.GeneralNominalSourceFormation.InitialSource registry context root →
    Yulang.B4Target.Steps (Yulang.GeneralDictionaryAgreedEvidence174.OrdinaryStep registry root)
        (Yulang.GeneralNominalSupport.initial context root) state →
      defer = true ∨ ¬gap registry state focus →
        (Yulang.GeneralNominalActualAgreedBoundary.boundary defer gap).Stable registry state focus →
          Yulang.GeneralNominalActualAgreedLocal.Local defer gap registry state focus
              (Yulang.CommonRoleOutermostResolver.Frontier.selected key children) →
            ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
              Yulang.GeneralNominalSaturationState.Models state.current model →
                ∀ (dictionaries : List Yulang.GeneralDictionaryReadback.Payload),
                  Yulang.CommonRoleOutermostResolver.All₂
                      (Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context model) children
                      dictionaries →
                    Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context model focus
                      (Yulang.CommonRoleOutermostResolver.Dictionary.node key dictionaries)
@Yulang.GeneralDictionaryAgreedEvidence174.selected_child_generated : ∀ {roles : Yulang.Roles.RoleDecls} {defer : Bool}
  {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles} {registry : Yulang.GeneralDeclarations.Registry}
  {state : Yulang.GeneralNominalSupport.Tracked roles} {root focus : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {key : Nat} {children : List (Yulang.GeneralNominalActualAgreedBoundary.vocabulary roles).Demand}
  {child : (Yulang.GeneralNominalActualAgreedBoundary.vocabulary roles).Demand},
  defer = true ∨ ¬gap registry state focus →
    (Yulang.GeneralNominalActualAgreedBoundary.boundary defer gap).Stable registry state focus →
      Yulang.B4TargetV3.Local (Yulang.GeneralNominalActualAgreedBoundary.boundary defer gap).toSourceBoundary registry
          state focus (Yulang.CommonRoleOutermostResolver.Frontier.selected key children) →
        focus = root ∨ Yulang.GeneralNominalSaturationState.Generated state.current root focus →
          child ∈ children → Yulang.GeneralNominalSaturationState.Generated state.current root child
@Yulang.GeneralDictionaryAgreedEvidence174.dictionary_evidence_snapshot : ∀ {roles : Yulang.Roles.RoleDecls}
  {defer : Bool} {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles}
  {registry : Yulang.GeneralDeclarations.Registry} {state : Yulang.GeneralNominalSupport.Tracked roles}
  {root : Yulang.GeneralSourceDictionaries.Occurrence roles},
  Yulang.GeneralNominalActualInspectionSteps.SourceFormed registry root state →
    Yulang.GeneralDictionaryAgreedEvidence174.RecordedExtensions state →
      (∀ (demand : Yulang.GeneralSourceDictionaries.Occurrence roles), defer = true ∨ ¬gap registry state demand) →
        (Yulang.GeneralNominalActualAgreedBoundary.boundary defer gap).Stable registry state root →
          (∀ (demand : Yulang.GeneralSourceDictionaries.Occurrence roles),
              Yulang.GeneralNominalSaturationState.Generated state.current root demand →
                (Yulang.GeneralNominalActualAgreedBoundary.boundary defer gap).Stable registry state demand) →
            ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
              Yulang.GeneralNominalSaturationState.Models state.current model →
                ∀ (dictionary : Yulang.GeneralDictionaryReadback.Payload)
                  (focus : Yulang.GeneralSourceDictionaries.Occurrence roles),
                  focus = root ∨ Yulang.GeneralNominalSaturationState.Generated state.current root focus →
                    Yulang.B4TargetV3.Classify
                        (Yulang.GeneralNominalActualAgreedBoundary.boundary defer gap).toSourceBoundary registry state
                        focus (Yulang.CommonRoleOutermostResolver.Result.selected dictionary) →
                      Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context model focus
                        dictionary
@Yulang.GeneralDictionaryAgreedEvidence174.dictionaries_evidence_snapshot : ∀ {roles : Yulang.Roles.RoleDecls}
  {defer : Bool} {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles}
  {registry : Yulang.GeneralDeclarations.Registry} {state : Yulang.GeneralNominalSupport.Tracked roles}
  {root : Yulang.GeneralSourceDictionaries.Occurrence roles},
  Yulang.GeneralNominalActualInspectionSteps.SourceFormed registry root state →
    Yulang.GeneralDictionaryAgreedEvidence174.RecordedExtensions state →
      (∀ (demand : Yulang.GeneralSourceDictionaries.Occurrence roles), defer = true ∨ ¬gap registry state demand) →
        (Yulang.GeneralNominalActualAgreedBoundary.boundary defer gap).Stable registry state root →
          (∀ (demand : Yulang.GeneralSourceDictionaries.Occurrence roles),
              Yulang.GeneralNominalSaturationState.Generated state.current root demand →
                (Yulang.GeneralNominalActualAgreedBoundary.boundary defer gap).Stable registry state demand) →
            ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
              Yulang.GeneralNominalSaturationState.Models state.current model →
                ∀ (dictionaries : List Yulang.GeneralDictionaryReadback.Payload)
                  (demands : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
                  (∀ (child : Yulang.GeneralSourceDictionaries.Occurrence roles),
                      child ∈ demands →
                        child = root ∨ Yulang.GeneralNominalSaturationState.Generated state.current root child) →
                    Yulang.CommonRoleOutermostResolver.All₂
                        (fun child dictionary =>
                          Yulang.B4TargetV3.Classify
                            (Yulang.GeneralNominalActualAgreedBoundary.boundary defer gap).toSourceBoundary registry
                            state child (Yulang.CommonRoleOutermostResolver.Result.selected dictionary))
                        demands dictionaries →
                      Yulang.CommonRoleOutermostResolver.All₂
                        (Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context model)
                        demands dictionaries
@Yulang.GeneralDictionaryAgreedEvidence174.ordinary_initial_dictionary_evidence : ∀ {roles : Yulang.Roles.RoleDecls}
  {defer : Bool} {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles}
  {registry : Yulang.GeneralDeclarations.Registry} {state : Yulang.GeneralNominalSupport.Tracked roles}
  {root : Yulang.GeneralSourceDictionaries.Occurrence roles} (context : Yulang.GeneralNominalCandidates.Context),
  Yulang.GeneralNominalSourceFormation.InitialSource registry context root →
    Yulang.B4Target.Steps (Yulang.GeneralDictionaryAgreedEvidence174.OrdinaryStep registry root)
        (Yulang.GeneralNominalSupport.initial context root) state →
      (∀ (demand : Yulang.GeneralSourceDictionaries.Occurrence roles), defer = true ∨ ¬gap registry state demand) →
        (Yulang.GeneralNominalActualAgreedBoundary.boundary defer gap).Stable registry state root →
          (∀ (demand : Yulang.GeneralSourceDictionaries.Occurrence roles),
              Yulang.GeneralNominalSaturationState.Generated state.current root demand →
                (Yulang.GeneralNominalActualAgreedBoundary.boundary defer gap).Stable registry state demand) →
            ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
              Yulang.GeneralNominalSaturationState.Models state.current model →
                ∀ (dictionary : Yulang.GeneralDictionaryReadback.Payload),
                  Yulang.B4TargetV3.Classify
                      (Yulang.GeneralNominalActualAgreedBoundary.boundary defer gap).toSourceBoundary registry state
                      root (Yulang.CommonRoleOutermostResolver.Result.selected dictionary) →
                    Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context model root
                      dictionary
@Yulang.GeneralDictionaryAgreedEvidence174.ordinary_halted_dictionary_evidence : ∀ {roles : Yulang.Roles.RoleDecls}
  {defer : Bool} {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles}
  {registry : Yulang.GeneralDeclarations.Registry} {state : Yulang.GeneralNominalSupport.Tracked roles}
  {root : Yulang.GeneralSourceDictionaries.Occurrence roles},
  (Yulang.GeneralNominalActualAgreedBoundary.boundary defer gap).Checked registry →
    ∀ (context : Yulang.GeneralNominalCandidates.Context),
      Yulang.GeneralNominalSourceFormation.InitialSource registry context root →
        Yulang.B4Target.Steps (Yulang.GeneralDictionaryAgreedEvidence174.OrdinaryStep registry root)
            (Yulang.GeneralNominalSupport.initial context root) state →
          (∀ (after : Yulang.GeneralNominalSupport.Tracked roles),
              ¬Yulang.GeneralNominalActualInspectionSteps.Step registry root state after) →
            (∀ (demand : Yulang.GeneralSourceDictionaries.Occurrence roles),
                defer = true ∨ ¬gap registry state demand) →
              ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                Yulang.GeneralNominalSaturationState.Models state.current model →
                  ∀ (dictionary : Yulang.GeneralDictionaryReadback.Payload),
                    Yulang.B4TargetV3.Classify
                        (Yulang.GeneralNominalActualAgreedBoundary.boundary defer gap).toSourceBoundary registry state
                        root (Yulang.CommonRoleOutermostResolver.Result.selected dictionary) →
                      Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context model root
                        dictionary
@Yulang.GeneralDictionaryAgreedExact174.frontiers : {roles : Yulang.Roles.RoleDecls} →
  Bool →
    Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles →
      Yulang.B4SkeletonV3.Frontiers (Yulang.GeneralNominalActualAgreedBoundary.vocabulary roles)
@Yulang.GeneralDictionaryAgreedExact174.final_reachable : ∀ {roles : Yulang.Roles.RoleDecls} {defer : Bool}
  {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles} {registry : Yulang.GeneralDeclarations.Registry}
  {state : Yulang.GeneralNominalSupport.Tracked roles} {root : Yulang.GeneralSourceDictionaries.Occurrence roles},
  (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap).Checked registry →
    Yulang.B4TargetV5.Reachable (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap) registry root state →
      Yulang.B4TargetV5.Reachable (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap) registry root
        ((Yulang.GeneralDictionaryAgreedGround174.executor defer gap).run registry state root).fst
@Yulang.GeneralDictionaryAgreedExact174.final_exact : ∀ {roles : Yulang.Roles.RoleDecls} {defer : Bool}
  {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles} {registry : Yulang.GeneralDeclarations.Registry}
  {state : Yulang.GeneralNominalSupport.Tracked roles} {root : Yulang.GeneralSourceDictionaries.Occurrence roles},
  (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap).Checked registry →
    Yulang.B4TargetV5.Reachable (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap) registry root state →
      Yulang.CommonRoleOutermostResolver.FrontierExact
        (Yulang.GeneralDictionaryAgreedExact174.frontiers defer gap registry
          ((Yulang.GeneralDictionaryAgreedGround174.executor defer gap).run registry state root).fst)
@Yulang.GeneralDictionaryAgreedExact174.run_resolves_iff : ∀ {roles : Yulang.Roles.RoleDecls} {defer : Bool}
  {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles} {registry : Yulang.GeneralDeclarations.Registry}
  {state : Yulang.GeneralNominalSupport.Tracked roles} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {rank : Nat → Nat},
  (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap).Checked registry →
    Yulang.GeneralDictionaryAgreedEdge174.RoleStratified registry rank →
      Yulang.B4TargetV5.Reachable (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap) registry root state →
        ∀ (tree : Yulang.CommonRoleOutermostResolver.Tree),
          ((Yulang.GeneralDictionaryAgreedGround174.executor defer gap).run registry state root).snd = tree ↔
            Yulang.CommonRoleOutermostResolver.Resolves
              (Yulang.B4TargetV3.Local (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap).toSourceBoundary
                registry ((Yulang.GeneralDictionaryAgreedGround174.executor defer gap).run registry state root).fst)
              root tree
@Yulang.GeneralDictionaryAgreedExact174.completed_iff : ∀ {roles : Yulang.Roles.RoleDecls} {defer : Bool}
  {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles} {registry : Yulang.GeneralDeclarations.Registry}
  {state : Yulang.GeneralNominalSupport.Tracked roles} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {rank : Nat → Nat},
  (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap).Checked registry →
    Yulang.GeneralDictionaryAgreedEdge174.RoleStratified registry rank →
      Yulang.B4TargetV5.Reachable (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap) registry root state →
        ∀ (out : Yulang.CommonRoleOutermostResolver.Result),
          Yulang.B4TargetV3.Completed
              ((Yulang.GeneralDictionaryAgreedGround174.executor defer gap).run registry state root).snd out ↔
            Yulang.B4TargetV3.Classify (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap).toSourceBoundary
              registry ((Yulang.GeneralDictionaryAgreedGround174.executor defer gap).run registry state root).fst root
              out
@Yulang.GeneralDictionaryAgreedExact174.initial_run_resolves_iff : ∀ {roles : Yulang.Roles.RoleDecls} {defer : Bool}
  {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles} {registry : Yulang.GeneralDeclarations.Registry}
  {state : Yulang.GeneralNominalSupport.Tracked roles} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {rank : Nat → Nat},
  (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap).Checked registry →
    Yulang.GeneralDictionaryAgreedEdge174.RoleStratified registry rank →
      (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap).Initial registry root state →
        ∀ (tree : Yulang.CommonRoleOutermostResolver.Tree),
          ((Yulang.GeneralDictionaryAgreedGround174.executor defer gap).run registry state root).snd = tree ↔
            Yulang.CommonRoleOutermostResolver.Resolves
              (Yulang.B4TargetV3.Local (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap).toSourceBoundary
                registry ((Yulang.GeneralDictionaryAgreedGround174.executor defer gap).run registry state root).fst)
              root tree
@Yulang.GeneralDictionaryAgreedGround174.boundary : {roles : Yulang.Roles.RoleDecls} →
  Bool →
    Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles →
      Yulang.B4TargetV5.SourceBoundary (Yulang.GeneralNominalActualBoundary.vocabulary roles)
@Yulang.GeneralDictionaryAgreedGround174.reachable_old : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : (Yulang.GeneralNominalActualBoundary.vocabulary roles).Registry}
  {root : (Yulang.GeneralNominalActualBoundary.vocabulary roles).Demand}
  {state : (Yulang.GeneralNominalActualBoundary.vocabulary roles).State} {defer : Bool}
  {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles},
  Yulang.B4TargetV5.Reachable (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap) registry root state →
    Yulang.B4TargetV5.Reachable (Yulang.GeneralNominalActualBoundary.groundBoundary roles) registry root state
@Yulang.GeneralDictionaryAgreedGround174.reachable_agreed : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : (Yulang.GeneralNominalActualBoundary.vocabulary roles).Registry}
  {root : (Yulang.GeneralNominalActualBoundary.vocabulary roles).Demand}
  {state : (Yulang.GeneralNominalActualBoundary.vocabulary roles).State} {defer : Bool}
  {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles},
  Yulang.B4TargetV5.Reachable (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap) registry root state →
    Yulang.B4TargetV5.Reachable (Yulang.GeneralNominalActualAgreedBoundary.boundary defer gap) registry root state
@Yulang.GeneralDictionaryAgreedGround174.progress : ∀ {roles : Yulang.Roles.RoleDecls} (defer : Bool)
  (gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles) (registry : Yulang.GeneralDeclarations.Registry),
  (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap).Checked registry →
    ∀ (state : Yulang.GeneralNominalSupport.Tracked roles) (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
      Yulang.B4TargetV5.Reachable (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap) registry root state →
        Acc
          (fun next current =>
            (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap).Step registry root current next)
          state
@Yulang.GeneralDictionaryAgreedGround174.diagnostic : {roles : Yulang.Roles.RoleDecls} →
  Bool →
    Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles →
      Yulang.GeneralDeclarations.Registry →
        Yulang.GeneralNominalSupport.Tracked roles →
          Yulang.GeneralSourceDictionaries.Occurrence roles → Yulang.CommonRoleOutermostResolver.Tree
@Yulang.GeneralDictionaryAgreedGround174.diagnostic_eq_resolve : ∀ {roles : Yulang.Roles.RoleDecls} (defer : Bool)
  (gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles) (registry : Yulang.GeneralDeclarations.Registry)
  (state : Yulang.GeneralNominalSupport.Tracked roles) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (exact :
    Yulang.CommonRoleOutermostResolver.FrontierExact
      (Yulang.GeneralNominalActualAgreedBoundary.frontiers defer gap registry state))
  (accessible :
    Acc
      (Yulang.CommonRoleOutermostResolver.Child
        (Yulang.GeneralNominalActualAgreedBoundary.frontiers defer gap registry state).Local)
      root),
  Yulang.GeneralDictionaryAgreedGround174.diagnostic defer gap registry state root =
    Yulang.CommonRoleOutermostResolver.resolve
      (Yulang.GeneralNominalActualAgreedBoundary.frontiers defer gap registry state) exact root accessible
@Yulang.GeneralDictionaryAgreedGround174.executor : {roles : Yulang.Roles.RoleDecls} →
  Bool →
    Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles →
      Yulang.B4TargetV3.Executor (Yulang.GeneralNominalActualBoundary.vocabulary roles)
@Yulang.GeneralDictionaryAgreedGround174.execution : ∀ {roles : Yulang.Roles.RoleDecls} (defer : Bool)
  (gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles) (registry : Yulang.GeneralDeclarations.Registry),
  (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap).Checked registry →
    ∀ (state : Yulang.GeneralNominalSupport.Tracked roles) (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
      Yulang.B4TargetV5.Reachable (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap) registry root state →
        Yulang.B4Target.Steps ((Yulang.GeneralDictionaryAgreedGround174.boundary defer gap).Step registry root) state
          ((Yulang.GeneralDictionaryAgreedGround174.executor defer gap).run registry state root).fst
@Yulang.GeneralDictionaryAgreedGround174.halted : ∀ {roles : Yulang.Roles.RoleDecls} (defer : Bool)
  (gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles) (registry : Yulang.GeneralDeclarations.Registry),
  (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap).Checked registry →
    ∀ (state : Yulang.GeneralNominalSupport.Tracked roles) (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
      Yulang.B4TargetV5.Reachable (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap) registry root state →
        ∀ (next : (Yulang.GeneralNominalActualBoundary.vocabulary roles).State),
          ¬(Yulang.GeneralDictionaryAgreedGround174.boundary defer gap).Step registry root
              ((Yulang.GeneralDictionaryAgreedGround174.executor defer gap).run registry state root).fst next
@Yulang.GeneralDictionaryAgreedGround174.treeExecution : ∀ {roles : Yulang.Roles.RoleDecls} (defer : Bool)
  (gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles) (registry : Yulang.GeneralDeclarations.Registry),
  (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap).Checked registry →
    ∀ (state : Yulang.GeneralNominalSupport.Tracked roles) (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
      Yulang.B4TargetV5.Reachable (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap) registry root state →
        ∀
          (exact :
            Yulang.CommonRoleOutermostResolver.FrontierExact
              (Yulang.GeneralNominalActualAgreedBoundary.frontiers defer gap registry
                ((Yulang.GeneralDictionaryAgreedGround174.executor defer gap).run registry state root).fst))
          (accessible :
            Acc
              (Yulang.CommonRoleOutermostResolver.Child
                (Yulang.GeneralNominalActualAgreedBoundary.frontiers defer gap registry
                    ((Yulang.GeneralDictionaryAgreedGround174.executor defer gap).run registry state root).fst).Local)
              root),
          ((Yulang.GeneralDictionaryAgreedGround174.executor defer gap).run registry state root).snd =
            Yulang.CommonRoleOutermostResolver.resolve
              (Yulang.GeneralNominalActualAgreedBoundary.frontiers defer gap registry
                ((Yulang.GeneralDictionaryAgreedGround174.executor defer gap).run registry state root).fst)
              exact root accessible
@Yulang.GeneralDictionaryAgreedGround174.saturationTotal : ∀ {roles : Yulang.Roles.RoleDecls} (defer : Bool)
  (gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles),
  Yulang.B4TargetV5.SaturationTotal (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap)
    (Yulang.GeneralDictionaryAgreedGround174.executor defer gap)
@Yulang.GeneralDictionaryAgreedGround174.initialReorders : ∀ {roles : Yulang.Roles.RoleDecls} (defer : Bool)
  (gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles)
  (registry other : Yulang.GeneralDeclarations.Registry),
  (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap).Reorders registry other →
    ∀ (state : Yulang.GeneralNominalSupport.Tracked roles) (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
      (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap).Initial registry root state →
        (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap).Initial other root state
Yulang.GeneralDictionaryAgreedRoleExamples174.wrapOnly : Yulang.GeneralDeclarations.Registry
Yulang.GeneralDictionaryAgreedRoleExamples174.roleRank : Nat → Nat
Yulang.GeneralDictionaryAgreedRoleExamples174.wrapOnly_checked : Yulang.GeneralDeclarations.Checked
  Yulang.GeneralDictionaryAgreedRoleExamples174.wrapOnly
Yulang.GeneralDictionaryAgreedRoleExamples174.wrapOnly_nonleaf : Yulang.GeneralDeclarationExamples.wrap.requirements ≠
  []
Yulang.GeneralDictionaryAgreedRoleExamples174.wrapOnly_stratified : Yulang.GeneralDictionaryAgreedEdge174.RoleStratified
  Yulang.GeneralDictionaryAgreedRoleExamples174.wrapOnly Yulang.GeneralDictionaryAgreedRoleExamples174.roleRank
Yulang.GeneralDictionaryAgreedRoleExamples174.wrapOnly_accessible : ∀ (defer : Bool)
  (gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate Yulang.GeneralDeclarationExamples.roles)
  (state : Yulang.GeneralNominalSupport.Tracked Yulang.GeneralDeclarationExamples.roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles),
  Acc
    (Yulang.CommonRoleOutermostResolver.Child
      (Yulang.B4TargetV3.Local (Yulang.GeneralNominalActualAgreedBoundary.boundary defer gap).toSourceBoundary
        Yulang.GeneralDictionaryAgreedRoleExamples174.wrapOnly state))
    root
Yulang.GeneralDictionaryAgreedRoleExamples174.display_not_stratified : ∀ (rank : Nat → Nat),
  ¬Yulang.GeneralDictionaryAgreedEdge174.RoleStratified Yulang.GeneralDeclarationExamples.registry rank

```
