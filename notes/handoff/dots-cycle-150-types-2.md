# Cycle150 exact theorem types, part2/3

Lean4.35.0 `#check @name`, exit0.

```text
@Yulang.GeneralDictionaryNamedLocality.steps_ordinary : ∀ {roles : Yulang.Roles.RoleDecls}
  {names : Nat → Yulang.GeneralSourceDictionaries.Occurrence roles} {registry : Yulang.GeneralDeclarations.Registry}
  {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {before after : Yulang.GeneralNominalSupport.Tracked roles},
  Yulang.B4Target.Steps (Yulang.GeneralDictionaryNamedLocality.Step names registry root) before after →
    Yulang.B4Target.Steps (Yulang.GeneralDictionarySupportOrdinaryExecution.Step registry root) before after
@Yulang.GeneralDictionaryNamedLocality.at_aliases : ∀ {roles : Yulang.Roles.RoleDecls}
  {names : Nat → Yulang.GeneralSourceDictionaries.Occurrence roles} {registry : Yulang.GeneralDeclarations.Registry}
  {before after : Yulang.GeneralNominalSupport.Tracked roles}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles},
  Yulang.GeneralDictionaryNamedLocality.At names registry before focus after →
    after.current.aliases = before.current.aliases
@Yulang.GeneralDictionaryNamedLocality.at_named : ∀ {roles : Yulang.Roles.RoleDecls}
  {names : Nat → Yulang.GeneralSourceDictionaries.Occurrence roles} {registry : Yulang.GeneralDeclarations.Registry}
  {before after : Yulang.GeneralNominalSupport.Tracked roles}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles},
  Yulang.GeneralDictionaryNamedLocality.At names registry before focus after →
    Yulang.GeneralDictionaryNamedLocality.Named names before.current →
      Yulang.GeneralDictionaryNamedLocality.Named names after.current
@Yulang.GeneralDictionaryNamedLocality.initial_invariants : ∀ {roles : Yulang.Roles.RoleDecls}
  (names : Nat → Yulang.GeneralSourceDictionaries.Occurrence roles) (registry : Yulang.GeneralDeclarations.Registry)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (context : Yulang.GeneralNominalCandidates.Context),
  names root.identity = root →
    ∀ (state : Yulang.GeneralNominalSupport.Tracked roles),
      Yulang.B4Target.Steps (Yulang.GeneralDictionaryNamedLocality.Step names registry root)
          (Yulang.GeneralNominalSupport.initial context root) state →
        Yulang.GeneralDictionaryNamedLocality.Named names state.current ∧ state.current.aliases = []
@Yulang.GeneralDictionaryNamedLocality.alias_eq : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalSaturationState.State roles},
  state.aliases = [] → ∀ {first last : Nat}, Yulang.GeneralNominalSaturationState.Alias state first last → first = last
@Yulang.GeneralDictionaryNamedLocality.related_locality : ∀ {roles : Yulang.Roles.RoleDecls}
  (names : Nat → Yulang.GeneralSourceDictionaries.Occurrence roles)
  (state : Yulang.GeneralNominalSaturationState.State roles),
  Yulang.GeneralDictionaryNamedLocality.Named names state →
    state.aliases = [] →
      ∀ (focus : Yulang.GeneralSourceDictionaries.Occurrence roles),
        names focus.identity = focus →
          ∀ (site : Yulang.GeneralNominalDemandMerging.Site roles),
            Yulang.GeneralNominalJointCandidates.Related state focus site → site.occurrence = focus
@Yulang.GeneralDictionaryNamedLocality.initial_joint : ∀ {roles : Yulang.Roles.RoleDecls}
  (names : Nat → Yulang.GeneralSourceDictionaries.Occurrence roles) (registry : Yulang.GeneralDeclarations.Registry)
  (root focus : Yulang.GeneralSourceDictionaries.Occurrence roles) (context : Yulang.GeneralNominalCandidates.Context),
  Yulang.GeneralNominalSourceFormation.InitialSource registry context root →
    names root.identity = root →
      ∀ (state : Yulang.GeneralNominalSupport.Tracked roles),
        Yulang.B4Target.Steps (Yulang.GeneralDictionaryNamedLocality.Step names registry root)
            (Yulang.GeneralNominalSupport.initial context root) state →
          ∀ (packet : Yulang.GeneralNominalSaturationState.Packet roles),
            packet ∈ state.current.packets →
              packet.site.occurrence = focus →
                ∀ (key : Nat) (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
                  Yulang.GeneralNominalSupportBoundary.Local registry state focus
                      (Yulang.CommonRoleOutermostResolver.Frontier.selected key children) →
                    ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                      Yulang.GeneralNominalSaturationState.Models state.current model →
                        Yulang.GeneralNominalJointCandidates.Joint registry state.current focus key
Yulang.GeneralDictionaryNamedLocalityExample.root_named : Yulang.GeneralDictionaryNamedLocalityExample.names
    Yulang.GeneralNominalExamples.displayRoot.identity =
  Yulang.GeneralNominalExamples.displayRoot
Yulang.GeneralDictionaryNamedLocalityExample.child_named : Yulang.GeneralDictionaryNamedLocalityExample.names
    Yulang.GeneralNominalExamples.displayChild.identity =
  Yulang.GeneralNominalExamples.displayChild
Yulang.GeneralDictionaryNamedLocalityExample.actual_trace : Yulang.B4Target.Steps
  (Yulang.GeneralDictionaryNamedLocality.Step Yulang.GeneralDictionaryNamedLocalityExample.names
    Yulang.GeneralNominalExamples.registry Yulang.GeneralNominalExamples.displayRoot)
  Yulang.GeneralDictionarySupportRecursiveExample.start Yulang.GeneralDictionarySupportRecursiveExample.finish
Yulang.GeneralDictionaryNamedLocalityExample.every_model_joint : ∀
  (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionarySupportRecursiveExample.finish.current
      assignment →
    Yulang.GeneralNominalJointCandidates.Joint Yulang.GeneralNominalExamples.registry
      Yulang.GeneralDictionarySupportRecursiveExample.finish.current Yulang.GeneralNominalExamples.displayRoot 1
@Yulang.GeneralDictionaryTreeCoverage.selected_instance : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root focus : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (state : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.GeneralNominalSupportSteps.SourceFormed registry root state →
    Yulang.GeneralDictionaryTreeCoverage.Covered registry state root →
      Yulang.GeneralNominalSaturationState.Generated state.current root focus →
        ∀ (key : Nat) (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
          Yulang.GeneralNominalSupportBoundary.Local registry state focus
              (Yulang.CommonRoleOutermostResolver.Frontier.selected key children) →
            ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
              Yulang.GeneralNominalSaturationState.Models state.current model →
                Yulang.GeneralDictionaryRecursiveEvidence.Instance registry state.current.context model focus key
                    children ∧
                  ∀ (child : Yulang.GeneralSourceDictionaries.Occurrence roles),
                    child ∈ children → Yulang.GeneralNominalSaturationState.Generated state.current root child
@Yulang.GeneralDictionaryTreeCoverage.dictionary_evidence : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (state : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.GeneralNominalSupportSteps.SourceFormed registry root state →
    Yulang.GeneralDictionaryTreeCoverage.Covered registry state root →
      ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
        Yulang.GeneralNominalSaturationState.Models state.current model →
          ∀ (dictionary : Yulang.GeneralDictionaryReadback.Payload)
            (focus : Yulang.GeneralSourceDictionaries.Occurrence roles),
            Yulang.GeneralNominalSaturationState.Generated state.current root focus →
              Yulang.B4TargetV3.Classify (Yulang.GeneralNominalSupportBoundary.boundary roles).toSourceBoundary registry
                  state focus (Yulang.CommonRoleOutermostResolver.Result.selected dictionary) →
                Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context model focus dictionary
@Yulang.GeneralDictionaryTreeCoverage.dictionaries_evidence : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (state : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.GeneralNominalSupportSteps.SourceFormed registry root state →
    Yulang.GeneralDictionaryTreeCoverage.Covered registry state root →
      ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
        Yulang.GeneralNominalSaturationState.Models state.current model →
          ∀ (dictionaries : List Yulang.GeneralDictionaryReadback.Payload)
            (demands : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
            (∀ (focus : Yulang.GeneralSourceDictionaries.Occurrence roles),
                focus ∈ demands → Yulang.GeneralNominalSaturationState.Generated state.current root focus) →
              Yulang.CommonRoleOutermostResolver.All₂
                  (fun focus dictionary =>
                    Yulang.B4TargetV3.Classify (Yulang.GeneralNominalSupportBoundary.boundary roles).toSourceBoundary
                      registry state focus (Yulang.CommonRoleOutermostResolver.Result.selected dictionary))
                  demands dictionaries →
                Yulang.CommonRoleOutermostResolver.All₂
                  (Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context model) demands
                  dictionaries
@Yulang.GeneralDictionaryTreeCoverage.of_branch : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSupport.Tracked roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
  Yulang.GeneralDictionaryBranchCoverage.Covered registry state root →
    Yulang.GeneralDictionaryTreeCoverage.Covered registry state root
Yulang.GeneralDictionaryTreeCoverage.recursive_fixture : ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionarySupportRecursiveExample.finish.current model →
    Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralNominalExamples.registry
      Yulang.GeneralDictionarySupportRecursiveExample.finish.current.context model
      Yulang.GeneralNominalExamples.displayRoot
      (Yulang.CommonRoleOutermostResolver.Dictionary.node 1 [Yulang.CommonRoleOutermostResolver.Dictionary.node 3 []])
@Yulang.GeneralDictionaryTreeCoverage.of_trace : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (context : Yulang.GeneralNominalCandidates.Context) (state : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.B4Target.Steps (Yulang.GeneralDictionarySupportOrdinaryExecution.Step registry root)
      (Yulang.GeneralNominalSupport.initial context root) state →
    Yulang.GeneralDictionaryTreeCoverage.TraceCovered registry state root →
      Yulang.GeneralDictionaryTreeCoverage.Covered registry state root
@Yulang.GeneralDictionaryTreeCoverage.initial_dictionary_evidence : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (context : Yulang.GeneralNominalCandidates.Context),
  Yulang.GeneralNominalSourceFormation.InitialSource registry context root →
    ∀ (state : Yulang.GeneralNominalSupport.Tracked roles),
      Yulang.B4Target.Steps (Yulang.GeneralDictionarySupportOrdinaryExecution.Step registry root)
          (Yulang.GeneralNominalSupport.initial context root) state →
        Yulang.GeneralDictionaryTreeCoverage.TraceCovered registry state root →
          ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
            Yulang.GeneralNominalSaturationState.Models state.current model →
              ∀ (dictionary : Yulang.GeneralDictionaryReadback.Payload),
                Yulang.B4TargetV3.Classify (Yulang.GeneralNominalSupportBoundary.boundary roles).toSourceBoundary
                    registry state root (Yulang.CommonRoleOutermostResolver.Result.selected dictionary) →
                  Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context model root
                    dictionary
@Yulang.GeneralDictionaryTreeLeaf.branch_models : ∀ {roles : Yulang.Roles.RoleDecls}
  (context : Yulang.GeneralNominalRecursiveCandidates.Context) (registry : Yulang.GeneralDeclarations.Registry)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (declaration : Yulang.GeneralDeclarations.Declaration)
  (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
  (shape : Yulang.GeneralDictionaryTreeLeaf.TreeLeafShape context root declaration)
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models context.state model →
    Yulang.GeneralNominalRecursiveCandidates.BranchModels registry context root declaration checked
      [(shape.slot, shape.slot)] model
@Yulang.GeneralDictionaryTreeLeaf.ready : ∀ {roles : Yulang.Roles.RoleDecls}
  (context : Yulang.GeneralNominalRecursiveCandidates.Context) (registry : Yulang.GeneralDeclarations.Registry)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (declaration : Yulang.GeneralDeclarations.Declaration)
  (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
  (shape : Yulang.GeneralDictionaryTreeLeaf.TreeLeafShape context root declaration),
  Yulang.GeneralNominalRecursiveCandidates.RequestReady registry context root declaration checked
    [(shape.slot, shape.slot)]
@Yulang.GeneralDictionaryTreeLeaf.instance_of_shape : ∀ {roles : Yulang.Roles.RoleDecls}
  (context : Yulang.GeneralNominalRecursiveCandidates.Context) (registry : Yulang.GeneralDeclarations.Registry)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (declaration : Yulang.GeneralDeclarations.Declaration),
  declaration ∈ registry.declarations →
    Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration →
      ∀ (shape : Yulang.GeneralDictionaryTreeLeaf.TreeLeafShape context root declaration),
        Yulang.GeneralNominalRecursiveCandidates.Metadata registry context →
          ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
            Yulang.GeneralNominalState.Models context.state model →
              Yulang.GeneralDictionaryRecursiveEvidence.Instance registry context model root declaration.id []
@Yulang.GeneralDictionaryTreeLeaf.selected_leaf : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSaturationState.State roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (declaration : Yulang.GeneralDeclarations.Declaration),
  declaration ∈ registry.declarations →
    Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration →
      ∀ (shape : Yulang.GeneralDictionaryTreeLeaf.TreeLeafShape state.context root declaration) (key : Nat)
        (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
        Yulang.GeneralNominalFeedbackK2.Local registry state root
            (Yulang.CommonRoleOutermostResolver.Frontier.selected key children) →
          ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
            Yulang.GeneralNominalState.Models state.context.state model →
              declaration.id = key ∧
                children = [] ∧
                  Yulang.GeneralDictionaryRecursiveEvidence.Instance registry state.context model root key [] ∧
                    Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry state.context model root
                      (Yulang.CommonRoleOutermostResolver.Dictionary.node key [])
@Yulang.GeneralDictionaryTreeLeaf.selected_of_coverage : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSaturationState.State roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
  Yulang.GeneralDictionaryTreeLeaf.HasTreeLeaf registry state.context root →
    ∀ (key : Nat) (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
      Yulang.GeneralNominalFeedbackK2.Local registry state root
          (Yulang.CommonRoleOutermostResolver.Frontier.selected key children) →
        ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
          Yulang.GeneralNominalState.Models state.context.state model →
            children = [] ∧
              Yulang.GeneralDictionaryRecursiveEvidence.Instance registry state.context model root key [] ∧
                Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry state.context model root
                  (Yulang.CommonRoleOutermostResolver.Dictionary.node key [])
@Yulang.GeneralDictionaryTreeLeaf.spine_covered : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (context : Yulang.GeneralNominalRecursiveCandidates.Context)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
  Yulang.GeneralDictionarySpineLeaf.HasSpineLeaf registry context root →
    Yulang.GeneralDictionaryTreeLeaf.HasTreeLeaf registry context root
@Yulang.GeneralDictionaryTreeLeaf.branch_covered : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (context : Yulang.GeneralNominalRecursiveCandidates.Context)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
  Yulang.GeneralDictionaryBranchLeaf.HasBranchLeaf registry context root →
    Yulang.GeneralDictionaryTreeLeaf.HasTreeLeaf registry context root
Yulang.GeneralNominalBranchExample.state_models : Yulang.GeneralNominalState.Models
  Yulang.GeneralNominalBranchExample.state Yulang.GeneralNominalBranchExample.model
Yulang.GeneralNominalBranchExample.checked : Yulang.GeneralDeclarations.DeclarationChecked
  Yulang.GeneralDeclarationExamples.constructors Yulang.GeneralDeclarationExamples.roles
  Yulang.GeneralNominalBranchExample.declaration
Yulang.GeneralNominalBranchExample.actual_branch : Yulang.GeneralNominalRecursiveCandidates.BranchModels
  Yulang.GeneralNominalBranchExample.registry Yulang.GeneralNominalBranchExample.context
  Yulang.GeneralNominalBranchExample.root Yulang.GeneralNominalBranchExample.declaration
  Yulang.GeneralNominalBranchExample.checked [(0, 0)] Yulang.GeneralNominalBranchExample.model
@Yulang.GeneralNominalBranchExample.not_unary_spine : ∀ {n : Nat} (names : Fin n → Nat)
  (bounds : Fin n → Yulang.GeneralNominalInspection.Bounds Yulang.GeneralNominalBranchExample.state)
  (spine : Yulang.GeneralNominalSpineFacts.Spine Yulang.GeneralNominalBranchExample.state names bounds 0),
  spine.query ≠ Yulang.GeneralNominalBranchExample.fork.query
Yulang.GeneralNominalBranchExample.inhabited_branch : Yulang.GeneralNominalState.Models
    Yulang.GeneralNominalBranchExample.state Yulang.GeneralNominalBranchExample.model ∧
  Yulang.GeneralNominalRecursiveCandidates.BranchModels Yulang.GeneralNominalBranchExample.registry
    Yulang.GeneralNominalBranchExample.context Yulang.GeneralNominalBranchExample.root
    Yulang.GeneralNominalBranchExample.declaration Yulang.GeneralNominalBranchExample.checked [(0, 0)]
    Yulang.GeneralNominalBranchExample.model
Yulang.GeneralNominalBranchFacts.report_exact : ∀ (context : Yulang.GeneralNominalRecursiveCandidates.Context)
  (declaration : Yulang.GeneralDeclarations.Declaration) {n m : Nat} {names : Fin (n + m) → Nat}
  {bounds : Fin (n + m) → Yulang.GeneralNominalInspection.Bounds context.state} {slot : Fin context.state.base.slots}
  (fork : Yulang.GeneralNominalBranchFacts.Fork context.state n m names bounds slot),
  Yulang.GeneralNominalInspection.queries context.state context.interpretation declaration = [fork.query] →
    Yulang.GeneralNominalRecursiveCandidates.report context declaration [(slot, slot)] =
      have __src := Yulang.GeneralNominalRecursiveInspection.inspect context.state fork.query (slot, slot) none;
      { captures := __src.captures, inspected := __src.inspected,
        checked :=
          (slot, slot) ::
            (Yulang.GeneralNominalRecursiveInspection.inspect context.state fork.query (slot, slot) none).checked,
        blocked := __src.blocked, conflicts := __src.conflicts, arity := __src.arity, anchors := __src.anchors,
        tests := __src.tests }
@Yulang.GeneralNominalBranchFacts.private_models : ∀ {roles : Yulang.Roles.RoleDecls}
  (context : Yulang.GeneralNominalRecursiveCandidates.Context) (registry : Yulang.GeneralDeclarations.Registry)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (declaration : Yulang.GeneralDeclarations.Declaration)
  {n m : Nat} (names : Fin (n + m) → Nat),
  Function.Injective names →
    declaration.inputNames = List.ofFn names →
      ∀ (bounds : Fin (n + m) → Yulang.GeneralNominalInspection.Bounds context.state)
        {slot : Fin context.state.base.slots}
        (fork : Yulang.GeneralNominalBranchFacts.Fork context.state n m names bounds slot),
        Yulang.GeneralNominalInspection.queries context.state context.interpretation declaration = [fork.query] →
          ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
            Yulang.GeneralNominalState.Models context.state model →
              Yulang.GeneralNominalState.Models
                  (Yulang.GeneralNominalRecursiveCandidates.privateState registry context root declaration
                    [(slot, slot)])
                  model ∧
                Yulang.GeneralNominalRecursiveInspection.ProjectionModels context.state
                  (Yulang.GeneralNominalRecursiveCandidates.report context declaration [(slot, slot)]) model
Yulang.GeneralNominalBranchProjection.point_argument_matches : ∀ (state : Yulang.GeneralNominalState.State)
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models state model →
    ∀ (slot child : Fin state.base.slots) (descriptor : Yulang.GeneralNominalState.Descriptor state.base.slots),
      state.nominals slot = some descriptor →
        ∀ (index : Nat),
          descriptor.arguments[index]? = some (Yulang.GeneralNominalState.Parameter.type (child, child)) →
            ∀ (origin : Yulang.GeneralNominalRecursiveInspection.Origin),
              Yulang.GeneralNominalSpineFacts.Matches state model slot origin →
                Yulang.GeneralNominalSpineFacts.Matches state model child
                  (origin.nominal descriptor.declaration.name index)
Yulang.GeneralNominalBranchProjection.append_projection : ∀ (state : Yulang.GeneralNominalState.State)
  (left right : Yulang.GeneralNominalRecursiveInspection.Report state)
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalRecursiveInspection.ProjectionModels state left model →
    Yulang.GeneralNominalRecursiveInspection.ProjectionModels state right model →
      (∀ (a : Yulang.GeneralNominalRecursiveInspection.Capture state),
          a ∈ left.captures →
            ∀ (b : Yulang.GeneralNominalRecursiveInspection.Capture state), b ∈ right.captures → a.name ≠ b.name) →
        Yulang.GeneralNominalRecursiveInspection.ProjectionModels state (left.append right) model
Yulang.GeneralNominalBranchProjection.spine_capture_name : ∀ (state : Yulang.GeneralNominalState.State) {n : Nat}
  (names : Fin n → Nat) (bounds : Fin n → Yulang.GeneralNominalInspection.Bounds state) {slot : Fin state.base.slots}
  (spine : Yulang.GeneralNominalSpineFacts.Spine state names bounds slot)
  (origin : Option Yulang.GeneralNominalRecursiveInspection.Origin)
  (capture : Yulang.GeneralNominalRecursiveInspection.Capture state),
  capture ∈ (Yulang.GeneralNominalRecursiveInspection.inspect state spine.query (slot, slot) origin).captures →
    ∃ i, capture.name = names i
Yulang.GeneralNominalBranchProjection.inspect_fork : ∀ (state : Yulang.GeneralNominalState.State)
  (slot left right : Fin state.base.slots) (descriptor : Yulang.GeneralNominalState.Descriptor state.base.slots),
  state.nominals slot = some descriptor →
    descriptor.arguments =
        [Yulang.GeneralNominalState.Parameter.type (left, left),
          Yulang.GeneralNominalState.Parameter.type (right, right)] →
      ∀ (one two : Yulang.GeneralNominalInspection.Query)
        (origin : Option Yulang.GeneralNominalRecursiveInspection.Origin),
        Yulang.GeneralNominalRecursiveInspection.inspect state
            (Yulang.GeneralNominalInspection.Query.nominal descriptor.declaration.name [one, two]) (slot, slot) origin =
          Yulang.GeneralNominalRecursiveInspection.Report.visit (slot, slot) origin
            (Yulang.GeneralNominalRecursiveInspection.Test.nominal descriptor.declaration.name 2)
            ((Yulang.GeneralNominalRecursiveInspection.inspect state one (left, left)
                  (some
                    ((origin.getD
                          (Yulang.GeneralNominalRecursiveInspection.Origin.source (state.base.source slot))).nominal
                      descriptor.declaration.name 0))).append
              (Yulang.GeneralNominalRecursiveInspection.inspect state two (right, right)
                (some
                  ((origin.getD
                        (Yulang.GeneralNominalRecursiveInspection.Origin.source (state.base.source slot))).nominal
                    descriptor.declaration.name 1))))
Yulang.GeneralNominalBranchProjection.fork_projection : ∀ (state : Yulang.GeneralNominalState.State) {n m : Nat}
  (names : Fin n → Nat) (other : Fin m → Nat),
  Function.Injective names →
    Function.Injective other →
      (∀ (i : Fin n) (j : Fin m), names i ≠ other j) →
        ∀ (bounds : Fin n → Yulang.GeneralNominalInspection.Bounds state)
          (otherBounds : Fin m → Yulang.GeneralNominalInspection.Bounds state) (slot left right : Fin state.base.slots)
          (descriptor : Yulang.GeneralNominalState.Descriptor state.base.slots),
          state.nominals slot = some descriptor →
            descriptor.arguments =
                [Yulang.GeneralNominalState.Parameter.type (left, left),
                  Yulang.GeneralNominalState.Parameter.type (right, right)] →
              ∀ (one : Yulang.GeneralNominalSpineFacts.Spine state names bounds left)
                (two : Yulang.GeneralNominalSpineFacts.Spine state other otherBounds right)
                (model : Yulang.GeneralNominalCommonBridge.Assignment),
                Yulang.GeneralNominalState.Models state model →
                  ∀ (origin : Option Yulang.GeneralNominalRecursiveInspection.Origin),
                    (∀ (o : Yulang.GeneralNominalRecursiveInspection.Origin),
                        origin = some o → Yulang.GeneralNominalSpineFacts.Matches state model slot o) →
                      Yulang.GeneralNominalRecursiveInspection.ProjectionModels state
                        (Yulang.GeneralNominalRecursiveInspection.inspect state
                          (Yulang.GeneralNominalInspection.Query.nominal descriptor.declaration.name
                            [one.query, two.query])
                          (slot, slot) origin)
                        model
Yulang.GeneralNominalBranchProjection.fork_finished : ∀ (state : Yulang.GeneralNominalState.State) {n m : Nat}
  (names : Fin n → Nat) (other : Fin m → Nat) (bounds : Fin n → Yulang.GeneralNominalInspection.Bounds state)
  (otherBounds : Fin m → Yulang.GeneralNominalInspection.Bounds state) (slot left right : Fin state.base.slots)
  (descriptor : Yulang.GeneralNominalState.Descriptor state.base.slots),
  state.nominals slot = some descriptor →
    descriptor.arguments =
        [Yulang.GeneralNominalState.Parameter.type (left, left),
          Yulang.GeneralNominalState.Parameter.type (right, right)] →
      ∀ (one : Yulang.GeneralNominalSpineFacts.Spine state names bounds left)
        (two : Yulang.GeneralNominalSpineFacts.Spine state other otherBounds right)
        (origin : Option Yulang.GeneralNominalRecursiveInspection.Origin),
        Yulang.GeneralNominalRecursiveInspection.Finished
          (Yulang.GeneralNominalRecursiveInspection.inspect state
            (Yulang.GeneralNominalInspection.Query.nominal descriptor.declaration.name [one.query, two.query])
            (slot, slot) origin)
Yulang.GeneralNominalBranchProjection.fork_bindings : ∀ (state : Yulang.GeneralNominalState.State) {n m : Nat}
  (names : Fin (n + m) → Nat) (bounds : Fin (n + m) → Yulang.GeneralNominalInspection.Bounds state)
  (slot left right : Fin state.base.slots) (descriptor : Yulang.GeneralNominalState.Descriptor state.base.slots),
  state.nominals slot = some descriptor →
    descriptor.arguments =
        [Yulang.GeneralNominalState.Parameter.type (left, left),
          Yulang.GeneralNominalState.Parameter.type (right, right)] →
      ∀
        (one :
          Yulang.GeneralNominalSpineFacts.Spine state (fun i => names (Fin.castAdd m i))
            (fun i => bounds (Fin.castAdd m i)) left)
        (two :
          Yulang.GeneralNominalSpineFacts.Spine state (fun i => names (Fin.natAdd n i))
            (fun i => bounds (Fin.natAdd n i)) right)
        (origin : Option Yulang.GeneralNominalRecursiveInspection.Origin),
        Yulang.GeneralNominalRecursiveInspection.bindings state
            (Yulang.GeneralNominalRecursiveInspection.inspect state
              (Yulang.GeneralNominalInspection.Query.nominal descriptor.declaration.name [one.query, two.query])
              (slot, slot) origin) =
          List.ofFn fun i => (names i, state.base.source (bounds i).fst, state.base.source (bounds i).snd)
Yulang.GeneralNominalBranchProjection.fork_checked : ∀ (state : Yulang.GeneralNominalState.State) {n m : Nat}
  (names : Fin n → Nat) (other : Fin m → Nat) (bounds : Fin n → Yulang.GeneralNominalInspection.Bounds state)
  (otherBounds : Fin m → Yulang.GeneralNominalInspection.Bounds state) (slot left right : Fin state.base.slots)
  (descriptor : Yulang.GeneralNominalState.Descriptor state.base.slots),
  state.nominals slot = some descriptor →
    descriptor.arguments =
        [Yulang.GeneralNominalState.Parameter.type (left, left),
          Yulang.GeneralNominalState.Parameter.type (right, right)] →
      ∀ (one : Yulang.GeneralNominalSpineFacts.Spine state names bounds left)
        (two : Yulang.GeneralNominalSpineFacts.Spine state other otherBounds right)
        (model : Yulang.GeneralNominalCommonBridge.Assignment),
        Yulang.GeneralNominalState.Models state model →
          ∀ (origin : Option Yulang.GeneralNominalRecursiveInspection.Origin)
            (pair : Yulang.GeneralNominalInspection.Bounds state),
            pair ∈
                (Yulang.GeneralNominalRecursiveInspection.inspect state
                    (Yulang.GeneralNominalInspection.Query.nominal descriptor.declaration.name [one.query, two.query])
                    (slot, slot) origin).checked →
              Yulang.CommonNominalFullCarrier.Subtype (model (state.base.source pair.fst)).fst
                (model (state.base.source pair.snd)).fst
Yulang.GeneralNominalTreeExample.state_models : Yulang.GeneralNominalState.Models Yulang.GeneralNominalTreeExample.state
  Yulang.GeneralNominalTreeExample.model
Yulang.GeneralNominalTreeExample.checked : Yulang.GeneralDeclarations.DeclarationChecked
  Yulang.GeneralDeclarationExamples.constructors Yulang.GeneralDeclarationExamples.roles
  Yulang.GeneralNominalTreeExample.declaration
Yulang.GeneralNominalTreeExample.actual_branch : Yulang.GeneralNominalRecursiveCandidates.BranchModels
  Yulang.GeneralNominalTreeExample.registry Yulang.GeneralNominalTreeExample.context
  Yulang.GeneralNominalTreeExample.root Yulang.GeneralNominalTreeExample.declaration
  Yulang.GeneralNominalTreeExample.checked [(0, 0)] Yulang.GeneralNominalTreeExample.model
```
