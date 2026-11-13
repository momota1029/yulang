# Cycle155 public theorem types

110 public theorems, exact Lean output.

```text
Yulang.GeneralDictionaryInstalledRequestProvenance.singleton_variables : ∀ (state : Yulang.GeneralNominalState.State)
  (interpretation : Yulang.GeneralNominalInspection.Interpretation)
  (batch : List Yulang.GeneralNominalMaterialization.Request),
  (Yulang.GeneralNominalMaterialization.generated state interpretation batch).variables = [] →
    ∀ (request : Yulang.GeneralNominalMaterialization.Request),
      request ∈ batch → (Yulang.GeneralNominalMaterialization.generated state interpretation [request]).variables = []
@Yulang.GeneralDictionaryInstalledRequestProvenance.packet_covered : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalSaturationState.State roles)
  (packet : Yulang.GeneralNominalSaturationState.Packet roles),
  packet ∈ state.packets →
    ∀ (batch : List Yulang.GeneralNominalMaterialization.Request),
      (∀ (request : Yulang.GeneralNominalMaterialization.Request),
          request ∈ batch →
            request ∈
              Yulang.GeneralNominalMaterialization.requests packet.context.state packet.registry packet.site.occurrence
                packet.declaration ⋯ packet.bindings) →
        (Yulang.GeneralNominalMaterialization.generated packet.context.state packet.context.interpretation
                batch).variables =
            [] →
          Yulang.GeneralDictionaryRecordedBatchModels.Covered state batch
@Yulang.GeneralDictionaryInstalledRequestProvenance.installed_supported : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (before : Yulang.GeneralNominalSupport.Tracked roles) (packet : Yulang.GeneralNominalSaturationState.Packet roles)
  (support : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
  (Yulang.GeneralNominalPacketSupport.namedSchema packet).variables = [] →
    Yulang.GeneralDictionaryRequestProvenance.Supported registry root
      (Yulang.GeneralNominalValueSteps.install before packet support)
      (Yulang.GeneralNominalMaterialization.requests packet.context.state packet.registry packet.site.occurrence
        packet.declaration ⋯ packet.bindings)
@Yulang.GeneralDictionaryInstalledRequestProvenance.supported_install_append : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (before : Yulang.GeneralNominalSupport.Tracked roles) (packet : Yulang.GeneralNominalSaturationState.Packet roles)
  (support : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
  Yulang.GeneralNominalValueSteps.Step registry root before
      (Yulang.GeneralNominalValueSteps.install before packet support) →
    ∀ (batch : List Yulang.GeneralNominalMaterialization.Request),
      Yulang.GeneralDictionaryRequestProvenance.Supported registry root before batch →
        (Yulang.GeneralNominalPacketSupport.namedSchema packet).variables = [] →
          Yulang.GeneralDictionaryRequestProvenance.Supported registry root
            (Yulang.GeneralNominalValueSteps.install before packet support)
            (batch ++
              Yulang.GeneralNominalMaterialization.requests packet.context.state packet.registry packet.site.occurrence
                packet.declaration ⋯ packet.bindings)
Yulang.GeneralDictionaryNonterminalProvenanceApplication.parent_requests : ∀
  (capture : Yulang.GeneralNominalAllocation.Bindings),
  Yulang.GeneralNominalMaterialization.requests
      Yulang.GeneralDictionaryFiniteObservedExampleNonterminalClosure.current.state
      Yulang.GeneralDictionaryFiniteObservedExampleNonterminal.registry
      Yulang.GeneralDictionaryFiniteObservedExampleNonterminal.root
      Yulang.GeneralDictionaryFiniteObservedExampleNonterminal.declaration
      Yulang.GeneralDictionaryFiniteObservedExampleNonterminal.checked capture =
    [Yulang.GeneralDictionaryFiniteObservedExample.request]
Yulang.GeneralDictionaryNonterminalProvenanceApplication.parent_structural : Yulang.GeneralDictionaryProvenanceHeadBranch.Structural
  Yulang.GeneralDictionaryFiniteObservedExampleNonterminal.registry
  Yulang.GeneralDictionaryFiniteObservedExampleNonterminal.root
  Yulang.GeneralDictionaryFiniteObservedExampleNonterminalInstallation.installed
  Yulang.GeneralDictionaryFiniteObservedExampleNonterminal.root
  Yulang.GeneralDictionaryFiniteObservedExampleNonterminal.declaration
  Yulang.GeneralDictionaryFiniteObservedExampleNonterminal.checked
Yulang.GeneralDictionaryNonterminalProvenanceApplication.child_requests : ∀
  (capture : Yulang.GeneralNominalAllocation.Bindings),
  Yulang.GeneralNominalMaterialization.requests
      Yulang.GeneralDictionaryFiniteObservedExampleNonterminalClosure.current.state
      Yulang.GeneralDictionaryFiniteObservedExampleNonterminal.registry
      Yulang.GeneralDictionaryFiniteObservedExampleNonterminalEvidence.child Yulang.GeneralNominalExamples.intDisplay
      Yulang.GeneralDictionaryFiniteObservedExampleNonterminal.int_display_checked capture =
    []
Yulang.GeneralDictionaryNonterminalProvenanceApplication.child_structural : Yulang.GeneralDictionaryProvenanceHeadBranch.Structural
  Yulang.GeneralDictionaryFiniteObservedExampleNonterminal.registry
  Yulang.GeneralDictionaryFiniteObservedExampleNonterminal.root
  Yulang.GeneralDictionaryFiniteObservedExampleNonterminalInstallation.installed
  Yulang.GeneralDictionaryFiniteObservedExampleNonterminalEvidence.child Yulang.GeneralNominalExamples.intDisplay
  Yulang.GeneralDictionaryFiniteObservedExampleNonterminal.int_display_checked
Yulang.GeneralDictionaryNonterminalProvenanceApplication.selected_path_cases : ∀
  (focus : Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles),
  Yulang.GeneralDictionarySelectionPolicy.SelectedPath
      (Yulang.GeneralNominalValueBoundary.boundary Yulang.GeneralDeclarationExamples.roles).toSourceBoundary
      Yulang.GeneralDictionaryFiniteObservedExampleNonterminal.registry
      Yulang.GeneralDictionaryFiniteObservedExampleNonterminalInstallation.installed
      Yulang.GeneralDictionaryFiniteObservedExampleNonterminal.root focus →
    focus = Yulang.GeneralDictionaryFiniteObservedExampleNonterminal.root ∨
      focus = Yulang.GeneralDictionaryFiniteObservedExampleNonterminalEvidence.child
Yulang.GeneralDictionaryNonterminalProvenanceApplication.covered : Yulang.GeneralDictionarySelectedProvenanceCoverage.Covered
  Yulang.GeneralDictionaryFiniteObservedExampleNonterminal.registry
  Yulang.GeneralDictionaryFiniteObservedExampleNonterminal.root
  Yulang.GeneralDictionaryFiniteObservedExampleNonterminalInstallation.installed
Yulang.GeneralDictionaryNonterminalProvenanceApplication.classifier_evidence : ∀
  (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalSaturationState.Models
      Yulang.GeneralDictionaryFiniteObservedExampleNonterminalInstallation.installed.current assignment →
    Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralDictionaryFiniteObservedExampleNonterminal.registry
      Yulang.GeneralDictionaryFiniteObservedExampleNonterminalClosure.current assignment
      Yulang.GeneralDictionaryFiniteObservedExampleNonterminal.root
      Yulang.GeneralDictionaryFiniteObservedExampleNonterminalEvidence.payload
Yulang.GeneralDictionaryNonterminalProvenanceApplication.inhabited_recursive_application : Yulang.GeneralNominalSaturationState.Models
    Yulang.GeneralDictionaryFiniteObservedExampleNonterminalInstallation.installed.current
    Yulang.GeneralDictionaryFiniteObservedExample.model ∧
  Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralDictionaryFiniteObservedExampleNonterminal.registry
      Yulang.GeneralDictionaryFiniteObservedExampleNonterminalClosure.current
      Yulang.GeneralDictionaryFiniteObservedExample.model Yulang.GeneralDictionaryFiniteObservedExampleNonterminal.root
      Yulang.GeneralDictionaryFiniteObservedExampleNonterminalEvidence.payload ∧
    Yulang.GeneralDictionaryFiniteObservedExampleNonterminal.children.length = 1 ∧
      Yulang.GeneralDictionaryFiniteObservedExampleNonterminal.root.demand.outputs ≠ []
@Yulang.GeneralDictionaryProvenanceClassification.dictionary_evidence : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (state : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.B4TargetV5.Reachable (Yulang.GeneralNominalValueBoundary.boundary roles) registry root state →
    Yulang.GeneralDictionaryProvenanceClassification.Covered registry root state →
      ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
        Yulang.GeneralNominalSaturationState.Models state.current model →
          ∀ (dictionary : Yulang.GeneralDictionaryReadback.Payload)
            (focus : Yulang.GeneralSourceDictionaries.Occurrence roles),
            Yulang.B4TargetV3.Classify (Yulang.GeneralNominalValueBoundary.boundary roles).toSourceBoundary registry
                state focus (Yulang.CommonRoleOutermostResolver.Result.selected dictionary) →
              Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context model focus dictionary
@Yulang.GeneralDictionaryProvenanceClassification.dictionaries_evidence : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (state : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.B4TargetV5.Reachable (Yulang.GeneralNominalValueBoundary.boundary roles) registry root state →
    Yulang.GeneralDictionaryProvenanceClassification.Covered registry root state →
      ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
        Yulang.GeneralNominalSaturationState.Models state.current model →
          ∀ (dictionaries : List Yulang.GeneralDictionaryReadback.Payload)
            (focuses : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
            Yulang.CommonRoleOutermostResolver.All₂
                (fun focus dictionary =>
                  Yulang.B4TargetV3.Classify (Yulang.GeneralNominalValueBoundary.boundary roles).toSourceBoundary
                    registry state focus (Yulang.CommonRoleOutermostResolver.Result.selected dictionary))
                focuses dictionaries →
              Yulang.CommonRoleOutermostResolver.All₂
                (Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context model) focuses
                dictionaries
@Yulang.GeneralDictionaryProvenanceHeadBranch.selected_instance : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root focus : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (state : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.B4TargetV5.Reachable (Yulang.GeneralNominalValueBoundary.boundary roles) registry root state →
    ∀ (chosen : Yulang.GeneralDeclarations.Declaration),
      chosen ∈ registry.declarations →
        ∀ (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles chosen),
          Yulang.GeneralDictionaryProvenanceHeadBranch.Structural registry root state focus chosen checked →
            ∀ (key : Nat) (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
              Yulang.GeneralNominalValueBoundary.Local registry state focus
                  (Yulang.CommonRoleOutermostResolver.Frontier.selected key children) →
                ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                  Yulang.GeneralNominalSaturationState.Models state.current model →
                    Yulang.GeneralDictionaryRecursiveEvidence.Instance registry state.current.context model focus key
                      children
@Yulang.GeneralDictionaryProvenanceHeadBranch.node_evidence : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root focus : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (state : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.B4TargetV5.Reachable (Yulang.GeneralNominalValueBoundary.boundary roles) registry root state →
    ∀ (chosen : Yulang.GeneralDeclarations.Declaration),
      chosen ∈ registry.declarations →
        ∀ (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles chosen),
          Yulang.GeneralDictionaryProvenanceHeadBranch.Structural registry root state focus chosen checked →
            ∀ (key : Nat) (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
              Yulang.GeneralNominalValueBoundary.Local registry state focus
                  (Yulang.CommonRoleOutermostResolver.Frontier.selected key children) →
                ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                  Yulang.GeneralNominalSaturationState.Models state.current model →
                    ∀ (dictionaries : List Yulang.GeneralDictionaryReadback.Payload),
                      Yulang.CommonRoleOutermostResolver.All₂
                          (Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context model)
                          children dictionaries →
                        Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context model focus
                          (Yulang.CommonRoleOutermostResolver.Dictionary.node key dictionaries)
@Yulang.GeneralDictionaryProvenanceScalarBranch.report_exact : ∀ {roles : Yulang.Roles.RoleDecls}
  (context : Yulang.GeneralNominalRecursiveCandidates.Context)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (declaration : Yulang.GeneralDeclarations.Declaration)
  (shape : Yulang.GeneralDictionaryProvenanceScalarBranch.Shape context root declaration),
  Yulang.GeneralNominalRecursiveCandidates.report context declaration [(shape.slot, shape.slot)] =
    { inspected := [(shape.slot, shape.slot)], checked := [(shape.slot, shape.slot), (shape.slot, shape.slot)] }
@Yulang.GeneralDictionaryProvenanceScalarBranch.branch_models : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry)
  (saturationRoot root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (state : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.B4TargetV5.Reachable (Yulang.GeneralNominalValueBoundary.boundary roles) registry saturationRoot state →
    ∀ (declaration : Yulang.GeneralDeclarations.Declaration)
      (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
      (shape : Yulang.GeneralDictionaryProvenanceScalarBranch.Shape state.current.context root declaration),
      Yulang.GeneralDictionaryRequestProvenance.Supported registry saturationRoot state
          (Yulang.GeneralNominalMaterialization.requests state.current.context.state registry root declaration checked
            (Yulang.GeneralNominalRecursiveInspection.bindings state.current.context.state
              (Yulang.GeneralNominalRecursiveCandidates.report state.current.context declaration
                [(shape.slot, shape.slot)]))) →
        ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
          Yulang.GeneralNominalSaturationState.Models state.current model →
            Yulang.GeneralNominalRecursiveCandidates.BranchModels registry state.current.context root declaration
              checked [(shape.slot, shape.slot)] model
@Yulang.GeneralDictionaryProvenanceScalarBranch.instance_of_shape : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry)
  (saturationRoot root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (state : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.B4TargetV5.Reachable (Yulang.GeneralNominalValueBoundary.boundary roles) registry saturationRoot state →
    ∀ (declaration : Yulang.GeneralDeclarations.Declaration),
      declaration ∈ registry.declarations →
        ∀ (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
          (shape : Yulang.GeneralDictionaryProvenanceScalarBranch.Shape state.current.context root declaration),
          Yulang.GeneralDictionaryRequestProvenance.Supported registry saturationRoot state
              (Yulang.GeneralNominalMaterialization.requests state.current.context.state registry root declaration
                checked
                (Yulang.GeneralNominalRecursiveInspection.bindings state.current.context.state
                  (Yulang.GeneralNominalRecursiveCandidates.report state.current.context declaration
                    [(shape.slot, shape.slot)]))) →
            Yulang.GeneralNominalRecursiveCandidates.Metadata registry state.current.context →
              ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                Yulang.GeneralNominalSaturationState.Models state.current model →
                  Yulang.GeneralDictionaryRecursiveEvidence.Instance registry state.current.context model root
                    declaration.id
                    (Yulang.GeneralNominalAllocation.children state.current.context.state registry root declaration
                      checked
                      (Yulang.GeneralNominalRecursiveInspection.bindings state.current.context.state
                        (Yulang.GeneralNominalRecursiveCandidates.report state.current.context declaration
                          [(shape.slot, shape.slot)])))
@Yulang.GeneralDictionaryProvenanceScalarBranch.selected_instance : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry)
  (saturationRoot root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (state : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.B4TargetV5.Reachable (Yulang.GeneralNominalValueBoundary.boundary roles) registry saturationRoot state →
    ∀ (declaration : Yulang.GeneralDeclarations.Declaration),
      declaration ∈ registry.declarations →
        ∀ (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
          (shape : Yulang.GeneralDictionaryProvenanceScalarBranch.Shape state.current.context root declaration),
          Yulang.GeneralDictionaryRequestProvenance.Supported registry saturationRoot state
              (Yulang.GeneralNominalMaterialization.requests state.current.context.state registry root declaration
                checked
                (Yulang.GeneralNominalRecursiveInspection.bindings state.current.context.state
                  (Yulang.GeneralNominalRecursiveCandidates.report state.current.context declaration
                    [(shape.slot, shape.slot)]))) →
            ∀ (key : Nat) (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
              Yulang.GeneralNominalValueBoundary.Local registry state root
                  (Yulang.CommonRoleOutermostResolver.Frontier.selected key children) →
                ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                  Yulang.GeneralNominalSaturationState.Models state.current model →
                    Yulang.GeneralDictionaryRecursiveEvidence.Instance registry state.current.context model root key
                      children
@Yulang.GeneralDictionaryProvenanceTreeBranch.branch_models : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry)
  (saturationRoot root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (state : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.B4TargetV5.Reachable (Yulang.GeneralNominalValueBoundary.boundary roles) registry saturationRoot state →
    ∀ (declaration : Yulang.GeneralDeclarations.Declaration)
      (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
      (shape :
        Yulang.GeneralDictionaryHistoricalTreeBranch.Shape state.current.context registry root declaration checked),
      Yulang.GeneralDictionaryRequestProvenance.Supported registry saturationRoot state
          (Yulang.GeneralNominalMaterialization.requests state.current.context.state registry root declaration checked
            (Yulang.GeneralNominalRecursiveInspection.bindings state.current.context.state
              (Yulang.GeneralNominalRecursiveCandidates.report state.current.context declaration
                [(shape.slot, shape.slot)]))) →
        ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
          Yulang.GeneralNominalSaturationState.Models state.current model →
            Yulang.GeneralNominalRecursiveCandidates.BranchModels registry state.current.context root declaration
              checked [(shape.slot, shape.slot)] model
@Yulang.GeneralDictionaryProvenanceTreeBranch.ready : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry)
  (saturationRoot root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (state : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.B4TargetV5.Reachable (Yulang.GeneralNominalValueBoundary.boundary roles) registry saturationRoot state →
    ∀ (declaration : Yulang.GeneralDeclarations.Declaration)
      (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
      (shape :
        Yulang.GeneralDictionaryHistoricalTreeBranch.Shape state.current.context registry root declaration checked),
      Yulang.GeneralDictionaryRequestProvenance.Supported registry saturationRoot state
          (Yulang.GeneralNominalMaterialization.requests state.current.context.state registry root declaration checked
            (Yulang.GeneralNominalRecursiveInspection.bindings state.current.context.state
              (Yulang.GeneralNominalRecursiveCandidates.report state.current.context declaration
                [(shape.slot, shape.slot)]))) →
        Yulang.GeneralNominalRecursiveCandidates.RequestReady registry state.current.context root declaration checked
          [(shape.slot, shape.slot)]
@Yulang.GeneralDictionaryProvenanceTreeBranch.instance_of_shape : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry)
  (saturationRoot root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (state : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.B4TargetV5.Reachable (Yulang.GeneralNominalValueBoundary.boundary roles) registry saturationRoot state →
    ∀ (declaration : Yulang.GeneralDeclarations.Declaration),
      declaration ∈ registry.declarations →
        ∀ (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
          (shape :
            Yulang.GeneralDictionaryHistoricalTreeBranch.Shape state.current.context registry root declaration checked),
          Yulang.GeneralDictionaryRequestProvenance.Supported registry saturationRoot state
              (Yulang.GeneralNominalMaterialization.requests state.current.context.state registry root declaration
                checked
                (Yulang.GeneralNominalRecursiveInspection.bindings state.current.context.state
                  (Yulang.GeneralNominalRecursiveCandidates.report state.current.context declaration
                    [(shape.slot, shape.slot)]))) →
            Yulang.GeneralNominalRecursiveCandidates.Metadata registry state.current.context →
              ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                Yulang.GeneralNominalSaturationState.Models state.current model →
                  Yulang.GeneralDictionaryRecursiveEvidence.Instance registry state.current.context model root
                    declaration.id
                    (Yulang.GeneralNominalAllocation.children state.current.context.state registry root declaration
                      checked
                      (Yulang.GeneralNominalRecursiveInspection.bindings state.current.context.state
                        (Yulang.GeneralNominalRecursiveCandidates.report state.current.context declaration
                          [(shape.slot, shape.slot)])))
@Yulang.GeneralDictionaryProvenanceTreeBranch.selected_instance : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry)
  (saturationRoot root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (state : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.B4TargetV5.Reachable (Yulang.GeneralNominalValueBoundary.boundary roles) registry saturationRoot state →
    ∀ (declaration : Yulang.GeneralDeclarations.Declaration),
      declaration ∈ registry.declarations →
        ∀ (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
          (shape :
            Yulang.GeneralDictionaryHistoricalTreeBranch.Shape state.current.context registry root declaration checked),
          Yulang.GeneralDictionaryRequestProvenance.Supported registry saturationRoot state
              (Yulang.GeneralNominalMaterialization.requests state.current.context.state registry root declaration
                checked
                (Yulang.GeneralNominalRecursiveInspection.bindings state.current.context.state
                  (Yulang.GeneralNominalRecursiveCandidates.report state.current.context declaration
                    [(shape.slot, shape.slot)]))) →
            ∀ (key : Nat) (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
              Yulang.GeneralNominalFeedbackK2.Local registry state.current root
                  (Yulang.CommonRoleOutermostResolver.Frontier.selected key children) →
                ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                  Yulang.GeneralNominalSaturationState.Models state.current model →
                    declaration.id = key ∧
                      Yulang.GeneralDictionaryRecursiveEvidence.Instance registry state.current.context model root key
                        children
@Yulang.GeneralDictionaryProvenanceTreeBranch.selected_branch : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry)
  (saturationRoot root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (state : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.B4TargetV5.Reachable (Yulang.GeneralNominalValueBoundary.boundary roles) registry saturationRoot state →
    ∀ (declaration : Yulang.GeneralDeclarations.Declaration),
      declaration ∈ registry.declarations →
        ∀ (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
          (shape :
            Yulang.GeneralDictionaryHistoricalTreeBranch.Shape state.current.context registry root declaration checked),
          Yulang.GeneralDictionaryRequestProvenance.Supported registry saturationRoot state
              (Yulang.GeneralNominalMaterialization.requests state.current.context.state registry root declaration
                checked
                (Yulang.GeneralNominalRecursiveInspection.bindings state.current.context.state
                  (Yulang.GeneralNominalRecursiveCandidates.report state.current.context declaration
                    [(shape.slot, shape.slot)]))) →
            ∀ (key : Nat) (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
              Yulang.GeneralNominalFeedbackK2.Local registry state.current root
                  (Yulang.CommonRoleOutermostResolver.Frontier.selected key children) →
                ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                  Yulang.GeneralNominalSaturationState.Models state.current model →
                    declaration.id = key ∧
                      Yulang.GeneralNominalJointCandidates.BranchAt registry state.current root declaration.id model
@Yulang.GeneralDictionaryProvenanceTreeBranch.value_node_evidence : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry)
  (saturationRoot root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (state : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.B4TargetV5.Reachable (Yulang.GeneralNominalValueBoundary.boundary roles) registry saturationRoot state →
    ∀ (declaration : Yulang.GeneralDeclarations.Declaration),
      declaration ∈ registry.declarations →
        ∀ (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
          (shape :
            Yulang.GeneralDictionaryHistoricalTreeBranch.Shape state.current.context registry root declaration checked),
          Yulang.GeneralDictionaryRequestProvenance.Supported registry saturationRoot state
              (Yulang.GeneralNominalMaterialization.requests state.current.context.state registry root declaration
                checked
                (Yulang.GeneralNominalRecursiveInspection.bindings state.current.context.state
                  (Yulang.GeneralNominalRecursiveCandidates.report state.current.context declaration
                    [(shape.slot, shape.slot)]))) →
            ∀ (key : Nat) (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
              Yulang.GeneralNominalValueBoundary.Local registry state root
                  (Yulang.CommonRoleOutermostResolver.Frontier.selected key children) →
                ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                  Yulang.GeneralNominalSaturationState.Models state.current model →
                    ∀ (dictionaries : List Yulang.GeneralDictionaryReadback.Payload),
                      Yulang.CommonRoleOutermostResolver.All₂
                          (Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context model)
                          children dictionaries →
                        Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context model root
                          (Yulang.CommonRoleOutermostResolver.Dictionary.node key dictionaries)
@Yulang.GeneralDictionaryRecordedBatchModels.covered_nil : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalSaturationState.State roles),
  Yulang.GeneralDictionaryRecordedBatchModels.Covered state []
@Yulang.GeneralDictionaryRecordedBatchModels.covered_append : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalSaturationState.State roles)
  (first last : List Yulang.GeneralNominalMaterialization.Request),
  Yulang.GeneralDictionaryRecordedBatchModels.Covered state (first ++ last) ↔
    Yulang.GeneralDictionaryRecordedBatchModels.Covered state first ∧
      Yulang.GeneralDictionaryRecordedBatchModels.Covered state last
Yulang.GeneralDictionaryRecordedBatchModels.generated_cons : ∀ (state : Yulang.GeneralNominalState.State)
  (interpretation : Yulang.GeneralNominalInspection.Interpretation)
  (request : Yulang.GeneralNominalMaterialization.Request) (rest : List Yulang.GeneralNominalMaterialization.Request),
  Yulang.GeneralNominalMaterialization.generated state interpretation (request :: rest) =
    (Yulang.GeneralNominalMaterialization.generated state interpretation [request]).append
      (Yulang.GeneralNominalMaterialization.generated state interpretation rest)
@Yulang.GeneralDictionaryRecordedBatchModels.reachable_shape : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (state : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.B4TargetV5.Reachable (Yulang.GeneralNominalValueBoundary.boundary roles) registry root state →
    ∀ (batch : List Yulang.GeneralNominalMaterialization.Request),
      Yulang.GeneralDictionaryRecordedBatchModels.Covered state.current batch →
        (Yulang.GeneralNominalMaterialization.generated state.current.context.state state.current.context.interpretation
                batch).variables =
            [] ∧
          (Yulang.GeneralNominalMaterialization.generated state.current.context.state
                state.current.context.interpretation batch).unknown =
            false
@Yulang.GeneralDictionaryRecordedBatchModels.reachable_models : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (state : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.B4TargetV5.Reachable (Yulang.GeneralNominalValueBoundary.boundary roles) registry root state →
    ∀ (batch : List Yulang.GeneralNominalMaterialization.Request),
      Yulang.GeneralDictionaryRecordedBatchModels.Covered state.current batch →
        ∀ (declaration : Yulang.GeneralDeclarations.Declaration) (capture : Yulang.GeneralDeclarationDemands.Capture)
          (report : Yulang.GeneralNominalRecursiveInspection.Report state.current.context.state)
          (model : Yulang.GeneralNominalCommonBridge.Assignment),
          Yulang.GeneralNominalSaturationState.Models state.current model →
            Yulang.GeneralNominalMaterialization.Models state.current.context.state declaration capture report
              (Yulang.GeneralNominalMaterialization.generated state.current.context.state
                state.current.context.interpretation batch)
              model
@Yulang.GeneralDictionaryRecordedTreeBranch.branch_models : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry)
  (saturationRoot root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (state : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.B4TargetV5.Reachable (Yulang.GeneralNominalValueBoundary.boundary roles) registry saturationRoot state →
    ∀ (declaration : Yulang.GeneralDeclarations.Declaration)
      (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
      (shape :
        Yulang.GeneralDictionaryHistoricalTreeBranch.Shape state.current.context registry root declaration checked),
      Yulang.GeneralDictionaryRecordedBatchModels.Covered state.current
          (Yulang.GeneralNominalMaterialization.requests state.current.context.state registry root declaration checked
            (Yulang.GeneralNominalRecursiveInspection.bindings state.current.context.state
              (Yulang.GeneralNominalRecursiveCandidates.report state.current.context declaration
                [(shape.slot, shape.slot)]))) →
        ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
          Yulang.GeneralNominalSaturationState.Models state.current model →
            Yulang.GeneralNominalRecursiveCandidates.BranchModels registry state.current.context root declaration
              checked [(shape.slot, shape.slot)] model
@Yulang.GeneralDictionaryRecordedTreeBranch.ready : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry)
  (saturationRoot root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (state : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.B4TargetV5.Reachable (Yulang.GeneralNominalValueBoundary.boundary roles) registry saturationRoot state →
    ∀ (declaration : Yulang.GeneralDeclarations.Declaration)
      (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
      (shape :
        Yulang.GeneralDictionaryHistoricalTreeBranch.Shape state.current.context registry root declaration checked),
      Yulang.GeneralDictionaryRecordedBatchModels.Covered state.current
          (Yulang.GeneralNominalMaterialization.requests state.current.context.state registry root declaration checked
            (Yulang.GeneralNominalRecursiveInspection.bindings state.current.context.state
              (Yulang.GeneralNominalRecursiveCandidates.report state.current.context declaration
                [(shape.slot, shape.slot)]))) →
        Yulang.GeneralNominalRecursiveCandidates.RequestReady registry state.current.context root declaration checked
          [(shape.slot, shape.slot)]
@Yulang.GeneralDictionaryRecordedTreeBranch.instance_of_shape : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry)
  (saturationRoot root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (state : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.B4TargetV5.Reachable (Yulang.GeneralNominalValueBoundary.boundary roles) registry saturationRoot state →
    ∀ (declaration : Yulang.GeneralDeclarations.Declaration),
      declaration ∈ registry.declarations →
        ∀ (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
          (shape :
            Yulang.GeneralDictionaryHistoricalTreeBranch.Shape state.current.context registry root declaration checked),
          Yulang.GeneralDictionaryRecordedBatchModels.Covered state.current
              (Yulang.GeneralNominalMaterialization.requests state.current.context.state registry root declaration
                checked
                (Yulang.GeneralNominalRecursiveInspection.bindings state.current.context.state
                  (Yulang.GeneralNominalRecursiveCandidates.report state.current.context declaration
                    [(shape.slot, shape.slot)]))) →
            Yulang.GeneralNominalRecursiveCandidates.Metadata registry state.current.context →
              ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                Yulang.GeneralNominalSaturationState.Models state.current model →
                  Yulang.GeneralDictionaryRecursiveEvidence.Instance registry state.current.context model root
                    declaration.id
                    (Yulang.GeneralNominalAllocation.children state.current.context.state registry root declaration
                      checked
                      (Yulang.GeneralNominalRecursiveInspection.bindings state.current.context.state
                        (Yulang.GeneralNominalRecursiveCandidates.report state.current.context declaration
                          [(shape.slot, shape.slot)])))
@Yulang.GeneralDictionaryRecordedTreeBranch.selected_instance : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry)
  (saturationRoot root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (state : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.B4TargetV5.Reachable (Yulang.GeneralNominalValueBoundary.boundary roles) registry saturationRoot state →
    ∀ (declaration : Yulang.GeneralDeclarations.Declaration),
      declaration ∈ registry.declarations →
        ∀ (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
          (shape :
            Yulang.GeneralDictionaryHistoricalTreeBranch.Shape state.current.context registry root declaration checked),
          Yulang.GeneralDictionaryRecordedBatchModels.Covered state.current
              (Yulang.GeneralNominalMaterialization.requests state.current.context.state registry root declaration
                checked
                (Yulang.GeneralNominalRecursiveInspection.bindings state.current.context.state
                  (Yulang.GeneralNominalRecursiveCandidates.report state.current.context declaration
                    [(shape.slot, shape.slot)]))) →
            ∀ (key : Nat) (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
              Yulang.GeneralNominalFeedbackK2.Local registry state.current root
                  (Yulang.CommonRoleOutermostResolver.Frontier.selected key children) →
                ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                  Yulang.GeneralNominalSaturationState.Models state.current model →
                    declaration.id = key ∧
                      Yulang.GeneralDictionaryRecursiveEvidence.Instance registry state.current.context model root key
                        children
@Yulang.GeneralDictionaryRecordedTreeBranch.selected_branch : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry)
  (saturationRoot root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (state : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.B4TargetV5.Reachable (Yulang.GeneralNominalValueBoundary.boundary roles) registry saturationRoot state →
    ∀ (declaration : Yulang.GeneralDeclarations.Declaration),
      declaration ∈ registry.declarations →
        ∀ (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
          (shape :
            Yulang.GeneralDictionaryHistoricalTreeBranch.Shape state.current.context registry root declaration checked),
          Yulang.GeneralDictionaryRecordedBatchModels.Covered state.current
              (Yulang.GeneralNominalMaterialization.requests state.current.context.state registry root declaration
                checked
                (Yulang.GeneralNominalRecursiveInspection.bindings state.current.context.state
                  (Yulang.GeneralNominalRecursiveCandidates.report state.current.context declaration
                    [(shape.slot, shape.slot)]))) →
            ∀ (key : Nat) (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
              Yulang.GeneralNominalFeedbackK2.Local registry state.current root
                  (Yulang.CommonRoleOutermostResolver.Frontier.selected key children) →
                ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                  Yulang.GeneralNominalSaturationState.Models state.current model →
                    declaration.id = key ∧
                      Yulang.GeneralNominalJointCandidates.BranchAt registry state.current root declaration.id model
@Yulang.GeneralDictionaryRecordedTreeBranch.value_node_evidence : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry)
  (saturationRoot root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (state : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.B4TargetV5.Reachable (Yulang.GeneralNominalValueBoundary.boundary roles) registry saturationRoot state →
    ∀ (declaration : Yulang.GeneralDeclarations.Declaration),
      declaration ∈ registry.declarations →
        ∀ (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
          (shape :
            Yulang.GeneralDictionaryHistoricalTreeBranch.Shape state.current.context registry root declaration checked),
          Yulang.GeneralDictionaryRecordedBatchModels.Covered state.current
              (Yulang.GeneralNominalMaterialization.requests state.current.context.state registry root declaration
                checked
                (Yulang.GeneralNominalRecursiveInspection.bindings state.current.context.state
                  (Yulang.GeneralNominalRecursiveCandidates.report state.current.context declaration
                    [(shape.slot, shape.slot)]))) →
            ∀ (key : Nat) (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
              Yulang.GeneralNominalValueBoundary.Local registry state root
                  (Yulang.CommonRoleOutermostResolver.Frontier.selected key children) →
                ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                  Yulang.GeneralNominalSaturationState.Models state.current model →
                    ∀ (dictionaries : List Yulang.GeneralDictionaryReadback.Payload),
                      Yulang.CommonRoleOutermostResolver.All₂
                          (Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context model)
                          children dictionaries →
                        Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context model root
                          (Yulang.CommonRoleOutermostResolver.Dictionary.node key dictionaries)
Yulang.GeneralDictionaryRequestBatchAssembly.shape_of_singletons : ∀ (state : Yulang.GeneralNominalState.State)
  (interpretation : Yulang.GeneralNominalInspection.Interpretation)
  (batch : List Yulang.GeneralNominalMaterialization.Request),
  (∀ (request : Yulang.GeneralNominalMaterialization.Request),
      request ∈ batch →
        (Yulang.GeneralNominalMaterialization.generated state interpretation [request]).variables = [] ∧
          (Yulang.GeneralNominalMaterialization.generated state interpretation [request]).unknown = false) →
    (Yulang.GeneralNominalMaterialization.generated state interpretation batch).variables = [] ∧
      (Yulang.GeneralNominalMaterialization.generated state interpretation batch).unknown = false
Yulang.GeneralDictionaryRequestBatchAssembly.variables_of_singletons : ∀ (state : Yulang.GeneralNominalState.State)
  (interpretation : Yulang.GeneralNominalInspection.Interpretation)
  (batch : List Yulang.GeneralNominalMaterialization.Request),
  (∀ (request : Yulang.GeneralNominalMaterialization.Request),
      request ∈ batch →
        (Yulang.GeneralNominalMaterialization.generated state interpretation [request]).variables = []) →
    (Yulang.GeneralNominalMaterialization.generated state interpretation batch).variables = []
Yulang.GeneralDictionaryRequestBatchAssembly.models_of_singletons : ∀ (state : Yulang.GeneralNominalState.State)
  (interpretation : Yulang.GeneralNominalInspection.Interpretation)
  (batch : List Yulang.GeneralNominalMaterialization.Request) (declaration : Yulang.GeneralDeclarations.Declaration)
  (capture : Yulang.GeneralDeclarationDemands.Capture) (report : Yulang.GeneralNominalRecursiveInspection.Report state)
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  (∀ (request : Yulang.GeneralNominalMaterialization.Request),
      request ∈ batch →
        (Yulang.GeneralNominalMaterialization.generated state interpretation [request]).variables = [] ∧
          Yulang.GeneralNominalMaterialization.Models state declaration capture report
            (Yulang.GeneralNominalMaterialization.generated state interpretation [request]) model) →
    Yulang.GeneralNominalMaterialization.Models state declaration capture report
      (Yulang.GeneralNominalMaterialization.generated state interpretation batch) model
@Yulang.GeneralDictionaryRequestProvenance.supported_of_recorded : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (state : Yulang.GeneralNominalSupport.Tracked roles) (batch : List Yulang.GeneralNominalMaterialization.Request),
  Yulang.GeneralDictionaryRecordedBatchModels.Covered state.current batch →
    Yulang.GeneralDictionaryRequestProvenance.Supported registry root state batch
@Yulang.GeneralDictionaryRequestProvenance.supported_of_observed : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (before after : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.B4TargetV5.Reachable (Yulang.GeneralNominalValueBoundary.boundary roles) registry root before →
    Yulang.B4Target.Steps (Yulang.GeneralNominalValueSteps.Step registry root) before after →
      ∀ (batch : List Yulang.GeneralNominalMaterialization.Request),
        Yulang.GeneralDictionaryObservedFiniteRequests.Observed before.current.context.state
            before.current.context.interpretation batch →
          Yulang.GeneralDictionaryRequestProvenance.Supported registry root after batch
@Yulang.GeneralDictionaryRequestProvenance.supported_append : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (state : Yulang.GeneralNominalSupport.Tracked roles) (first last : List Yulang.GeneralNominalMaterialization.Request),
  Yulang.GeneralDictionaryRequestProvenance.Supported registry root state (first ++ last) ↔
    Yulang.GeneralDictionaryRequestProvenance.Supported registry root state first ∧
      Yulang.GeneralDictionaryRequestProvenance.Supported registry root state last
@Yulang.GeneralDictionaryRequestProvenance.shape : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (state : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.B4TargetV5.Reachable (Yulang.GeneralNominalValueBoundary.boundary roles) registry root state →
    ∀ (batch : List Yulang.GeneralNominalMaterialization.Request),
      Yulang.GeneralDictionaryRequestProvenance.Supported registry root state batch →
        (Yulang.GeneralNominalMaterialization.generated state.current.context.state state.current.context.interpretation
                batch).variables =
            [] ∧
          (Yulang.GeneralNominalMaterialization.generated state.current.context.state
                state.current.context.interpretation batch).unknown =
            false
@Yulang.GeneralDictionaryRequestProvenance.models : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (state : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.B4TargetV5.Reachable (Yulang.GeneralNominalValueBoundary.boundary roles) registry root state →
    ∀ (batch : List Yulang.GeneralNominalMaterialization.Request),
      Yulang.GeneralDictionaryRequestProvenance.Supported registry root state batch →
        ∀ (declaration : Yulang.GeneralDeclarations.Declaration) (capture : Yulang.GeneralDeclarationDemands.Capture)
          (report : Yulang.GeneralNominalRecursiveInspection.Report state.current.context.state)
          (model : Yulang.GeneralNominalCommonBridge.Assignment),
          Yulang.GeneralNominalSaturationState.Models state.current model →
            Yulang.GeneralNominalMaterialization.Models state.current.context.state declaration capture report
              (Yulang.GeneralNominalMaterialization.generated state.current.context.state
                state.current.context.interpretation batch)
              model
@Yulang.GeneralDictionaryRequestProvenanceTrace.recorded_step : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (before after : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.GeneralNominalValueSteps.Step registry root before after →
    ∀ (batch : List Yulang.GeneralNominalMaterialization.Request),
      Yulang.GeneralDictionaryRecordedBatchModels.Covered before.current batch →
        Yulang.GeneralDictionaryRecordedBatchModels.Covered after.current batch
@Yulang.GeneralDictionaryRequestProvenanceTrace.supported_step : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (before after : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.GeneralNominalValueSteps.Step registry root before after →
    ∀ (batch : List Yulang.GeneralNominalMaterialization.Request),
      Yulang.GeneralDictionaryRequestProvenance.Supported registry root before batch →
        Yulang.GeneralDictionaryRequestProvenance.Supported registry root after batch
@Yulang.GeneralDictionaryRequestProvenanceTrace.supported_trace : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (before after : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.B4Target.Steps (Yulang.GeneralNominalValueSteps.Step registry root) before after →
    ∀ (batch : List Yulang.GeneralNominalMaterialization.Request),
      Yulang.GeneralDictionaryRequestProvenance.Supported registry root before batch →
        Yulang.GeneralDictionaryRequestProvenance.Supported registry root after batch
@Yulang.GeneralDictionaryRequestProvenanceTrace.reachable_trace : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (before after : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.B4TargetV5.Reachable (Yulang.GeneralNominalValueBoundary.boundary roles) registry root before →
    Yulang.B4Target.Steps (Yulang.GeneralNominalValueSteps.Step registry root) before after →
      Yulang.B4TargetV5.Reachable (Yulang.GeneralNominalValueBoundary.boundary roles) registry root after
@Yulang.GeneralDictionaryRequestProvenanceTrace.models_after_trace : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (before after : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.B4TargetV5.Reachable (Yulang.GeneralNominalValueBoundary.boundary roles) registry root before →
    Yulang.B4Target.Steps (Yulang.GeneralNominalValueSteps.Step registry root) before after →
      ∀ (batch : List Yulang.GeneralNominalMaterialization.Request),
        Yulang.GeneralDictionaryRequestProvenance.Supported registry root before batch →
          ∀ (declaration : Yulang.GeneralDeclarations.Declaration) (capture : Yulang.GeneralDeclarationDemands.Capture)
            (report : Yulang.GeneralNominalRecursiveInspection.Report after.current.context.state)
            (model : Yulang.GeneralNominalCommonBridge.Assignment),
            Yulang.GeneralNominalSaturationState.Models after.current model →
              Yulang.GeneralNominalMaterialization.Models after.current.context.state declaration capture report
                (Yulang.GeneralNominalMaterialization.generated after.current.context.state
                  after.current.context.interpretation batch)
                model
Yulang.GeneralDictionaryReservedClassifierSoundness.current_requests_exact : ∀
  (capture : Yulang.GeneralNominalAllocation.Bindings),
  Yulang.GeneralNominalMaterialization.requests Yulang.GeneralDictionaryReservedInstalledClassification.current.state
      Yulang.GeneralDictionaryFiniteObservedExample.registry Yulang.GeneralDictionaryFiniteObservedExampleReserved.root
      Yulang.GeneralDictionaryFiniteObservedExample.declaration Yulang.GeneralDictionaryFiniteObservedExample.checked
      capture =
    [Yulang.GeneralDictionaryFiniteObservedExampleReserved.request]
Yulang.GeneralDictionaryReservedClassifierSoundness.structural : Yulang.GeneralDictionaryProvenanceHeadBranch.Structural
  Yulang.GeneralDictionaryFiniteObservedExample.registry Yulang.GeneralDictionaryFiniteObservedExampleReserved.root
  Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.installed
  Yulang.GeneralDictionaryFiniteObservedExampleReserved.root Yulang.GeneralDictionaryFiniteObservedExample.declaration
  Yulang.GeneralDictionaryFiniteObservedExample.checked
Yulang.GeneralDictionaryReservedClassifierSoundness.selected_path_root : ∀
  (focus : Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles),
  Yulang.GeneralDictionarySelectionPolicy.SelectedPath
      (Yulang.GeneralNominalValueBoundary.boundary Yulang.GeneralDeclarationExamples.roles).toSourceBoundary
      Yulang.GeneralDictionaryFiniteObservedExample.registry
      Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.installed
      Yulang.GeneralDictionaryFiniteObservedExampleReserved.root focus →
    focus = Yulang.GeneralDictionaryFiniteObservedExampleReserved.root
Yulang.GeneralDictionaryReservedClassifierSoundness.covered : Yulang.GeneralDictionarySelectedProvenanceCoverage.Covered
  Yulang.GeneralDictionaryFiniteObservedExample.registry Yulang.GeneralDictionaryFiniteObservedExampleReserved.root
  Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.installed
Yulang.GeneralDictionaryReservedClassifierSoundness.classifier_evidence : ∀
  (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalSaturationState.Models
      Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.installed.current assignment →
    Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralDictionaryFiniteObservedExample.registry
      Yulang.GeneralDictionaryReservedInstalledClassification.current assignment
      Yulang.GeneralDictionaryFiniteObservedExampleReserved.root
      (Yulang.CommonRoleOutermostResolver.Dictionary.node Yulang.GeneralDictionaryFiniteObservedExample.declaration.id
        [])
Yulang.GeneralDictionaryReservedClassifierSoundness.inhabited_classifier_evidence : Yulang.GeneralDictionaryRecursiveEvidence.Evidence
    Yulang.GeneralDictionaryFiniteObservedExample.registry
    Yulang.GeneralDictionaryReservedInstalledClassification.current
    Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.positive
    Yulang.GeneralDictionaryFiniteObservedExampleReserved.root
    (Yulang.CommonRoleOutermostResolver.Dictionary.node Yulang.GeneralDictionaryFiniteObservedExample.declaration.id
      []) ∧
  ¬Yulang.GeneralNominalValueSteps.Stable Yulang.GeneralDictionaryFiniteObservedExample.registry
      Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.installed
      Yulang.GeneralDictionaryFiniteObservedExampleReserved.root
Yulang.GeneralDictionaryReservedEqualityStep.raw_countermodel : Yulang.GeneralNominalState.Models
  Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.installed.current.context.state
  Yulang.GeneralDictionaryFiniteObservedExample.model
Yulang.GeneralDictionaryReservedEqualityStep.not_raw_equal : ¬Yulang.GeneralNominalFeedbackSteps.RawEqual
    Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.installed.current 2 0
Yulang.GeneralDictionaryReservedEqualityStep.equality_step : Yulang.GeneralNominalValueSteps.Step
  Yulang.GeneralDictionaryFiniteObservedExample.registry Yulang.GeneralDictionaryFiniteObservedExampleReserved.root
  Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.installed
  Yulang.GeneralDictionaryReservedEqualityStep.after
Yulang.GeneralDictionaryReservedEqualityStep.installed_not_stable : ¬Yulang.GeneralNominalValueSteps.Stable
    Yulang.GeneralDictionaryFiniteObservedExample.registry
    Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.installed
    Yulang.GeneralDictionaryFiniteObservedExampleReserved.root
Yulang.GeneralDictionaryReservedEqualityStep.models_iff : ∀ (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryReservedEqualityStep.after.current assignment ↔
    Yulang.GeneralNominalSaturationState.Models
      Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.installed.current assignment
Yulang.GeneralDictionaryReservedEqualityStep.reachable : Yulang.B4TargetV5.Reachable
  (Yulang.GeneralNominalValueBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
  Yulang.GeneralDictionaryFiniteObservedExample.registry Yulang.GeneralDictionaryFiniteObservedExampleReserved.root
  Yulang.GeneralDictionaryReservedEqualityStep.after
Yulang.GeneralDictionaryReservedEqualityStep.final_evidence : ∀
  (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryReservedEqualityStep.after.current assignment →
    Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralDictionaryFiniteObservedExample.registry
      Yulang.GeneralDictionaryReservedEqualityStep.after.current.context assignment
      Yulang.GeneralDictionaryFiniteObservedExampleReserved.root
      (Yulang.CommonRoleOutermostResolver.Dictionary.node Yulang.GeneralDictionaryFiniteObservedExample.declaration.id
        [])
Yulang.GeneralDictionaryReservedEqualityStep.reachable_dictionary_after_feedback : Yulang.B4TargetV5.Reachable
    (Yulang.GeneralNominalValueBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
    Yulang.GeneralDictionaryFiniteObservedExample.registry Yulang.GeneralDictionaryFiniteObservedExampleReserved.root
    Yulang.GeneralDictionaryReservedEqualityStep.after ∧
  Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryReservedEqualityStep.after.current
      Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.positive ∧
    ∀ (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryReservedEqualityStep.after.current
          assignment →
        Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralDictionaryFiniteObservedExample.registry
          Yulang.GeneralDictionaryReservedEqualityStep.after.current.context assignment
          Yulang.GeneralDictionaryFiniteObservedExampleReserved.root
          (Yulang.CommonRoleOutermostResolver.Dictionary.node
            Yulang.GeneralDictionaryFiniteObservedExample.declaration.id [])
Yulang.GeneralDictionaryReservedInstalledClassification.selected : Yulang.GeneralNominalFeedbackK2.Local
  Yulang.GeneralDictionaryFiniteObservedExample.registry
  Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.installed.current
  Yulang.GeneralDictionaryFiniteObservedExampleReserved.root
  (Yulang.CommonRoleOutermostResolver.Frontier.selected Yulang.GeneralDictionaryFiniteObservedExample.declaration.id [])
Yulang.GeneralDictionaryReservedInstalledClassification.decisions : Yulang.GeneralNominalSupport.DecisionGuard
  Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.installed
  Yulang.GeneralDictionaryFiniteObservedExample.registry Yulang.GeneralDictionaryFiniteObservedExampleReserved.root []
Yulang.GeneralDictionaryReservedInstalledClassification.value_selected : Yulang.GeneralNominalValueBoundary.Local
  Yulang.GeneralDictionaryFiniteObservedExample.registry
  Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.installed
  Yulang.GeneralDictionaryFiniteObservedExampleReserved.root
  (Yulang.CommonRoleOutermostResolver.Frontier.selected Yulang.GeneralDictionaryFiniteObservedExample.declaration.id [])
Yulang.GeneralDictionaryReservedInstalledClassification.classified : Yulang.B4TargetV3.Classify
  (Yulang.GeneralNominalValueBoundary.boundary Yulang.GeneralDeclarationExamples.roles).toSourceBoundary
  Yulang.GeneralDictionaryFiniteObservedExample.registry
  Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.installed
  Yulang.GeneralDictionaryFiniteObservedExampleReserved.root
  (Yulang.CommonRoleOutermostResolver.Result.selected
    (Yulang.CommonRoleOutermostResolver.Dictionary.node Yulang.GeneralDictionaryFiniteObservedExample.declaration.id
      []))
Yulang.GeneralDictionaryReservedInstalledClassification.selected_not_yet_stable : Yulang.B4TargetV3.Classify
    (Yulang.GeneralNominalValueBoundary.boundary Yulang.GeneralDeclarationExamples.roles).toSourceBoundary
    Yulang.GeneralDictionaryFiniteObservedExample.registry
    Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.installed
    Yulang.GeneralDictionaryFiniteObservedExampleReserved.root
    (Yulang.CommonRoleOutermostResolver.Result.selected
      (Yulang.CommonRoleOutermostResolver.Dictionary.node Yulang.GeneralDictionaryFiniteObservedExample.declaration.id
        [])) ∧
  ¬Yulang.GeneralNominalValueSteps.Stable Yulang.GeneralDictionaryFiniteObservedExample.registry
        Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.installed
        Yulang.GeneralDictionaryFiniteObservedExampleReserved.root ∧
    ∀ (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.GeneralNominalSaturationState.Models
          Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.installed.current assignment →
        Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralDictionaryFiniteObservedExample.registry
          Yulang.GeneralDictionaryReservedInstalledClassification.current assignment
          Yulang.GeneralDictionaryFiniteObservedExampleReserved.root
          (Yulang.CommonRoleOutermostResolver.Dictionary.node
            Yulang.GeneralDictionaryFiniteObservedExample.declaration.id [])
Yulang.GeneralDictionaryReservedInstalledEvidence.current_instance : ∀
  (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalSaturationState.Models
      Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.installed.current assignment →
    Yulang.GeneralDictionaryRecursiveEvidence.Instance Yulang.GeneralDictionaryFiniteObservedExample.registry
      Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.installed.current.context assignment
      Yulang.GeneralDictionaryFiniteObservedExampleReserved.root
      Yulang.GeneralDictionaryFiniteObservedExample.declaration.id []
Yulang.GeneralDictionaryReservedInstalledEvidence.current_evidence : ∀
  (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalSaturationState.Models
      Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.installed.current assignment →
    Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralDictionaryFiniteObservedExample.registry
      Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.installed.current.context assignment
      Yulang.GeneralDictionaryFiniteObservedExampleReserved.root
      (Yulang.CommonRoleOutermostResolver.Dictionary.node Yulang.GeneralDictionaryFiniteObservedExample.declaration.id
        [])
Yulang.GeneralDictionaryReservedInstalledEvidence.ordinary_continuation_evidence : ∀
  (after : Yulang.GeneralNominalSaturationState.State Yulang.GeneralDeclarationExamples.roles),
  Yulang.B4Target.Steps
      (Yulang.GeneralDictionaryOrdinaryTrace.OrdinaryStep Yulang.GeneralDictionaryFiniteObservedExample.registry
        Yulang.GeneralDictionaryFiniteObservedExampleReserved.root)
      Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.installed.current after →
    ∀ (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.GeneralNominalSaturationState.Models after assignment →
        Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralDictionaryFiniteObservedExample.registry
          after.context assignment Yulang.GeneralDictionaryFiniteObservedExampleReserved.root
          (Yulang.CommonRoleOutermostResolver.Dictionary.node
            Yulang.GeneralDictionaryFiniteObservedExample.declaration.id [])
Yulang.GeneralDictionaryReservedInstalledEvidence.actual_reserved_dictionary : Yulang.GeneralNominalValueSteps.Step
    Yulang.GeneralDictionaryFiniteObservedExample.registry Yulang.GeneralDictionaryFiniteObservedExampleReserved.root
    Yulang.GeneralDictionaryFiniteObservedExampleReserved.start
    Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.installed ∧
  Yulang.B4TargetV5.Reachable (Yulang.GeneralNominalValueBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
      Yulang.GeneralDictionaryFiniteObservedExample.registry Yulang.GeneralDictionaryFiniteObservedExampleReserved.root
      Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.installed ∧
    Yulang.GeneralNominalSaturationState.Models
        Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.installed.current
        Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.positive ∧
      (¬∃ slot, Yulang.GeneralDictionaryFiniteObservedExampleReserved.state.base.source slot = 2) ∧
        ∀ (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
          Yulang.GeneralNominalSaturationState.Models
              Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.installed.current assignment →
            Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralDictionaryFiniteObservedExample.registry
              Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.installed.current.context assignment
              Yulang.GeneralDictionaryFiniteObservedExampleReserved.root
              (Yulang.CommonRoleOutermostResolver.Dictionary.node
                Yulang.GeneralDictionaryFiniteObservedExample.declaration.id [])
Yulang.GeneralDictionaryReservedMixedProvenance.source_observed : Yulang.GeneralDictionaryObservedFiniteRequests.Observed
  Yulang.GeneralDictionaryFiniteObservedExampleReserved.state
  Yulang.GeneralDictionaryFiniteObservedExample.interpretation
  [Yulang.GeneralDictionaryReservedMixedProvenance.original]
Yulang.GeneralDictionaryReservedMixedProvenance.reserved_covered : Yulang.GeneralDictionaryRecordedBatchModels.Covered
  Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.installed.current
  [Yulang.GeneralDictionaryFiniteObservedExampleReserved.request]
Yulang.GeneralDictionaryReservedMixedProvenance.supported : Yulang.GeneralDictionaryRequestProvenance.Supported
  Yulang.GeneralDictionaryFiniteObservedExample.registry Yulang.GeneralDictionaryFiniteObservedExampleReserved.root
  Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.installed
  Yulang.GeneralDictionaryReservedMixedProvenance.batch
Yulang.GeneralDictionaryReservedMixedProvenance.installed_batch_models : ∀
  (capture : Yulang.GeneralDeclarationDemands.Capture)
  (report :
    Yulang.GeneralNominalRecursiveInspection.Report
      Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.installed.current.context.state)
  (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalSaturationState.Models
      Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.installed.current assignment →
    Yulang.GeneralNominalMaterialization.Models
      Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.installed.current.context.state
      Yulang.GeneralDictionaryFiniteObservedExample.declaration capture report
      (Yulang.GeneralNominalMaterialization.generated
        Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.installed.current.context.state
        Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.installed.current.context.interpretation
        Yulang.GeneralDictionaryReservedMixedProvenance.batch)
      assignment
Yulang.GeneralDictionaryReservedMixedProvenance.after_batch_models : ∀
  (capture : Yulang.GeneralDeclarationDemands.Capture)
  (report :
    Yulang.GeneralNominalRecursiveInspection.Report
      Yulang.GeneralDictionaryReservedEqualityStep.after.current.context.state)
  (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryReservedEqualityStep.after.current assignment →
    Yulang.GeneralNominalMaterialization.Models Yulang.GeneralDictionaryReservedEqualityStep.after.current.context.state
      Yulang.GeneralDictionaryFiniteObservedExample.declaration capture report
      (Yulang.GeneralNominalMaterialization.generated
        Yulang.GeneralDictionaryReservedEqualityStep.after.current.context.state
        Yulang.GeneralDictionaryReservedEqualityStep.after.current.context.interpretation
        Yulang.GeneralDictionaryReservedMixedProvenance.batch)
      assignment
Yulang.GeneralDictionaryReservedMixedProvenance.inhabited_mixed_provenance : ¬Yulang.GeneralDictionaryObservedFiniteRequests.Observed
      Yulang.GeneralDictionaryFiniteObservedExampleReserved.state
      Yulang.GeneralDictionaryFiniteObservedExample.interpretation
      [Yulang.GeneralDictionaryFiniteObservedExampleReserved.request] ∧
  Yulang.GeneralDictionaryRequestProvenance.Supported Yulang.GeneralDictionaryFiniteObservedExample.registry
      Yulang.GeneralDictionaryFiniteObservedExampleReserved.root
      Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.installed
      Yulang.GeneralDictionaryReservedMixedProvenance.batch ∧
    Yulang.GeneralNominalSaturationState.Models
        Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.installed.current
        Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.positive ∧
      Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryReservedEqualityStep.after.current
        Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.positive
Yulang.GeneralDictionaryReservedNominalRefresh.snapshot_models : ∀ (m : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryReservedEqualityStep.after.current m →
    Yulang.GeneralNominalState.Models Yulang.GeneralDictionaryReservedNominalRefresh.snapshot m
Yulang.GeneralDictionaryReservedNominalRefresh.output_member : 2 ∈
  Yulang.GeneralNominalState.sources Yulang.GeneralDictionaryReservedEqualityStep.after.current.context.state
Yulang.GeneralDictionaryReservedNominalRefresh.output_known : Yulang.GeneralNominalState.Known
  Yulang.GeneralDictionaryReservedNominalRefresh.snapshot 2
Yulang.GeneralDictionaryReservedNominalRefresh.refresh_step : Yulang.GeneralNominalValueSteps.Step
  Yulang.GeneralDictionaryFiniteObservedExample.registry Yulang.GeneralDictionaryFiniteObservedExampleReserved.root
  Yulang.GeneralDictionaryReservedEqualityStep.after Yulang.GeneralDictionaryReservedNominalRefresh.refreshed
Yulang.GeneralDictionaryReservedNominalRefresh.equality_successor_not_stable : ¬Yulang.GeneralNominalValueSteps.Stable
    Yulang.GeneralDictionaryFiniteObservedExample.registry Yulang.GeneralDictionaryReservedEqualityStep.after
    Yulang.GeneralDictionaryFiniteObservedExampleReserved.root
Yulang.GeneralDictionaryReservedNominalRefresh.refreshed_models : ∀ (m : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryReservedNominalRefresh.refreshed.current m ↔
    Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryReservedEqualityStep.after.current m
Yulang.GeneralDictionaryReservedNominalRefresh.refreshed_reachable : Yulang.B4TargetV5.Reachable
  (Yulang.GeneralNominalValueBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
  Yulang.GeneralDictionaryFiniteObservedExample.registry Yulang.GeneralDictionaryFiniteObservedExampleReserved.root
  Yulang.GeneralDictionaryReservedNominalRefresh.refreshed
Yulang.GeneralDictionaryReservedNominalRefresh.refreshed_inhabited : Yulang.GeneralNominalSaturationState.Models
  Yulang.GeneralDictionaryReservedNominalRefresh.refreshed.current
  Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.positive
Yulang.GeneralDictionaryReservedOutputEquality.nominal_repeated_scalar : ∀
  (assignment : Yulang.GeneralNominalCommonBridge.Assignment) (source name count : Nat)
  (scalar : Yulang.Inference.Base),
  (Yulang.GeneralNominalRecursiveInspection.Test.nominal name count).Holds (assignment source).fst →
    (∀ (index : Nat),
        index < count →
          (∃ actual,
              Yulang.GeneralNominalRecursiveInspection.Observes assignment
                ((Yulang.GeneralNominalRecursiveInspection.Origin.source source).nominal name index) actual) ∧
            ∀ (actual : Yulang.CommonNominalFullCarrier.Ty),
              Yulang.GeneralNominalRecursiveInspection.Observes assignment
                  ((Yulang.GeneralNominalRecursiveInspection.Origin.source source).nominal name index) actual →
                Yulang.CommonNominalFullCarrier.Equivalent actual (Yulang.CommonNominalSyntax.Layer.base scalar)) →
      Yulang.CommonNominalFullCarrier.Equivalent (assignment source).fst
        (Yulang.CommonNominalFullCarrier.nominal name
          (List.replicate count (Sum.inl (Yulang.CommonNominalSyntax.Layer.base scalar))))
Yulang.GeneralDictionaryReservedOutputEquality.output_equal : ∀
  (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalSaturationState.Models
      Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.installed.current assignment →
    Yulang.CommonNominalFullCarrier.Equivalent (assignment 2).fst
      (Yulang.CommonNominalFullCarrier.nominal 0 Yulang.GeneralDictionaryFiniteObservedExample.arguments)
Yulang.GeneralDictionaryReservedOutputEquality.source_equal : ∀
  (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalSaturationState.Models
      Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.installed.current assignment →
    Yulang.CommonNominalFullCarrier.Equivalent (assignment 0).fst
      (Yulang.CommonNominalFullCarrier.nominal 0 Yulang.GeneralDictionaryFiniteObservedExample.arguments)
Yulang.GeneralDictionaryReservedOutputEquality.journal_equal : Yulang.GeneralNominalFeedbackK2.Equal
  Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.installed.current 2 0
Yulang.GeneralDictionaryReservedRefreshedEvidence.metadata : Yulang.GeneralNominalRecursiveCandidates.Metadata
  Yulang.GeneralDictionaryFiniteObservedExample.registry Yulang.GeneralDictionaryReservedRefreshedEvidence.current
Yulang.GeneralDictionaryReservedRefreshedEvidence.recorded : Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.packet ∈
  Yulang.GeneralDictionaryReservedNominalRefresh.refreshed.current.packets
Yulang.GeneralDictionaryReservedRefreshedEvidence.requests_exact : ∀
  (capture : Yulang.GeneralNominalAllocation.Bindings),
  Yulang.GeneralNominalMaterialization.requests Yulang.GeneralDictionaryReservedRefreshedEvidence.current.state
      Yulang.GeneralDictionaryFiniteObservedExample.registry Yulang.GeneralDictionaryFiniteObservedExampleReserved.root
      Yulang.GeneralDictionaryFiniteObservedExample.declaration Yulang.GeneralDictionaryFiniteObservedExample.checked
      capture =
    [Yulang.GeneralDictionaryFiniteObservedExampleReserved.request]
Yulang.GeneralDictionaryReservedRefreshedEvidence.covered : Yulang.GeneralDictionaryRecordedBatchModels.Covered
  Yulang.GeneralDictionaryReservedNominalRefresh.refreshed.current
  [Yulang.GeneralDictionaryFiniteObservedExampleReserved.request]
Yulang.GeneralDictionaryReservedRefreshedEvidence.supported : Yulang.GeneralDictionaryRequestProvenance.Supported
  Yulang.GeneralDictionaryFiniteObservedExample.registry Yulang.GeneralDictionaryFiniteObservedExampleReserved.root
  Yulang.GeneralDictionaryReservedNominalRefresh.refreshed
  (Yulang.GeneralNominalMaterialization.requests Yulang.GeneralDictionaryReservedRefreshedEvidence.current.state
    Yulang.GeneralDictionaryFiniteObservedExample.registry Yulang.GeneralDictionaryFiniteObservedExampleReserved.root
    Yulang.GeneralDictionaryFiniteObservedExample.declaration Yulang.GeneralDictionaryFiniteObservedExample.checked
    (Yulang.GeneralNominalRecursiveInspection.bindings Yulang.GeneralDictionaryReservedRefreshedEvidence.current.state
      (Yulang.GeneralNominalRecursiveCandidates.report Yulang.GeneralDictionaryReservedRefreshedEvidence.current
        Yulang.GeneralDictionaryFiniteObservedExample.declaration
        [(Yulang.GeneralDictionaryReservedRefreshedEvidence.shape.slot,
            Yulang.GeneralDictionaryReservedRefreshedEvidence.shape.slot)])))
Yulang.GeneralDictionaryReservedRefreshedEvidence.current_instance : ∀
  (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryReservedNominalRefresh.refreshed.current
      assignment →
    Yulang.GeneralDictionaryRecursiveEvidence.Instance Yulang.GeneralDictionaryFiniteObservedExample.registry
      Yulang.GeneralDictionaryReservedRefreshedEvidence.current assignment
      Yulang.GeneralDictionaryFiniteObservedExampleReserved.root
      Yulang.GeneralDictionaryFiniteObservedExample.declaration.id []
Yulang.GeneralDictionaryReservedRefreshedEvidence.current_evidence : ∀
  (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryReservedNominalRefresh.refreshed.current
      assignment →
    Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralDictionaryFiniteObservedExample.registry
      Yulang.GeneralDictionaryReservedRefreshedEvidence.current assignment
      Yulang.GeneralDictionaryFiniteObservedExampleReserved.root
      (Yulang.CommonRoleOutermostResolver.Dictionary.node Yulang.GeneralDictionaryFiniteObservedExample.declaration.id
        [])
Yulang.GeneralDictionaryReservedRefreshedEvidence.reachable_inhabited_dictionary : Yulang.B4TargetV5.Reachable
    (Yulang.GeneralNominalValueBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
    Yulang.GeneralDictionaryFiniteObservedExample.registry Yulang.GeneralDictionaryFiniteObservedExampleReserved.root
    Yulang.GeneralDictionaryReservedNominalRefresh.refreshed ∧
  Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryReservedNominalRefresh.refreshed.current
      Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.positive ∧
    Yulang.GeneralNominalState.Known Yulang.GeneralDictionaryReservedRefreshedEvidence.current.state 2 ∧
      Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralDictionaryFiniteObservedExample.registry
        Yulang.GeneralDictionaryReservedRefreshedEvidence.current
        Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.positive
        Yulang.GeneralDictionaryFiniteObservedExampleReserved.root
        (Yulang.CommonRoleOutermostResolver.Dictionary.node Yulang.GeneralDictionaryFiniteObservedExample.declaration.id
          [])
Yulang.GeneralDictionaryReservedSuccessorBoundary.raw_equal : Yulang.GeneralNominalFeedbackSteps.RawEqual
  Yulang.GeneralDictionaryReservedEqualityStep.after.current 2 0
Yulang.GeneralDictionaryReservedSuccessorBoundary.no_target_slot : ¬∃ slot,
    Yulang.GeneralDictionaryReservedEqualityStep.after.current.context.state.base.source slot = 2
Yulang.GeneralDictionaryReservedSuccessorBoundary.output_not_known : ¬Yulang.GeneralNominalState.Known
    Yulang.GeneralDictionaryReservedEqualityStep.after.current.context.state 2
Yulang.GeneralDictionaryReservedSuccessorBoundary.point_closed : Yulang.GeneralNominalReobservationSteps.PointClosed
  Yulang.GeneralDictionaryReservedEqualityStep.after.current.context.state
Yulang.GeneralDictionaryReservedSuccessorBoundary.no_reobservation : ∀
  (revision :
    Yulang.GeneralNominalReobservationSteps.Revision Yulang.GeneralDictionaryReservedEqualityStep.after.current),
  ¬Yulang.GeneralNominalReobservationSteps.Improves revision
Yulang.GeneralDictionaryReservedSuccessorBoundary.stable_excludes_output_refresh : Yulang.GeneralNominalValueSteps.Stable
    Yulang.GeneralDictionaryFiniteObservedExample.registry Yulang.GeneralDictionaryReservedEqualityStep.after
    Yulang.GeneralDictionaryFiniteObservedExampleReserved.root →
  ∀ (next : Yulang.GeneralNominalCandidates.Context)
    (certificate :
      Yulang.GeneralNominalFeedbackSteps.Refresh Yulang.GeneralDictionaryReservedEqualityStep.after.current next),
    ¬Yulang.GeneralNominalState.Known next.state 2
@Yulang.GeneralDictionarySelectedProvenanceCoverage.dictionary_evidence : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (state : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.B4TargetV5.Reachable (Yulang.GeneralNominalValueBoundary.boundary roles) registry root state →
    Yulang.GeneralDictionarySelectedProvenanceCoverage.Covered registry root state →
      ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
        Yulang.GeneralNominalSaturationState.Models state.current model →
          ∀ (dictionary : Yulang.GeneralDictionaryReadback.Payload)
            (focus : Yulang.GeneralSourceDictionaries.Occurrence roles),
            Yulang.GeneralDictionarySelectionPolicy.SelectedPath
                (Yulang.GeneralNominalValueBoundary.boundary roles).toSourceBoundary registry state root focus →
              Yulang.B4TargetV3.Classify (Yulang.GeneralNominalValueBoundary.boundary roles).toSourceBoundary registry
                  state focus (Yulang.CommonRoleOutermostResolver.Result.selected dictionary) →
                Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context model focus dictionary
@Yulang.GeneralDictionarySelectedProvenanceCoverage.dictionaries_evidence : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (state : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.B4TargetV5.Reachable (Yulang.GeneralNominalValueBoundary.boundary roles) registry root state →
    Yulang.GeneralDictionarySelectedProvenanceCoverage.Covered registry root state →
      ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
        Yulang.GeneralNominalSaturationState.Models state.current model →
          ∀ (dictionaries : List Yulang.GeneralDictionaryReadback.Payload)
            (focuses : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
            (∀ (focus : Yulang.GeneralSourceDictionaries.Occurrence roles),
                focus ∈ focuses →
                  Yulang.GeneralDictionarySelectionPolicy.SelectedPath
                    (Yulang.GeneralNominalValueBoundary.boundary roles).toSourceBoundary registry state root focus) →
              Yulang.CommonRoleOutermostResolver.All₂
                  (fun focus dictionary =>
                    Yulang.B4TargetV3.Classify (Yulang.GeneralNominalValueBoundary.boundary roles).toSourceBoundary
                      registry state focus (Yulang.CommonRoleOutermostResolver.Result.selected dictionary))
                  focuses dictionaries →
                Yulang.CommonRoleOutermostResolver.All₂
                  (Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context model) focuses
                  dictionaries
@Yulang.GeneralDictionarySelectedProvenanceCoverage.root_dictionary_evidence : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (state : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.B4TargetV5.Reachable (Yulang.GeneralNominalValueBoundary.boundary roles) registry root state →
    Yulang.GeneralDictionarySelectedProvenanceCoverage.Covered registry root state →
      ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
        Yulang.GeneralNominalSaturationState.Models state.current model →
          ∀ (dictionary : Yulang.GeneralDictionaryReadback.Payload),
            Yulang.B4TargetV3.Classify (Yulang.GeneralNominalValueBoundary.boundary roles).toSourceBoundary registry
                state root (Yulang.CommonRoleOutermostResolver.Result.selected dictionary) →
              Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context model root dictionary
@Yulang.GeneralDictionarySelectedProvenanceCoverage.completed_tree_evidence : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (state : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.B4TargetV5.Reachable (Yulang.GeneralNominalValueBoundary.boundary roles) registry root state →
    Yulang.GeneralDictionarySelectedProvenanceCoverage.Covered registry root state →
      ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
        Yulang.GeneralNominalSaturationState.Models state.current model →
          ∀ (tree : Yulang.CommonRoleOutermostResolver.Tree),
            Yulang.CommonRoleOutermostResolver.Resolves
                (Yulang.B4TargetV3.Local (Yulang.GeneralNominalValueBoundary.boundary roles).toSourceBoundary registry
                  state)
                root tree →
              ∀ (dictionary : Yulang.GeneralDictionaryReadback.Payload),
                Yulang.B4TargetV3.Completed tree (Yulang.CommonRoleOutermostResolver.Result.selected dictionary) →
                  Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context model root
                    dictionary
@Yulang.GeneralDictionarySelectedProvenanceCoverage.covered_of_global : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (state : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.GeneralDictionaryProvenanceClassification.Covered registry root state →
    Yulang.GeneralDictionarySelectedProvenanceCoverage.Covered registry root state
```
