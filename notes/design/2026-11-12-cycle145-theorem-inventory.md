# cycle145 theorem inventory

Full Lean-checked implicit quantifiers and hypotheses follow. Helper/scoped regression results do not close general V5 bridges.

## GeneralDictionaryAliasJoint

`joint_at_related`, `joint_alias_iff`, `representative_instance`

## GeneralDictionaryFailedDiagnosticScope

`no_selected_classification`, `no_children_evidence`, `node_at_failed_snapshot`

## GeneralDictionaryJointMerge

`evidence_merge_iff`, `evidence_merge_of_outputs`, `branch_extension`, `branch_extension_back`, `merge_sources`, `branch_merge`, `branch_merge_iff`, `alias_merge_first_iff`, `joint_merge_shared`, `joint_merge_iff`, `joint_merge_of_outputs`, `branch_output_targets`, `joint_merge_registered`, `sourceformed_merge_joint`

## GeneralDictionaryJointMergeEnabled

`recovered`, `same`, `guard`, `distinct`, `actual_step`, `enabled_nonempty_joint`

## GeneralDictionaryJointMergeExample

`terminal_checked`, `source_models`, `report_exact`, `emissions_empty`, `schema_exact`, `branch_models`, `prepared`, `before_models`, `branch_at`, `same_inputs`, `dictionary_outputs`, `output_atoms_nonempty`, `output_atoms_hold`, `merged_joint`, `source_evidence`, `merged_evidence`

## GeneralDictionaryJointMergeJournalScope

`bad_source_models`, `bad_packet`, `no_empty_facts_formation`

## GeneralDictionaryJointMergeResidual

`separate_joint_merge_iff`, `separate_joint_failure_iff`, `recorded_key_conflict`

## GeneralDictionaryJointMergeSequence

`sources_fold`, `branch_fold`, `packets_fold`, `sites_fold`, `joint_fold`, `aliases_fold`, `alias_edges_iff`, `alias_events_iff`, `joint_events_iff`

## GeneralDictionaryMergeSequence

`models_fold`, `evidence_fold`, `evidence_at_final_model`, `event_atoms_iff`, `models_events_iff`, `evidence_events_iff`

## GeneralDictionaryOutputMergeReachable

`checked`, `registry_checked`, `all_source_decisions`, `query`, `output_nonzero`, `schema`, `branch`, `prepared`, `survivor`, `selected`, `children_exact`, `enabled`, `packet_guard`, `novel`, `source`, `before_scheduled`, `before_model`, `site_present`, `inputs_same`, `actual_early_merge`, `finish_model`, `actual_path`, `reachable`, `inhabited_early_merge`, `output_atoms_exact`, `output_targets_distinct`, `finish_sourceformed`, `reachable_nonempty_output_merge`

## GeneralDictionaryOutputMergeRootEvidence

`parent_instance`, `current_parent_instance`, `root_evidence`, `reachable_full_dictionary`

## GeneralDictionaryOutputMergeScalarFacts

`packet_present`, `requests`, `all_models_unchanged`, `all_models_evidence_unchanged`

## GeneralDictionaryOutputMergeScope

`child_no_branch`, `child_no_joint`, `child_no_instance`, `child_no_evidence`, `reachable_without_child_evidence`

## GeneralDictionaryOutputMergeSuccess

`checked`, `registry_checked`, `all_source_decisions`, `query`, `output_nonzero`, `schema`, `branch`, `prepared`, `survivor`, `selected`, `children_exact`, `enabled`, `packet_guard`, `novel`, `source`, `before_scheduled`, `before_model`, `site_present`, `inputs_same`, `actual_early_merge`, `finish_model`, `actual_path`, `reachable`, `inhabited_early_merge`, `output_atoms_exact`, `output_targets_distinct`, `finish_sourceformed`, `reachable_nonempty_output_merge`, `terminal_report`, `terminal_schema`, `terminal_branch`, `terminal_instance`, `final_extension`, `current_terminal_instance`, `output_reserved`, `sources_shape`, `current_fresh`, `child_linked`, `child_branch_at`, `old_alias_eq`, `first_not_parent`, `last_not_parent`, `sites_exact`, `merged_alias_identity`, `merged_child_joint`, `merged_child_evidence`, `reachable_joint_evidence`

## GeneralDictionaryScalarJournalMerge

`outputs_from_packets`, `models_merge_iff`, `evidence_merge_iff`

## GeneralDictionaryScalarMerge

`output_atoms_of_scalar_tests`, `evidence_merge_of_scalar_tests`

## GeneralDictionaryScalarMergeExample

`generated_output_equations`, `complete_evidence_from_requests`

## Elaborated theorem types

```text
@Yulang.GeneralDictionaryAliasJoint.joint_at_related : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSaturationState.State roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (site : Yulang.GeneralNominalDemandMerging.Site roles)
  (key : Nat),
  Yulang.GeneralNominalJointCandidates.Related state root site →
    Yulang.GeneralNominalJointCandidates.Joint registry state root key →
      Yulang.GeneralNominalJointCandidates.Joint registry state site.occurrence key
@Yulang.GeneralDictionaryAliasJoint.joint_alias_iff : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSaturationState.State roles)
  (first last : Yulang.GeneralNominalDemandMerging.Site roles) (key : Nat),
  Membership.mem.{0, 0} state.sites first →
    Membership.mem.{0, 0} state.sites last →
      Yulang.GeneralNominalSaturationState.Alias state first.occurrence.identity last.occurrence.identity →
        (Yulang.GeneralNominalJointCandidates.Joint registry state first.occurrence key ↔
          Yulang.GeneralNominalJointCandidates.Joint registry state last.occurrence key)
@Yulang.GeneralDictionaryAliasJoint.representative_instance : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSupport.Tracked roles)
  (root focus representative : Yulang.GeneralSourceDictionaries.Occurrence roles),
  Yulang.B4TargetV5.Reachable.{0} (Yulang.GeneralNominalSupportBoundary.boundary roles) registry root state →
    ∀ (site : Yulang.GeneralNominalDemandMerging.Site roles),
      Yulang.GeneralNominalJointCandidates.Related state.current representative site →
        Eq.{1} site.occurrence focus →
          ∀ (key : Nat) (children : List.{0} (Yulang.GeneralSourceDictionaries.Occurrence roles)),
            Yulang.GeneralNominalSupportSteps.Stable registry state focus →
              Yulang.GeneralNominalSupportBoundary.Local registry state focus
                  (Yulang.CommonRoleOutermostResolver.Frontier.selected.{0} key children) →
                Yulang.GeneralNominalJointCandidates.Joint registry state.current representative key →
                  (∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                      Yulang.GeneralNominalSaturationState.Models state.current model →
                        Yulang.GeneralDictionaryRecursiveEvidence.Instance registry state.current.context model focus
                          key children) ∧
                    ∀ (child : Yulang.GeneralSourceDictionaries.Occurrence roles),
                      Membership.mem.{0, 0} children child →
                        Yulang.GeneralNominalSaturationState.Generated state.current focus child
Yulang.GeneralDictionaryFailedDiagnosticScope.no_selected_classification : ∀
  (dictionary : Yulang.CommonRoleOutermostResolver.Dictionary),
  ¬Yulang.B4TargetV3.Classify.{0}
      (Yulang.B4TargetV5.SourceBoundary.toSourceBoundary.{0} Yulang.GeneralDictionaryFailedDiagnosticScope.b)
      Yulang.GeneralDictionaryEarlyMergeExample.registry Yulang.GeneralDictionaryEarlyMergeExample.finish
      Yulang.GeneralNominalExamples.displayRoot (Yulang.CommonRoleOutermostResolver.Result.selected dictionary)
Yulang.GeneralDictionaryFailedDiagnosticScope.no_children_evidence : ∀
  (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (dictionaries : List.{0} Yulang.CommonRoleOutermostResolver.Dictionary),
  ¬Yulang.CommonRoleOutermostResolver.All₂.{0, 0}
      (fun child dictionary =>
        Yulang.B4Target.SourceBoundary.Evidence.{0}
          (Yulang.B4TargetV5.SourceBoundary.toSourceBoundary.{0} Yulang.GeneralDictionaryFailedDiagnosticScope.b)
          Yulang.GeneralDictionaryEarlyMergeExample.registry Yulang.GeneralDictionaryEarlyMergeExample.finish model
          child dictionary)
      Yulang.GeneralDictionaryEarlyMergeExample.children dictionaries
Yulang.GeneralDictionaryFailedDiagnosticScope.node_at_failed_snapshot : ∀
  (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (focus : Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles) (key : Nat)
  (kids : List.{0} (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles))
  (dictionaries : List.{0} Yulang.CommonRoleOutermostResolver.Dictionary),
  Eq.{1} focus Yulang.GeneralNominalExamples.displayRoot ∨
      Yulang.B4Target.SourceBoundary.Generated.{0}
        (Yulang.B4TargetV5.SourceBoundary.toSourceBoundary.{0} Yulang.GeneralDictionaryFailedDiagnosticScope.b)
        Yulang.GeneralDictionaryEarlyMergeExample.registry Yulang.GeneralDictionaryEarlyMergeExample.finish
        Yulang.GeneralNominalExamples.displayRoot focus →
    Yulang.B4Target.SafeKnown.{0}
        (Yulang.B4TargetV5.SourceBoundary.toSourceBoundary.{0} Yulang.GeneralDictionaryFailedDiagnosticScope.b)
        Yulang.GeneralDictionaryEarlyMergeExample.registry Yulang.GeneralDictionaryEarlyMergeExample.finish focus →
      Yulang.B4Target.Unique.{0}
          (Yulang.B4TargetV5.SourceBoundary.toSourceBoundary.{0} Yulang.GeneralDictionaryFailedDiagnosticScope.b)
          Yulang.GeneralDictionaryEarlyMergeExample.registry Yulang.GeneralDictionaryEarlyMergeExample.finish focus key
          kids →
        Yulang.CommonRoleOutermostResolver.All₂.{0, 0}
            (fun child dictionary =>
              Yulang.B4Target.SourceBoundary.Evidence.{0}
                (Yulang.B4TargetV5.SourceBoundary.toSourceBoundary.{0} Yulang.GeneralDictionaryFailedDiagnosticScope.b)
                Yulang.GeneralDictionaryEarlyMergeExample.registry Yulang.GeneralDictionaryEarlyMergeExample.finish
                model child dictionary)
            kids dictionaries →
          Yulang.B4Target.SourceBoundary.Evidence.{0}
            (Yulang.B4TargetV5.SourceBoundary.toSourceBoundary.{0} Yulang.GeneralDictionaryFailedDiagnosticScope.b)
            Yulang.GeneralDictionaryEarlyMergeExample.registry Yulang.GeneralDictionaryEarlyMergeExample.finish model
            focus (Yulang.CommonRoleOutermostResolver.Dictionary.node key dictionaries)
@Yulang.GeneralDictionaryJointMerge.evidence_merge_iff : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSaturationState.State roles)
  (first last : Yulang.GeneralNominalDemandMerging.Site roles) (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (payload : Yulang.GeneralDictionaryReadback.Payload),
  Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry
      (Yulang.GeneralNominalSaturationState.merge state first last).context model root payload ↔
    Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry state.context model root payload ∧
      Yulang.PresenceNormalForm.All.{0, 0} Yulang.CommonNominalFullCarrier.model model
        (Yulang.GeneralNominalDemandMerging.outputAtoms first last)
@Yulang.GeneralDictionaryJointMerge.evidence_merge_of_outputs : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSaturationState.State roles)
  (first last : Yulang.GeneralNominalDemandMerging.Site roles),
  Yulang.GeneralNominalDemandMerging.SameInputs (Yulang.GeneralNominalSaturationState.Models state) first last →
    ∀ (meaning : Yulang.GeneralNominalDemandMerging.AssociatedMeaning)
      (model : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.GeneralNominalSaturationState.Models state model →
        Yulang.GeneralNominalDemandMerging.DictionaryOutputs meaning model first →
          Yulang.GeneralNominalDemandMerging.DictionaryOutputs meaning model last →
            ∀ (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
              (payload : Yulang.GeneralDictionaryReadback.Payload),
              Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry state.context model root payload →
                Yulang.GeneralNominalSaturationState.Models
                    (Yulang.GeneralNominalSaturationState.merge state first last) model ∧
                  Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry
                    (Yulang.GeneralNominalSaturationState.merge state first last).context model root payload
@Yulang.GeneralDictionaryJointMerge.branch_extension : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSaturationState.State roles)
  (atoms : List.{0} (Yulang.PresenceNormalForm.Atom Nat)),
  (∀ (source : Nat),
      Membership.mem.{0, 0}
          (Yulang.GeneralNominalState.sources
            (Yulang.GeneralNominalState.extend state.context.state List.nil.{0} atoms))
          source ↔
        Membership.mem.{0, 0} (Yulang.GeneralNominalState.sources state.context.state) source) →
    ∀ (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (key : Nat)
      (model : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.PresenceNormalForm.All.{0, 0} Yulang.CommonNominalFullCarrier.model model atoms →
        Yulang.GeneralNominalJointCandidates.BranchAt registry state root key model →
          Yulang.GeneralNominalJointCandidates.BranchAt registry
            { context := Yulang.GeneralDictionaryOrdinaryTransport.extend state.context List.nil.{0} atoms List.nil.{0},
              packets := state.packets, sites := state.sites, edges := state.edges, aliases := state.aliases }
            root key model
@Yulang.GeneralDictionaryJointMerge.branch_extension_back : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSaturationState.State roles)
  (atoms : List.{0} (Yulang.PresenceNormalForm.Atom Nat)),
  (∀ (source : Nat),
      Membership.mem.{0, 0}
          (Yulang.GeneralNominalState.sources
            (Yulang.GeneralNominalState.extend state.context.state List.nil.{0} atoms))
          source ↔
        Membership.mem.{0, 0} (Yulang.GeneralNominalState.sources state.context.state) source) →
    ∀ (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (key : Nat)
      (model : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.GeneralNominalJointCandidates.BranchAt registry
          { context := Yulang.GeneralDictionaryOrdinaryTransport.extend state.context List.nil.{0} atoms List.nil.{0},
            packets := state.packets, sites := state.sites, edges := state.edges, aliases := state.aliases }
          root key model →
        Yulang.GeneralNominalJointCandidates.BranchAt registry state root key model ∧
          Yulang.PresenceNormalForm.All.{0, 0} Yulang.CommonNominalFullCarrier.model model atoms
@Yulang.GeneralDictionaryJointMerge.merge_sources : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalSaturationState.State roles)
  (first last : Yulang.GeneralNominalDemandMerging.Site roles),
  (∀ (output : Yulang.GeneralSourceState.Output),
      Membership.mem.{0, 0} first.occurrence.demand.outputs output →
        Membership.mem.{0, 0} (Yulang.GeneralNominalState.sources state.context.state) output.target) →
    (∀ (output : Yulang.GeneralSourceState.Output),
        Membership.mem.{0, 0} last.occurrence.demand.outputs output →
          Membership.mem.{0, 0} (Yulang.GeneralNominalState.sources state.context.state) output.target) →
      ∀ (source : Nat),
        Membership.mem.{0, 0}
            (Yulang.GeneralNominalState.sources
              (Yulang.GeneralNominalSaturationState.merge state first last).context.state)
            source ↔
          Membership.mem.{0, 0} (Yulang.GeneralNominalState.sources state.context.state) source
@Yulang.GeneralDictionaryJointMerge.branch_merge : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSaturationState.State roles)
  (first last : Yulang.GeneralNominalDemandMerging.Site roles),
  (∀ (output : Yulang.GeneralSourceState.Output),
      Membership.mem.{0, 0} first.occurrence.demand.outputs output →
        Membership.mem.{0, 0} (Yulang.GeneralNominalState.sources state.context.state) output.target) →
    (∀ (output : Yulang.GeneralSourceState.Output),
        Membership.mem.{0, 0} last.occurrence.demand.outputs output →
          Membership.mem.{0, 0} (Yulang.GeneralNominalState.sources state.context.state) output.target) →
      ∀ (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (key : Nat)
        (model : Yulang.GeneralNominalCommonBridge.Assignment),
        Yulang.PresenceNormalForm.All.{0, 0} Yulang.CommonNominalFullCarrier.model model
            (Yulang.GeneralNominalDemandMerging.outputAtoms first last) →
          Yulang.GeneralNominalJointCandidates.BranchAt registry state root key model →
            Yulang.GeneralNominalJointCandidates.BranchAt registry
              (Yulang.GeneralNominalSaturationState.merge state first last) root key model
@Yulang.GeneralDictionaryJointMerge.branch_merge_iff : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSaturationState.State roles)
  (first last : Yulang.GeneralNominalDemandMerging.Site roles),
  (∀ (output : Yulang.GeneralSourceState.Output),
      Membership.mem.{0, 0} first.occurrence.demand.outputs output →
        Membership.mem.{0, 0} (Yulang.GeneralNominalState.sources state.context.state) output.target) →
    (∀ (output : Yulang.GeneralSourceState.Output),
        Membership.mem.{0, 0} last.occurrence.demand.outputs output →
          Membership.mem.{0, 0} (Yulang.GeneralNominalState.sources state.context.state) output.target) →
      ∀ (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (key : Nat)
        (model : Yulang.GeneralNominalCommonBridge.Assignment),
        Yulang.GeneralNominalJointCandidates.BranchAt registry
            (Yulang.GeneralNominalSaturationState.merge state first last) root key model ↔
          Yulang.GeneralNominalJointCandidates.BranchAt registry state root key model ∧
            Yulang.PresenceNormalForm.All.{0, 0} Yulang.CommonNominalFullCarrier.model model
              (Yulang.GeneralNominalDemandMerging.outputAtoms first last)
@Yulang.GeneralDictionaryJointMerge.alias_merge_first_iff : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalSaturationState.State roles)
  (first last : Yulang.GeneralNominalDemandMerging.Site roles) (identity : Nat),
  Yulang.GeneralNominalSaturationState.Alias (Yulang.GeneralNominalSaturationState.merge state first last)
      first.occurrence.identity identity ↔
    Yulang.GeneralNominalSaturationState.Alias state first.occurrence.identity identity ∨
      Yulang.GeneralNominalSaturationState.Alias state last.occurrence.identity identity
@Yulang.GeneralDictionaryJointMerge.joint_merge_shared : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSaturationState.State roles)
  (first last : Yulang.GeneralNominalDemandMerging.Site roles),
  (∀ (output : Yulang.GeneralSourceState.Output),
      Membership.mem.{0, 0} first.occurrence.demand.outputs output →
        Membership.mem.{0, 0} (Yulang.GeneralNominalState.sources state.context.state) output.target) →
    (∀ (output : Yulang.GeneralSourceState.Output),
        Membership.mem.{0, 0} last.occurrence.demand.outputs output →
          Membership.mem.{0, 0} (Yulang.GeneralNominalState.sources state.context.state) output.target) →
      ∀ (key : Nat),
        (∀ (packet : Yulang.GeneralNominalSaturationState.Packet roles),
            Membership.mem.{0, 0} state.packets packet →
              Yulang.GeneralNominalSaturationState.Alias state first.occurrence.identity
                    packet.site.occurrence.identity ∨
                  Yulang.GeneralNominalSaturationState.Alias state last.occurrence.identity
                    packet.site.occurrence.identity →
                Eq.{1} packet.declaration.id key) →
          ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
            Yulang.GeneralNominalSaturationState.Models state model →
              Yulang.PresenceNormalForm.All.{0, 0} Yulang.CommonNominalFullCarrier.model model
                  (Yulang.GeneralNominalDemandMerging.outputAtoms first last) →
                Yulang.GeneralNominalJointCandidates.BranchAt registry state first.occurrence key model →
                  (∀ (site : Yulang.GeneralNominalDemandMerging.Site roles),
                      Membership.mem.{0, 0} state.sites site →
                        Yulang.GeneralNominalSaturationState.Alias state first.occurrence.identity
                              site.occurrence.identity ∨
                            Yulang.GeneralNominalSaturationState.Alias state last.occurrence.identity
                              site.occurrence.identity →
                          Yulang.GeneralNominalJointCandidates.BranchAt registry state site.occurrence key model) →
                    Yulang.GeneralNominalJointCandidates.Joint registry
                      (Yulang.GeneralNominalSaturationState.merge state first last) first.occurrence key
@Yulang.GeneralDictionaryJointMerge.joint_merge_iff : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSaturationState.State roles)
  (first last : Yulang.GeneralNominalDemandMerging.Site roles),
  (∀ (output : Yulang.GeneralSourceState.Output),
      Membership.mem.{0, 0} first.occurrence.demand.outputs output →
        Membership.mem.{0, 0} (Yulang.GeneralNominalState.sources state.context.state) output.target) →
    (∀ (output : Yulang.GeneralSourceState.Output),
        Membership.mem.{0, 0} last.occurrence.demand.outputs output →
          Membership.mem.{0, 0} (Yulang.GeneralNominalState.sources state.context.state) output.target) →
      ∀ (key : Nat),
        Yulang.GeneralNominalJointCandidates.Joint registry
            (Yulang.GeneralNominalSaturationState.merge state first last) first.occurrence key ↔
          (∀ (packet : Yulang.GeneralNominalSaturationState.Packet roles),
              Membership.mem.{0, 0} state.packets packet →
                Yulang.GeneralNominalSaturationState.Alias state first.occurrence.identity
                      packet.site.occurrence.identity ∨
                    Yulang.GeneralNominalSaturationState.Alias state last.occurrence.identity
                      packet.site.occurrence.identity →
                  Eq.{1} packet.declaration.id key) ∧
            Exists.{1} fun model =>
              Yulang.GeneralNominalSaturationState.Models state model ∧
                Yulang.PresenceNormalForm.All.{0, 0} Yulang.CommonNominalFullCarrier.model model
                    (Yulang.GeneralNominalDemandMerging.outputAtoms first last) ∧
                  Yulang.GeneralNominalJointCandidates.BranchAt registry state first.occurrence key model ∧
                    ∀ (site : Yulang.GeneralNominalDemandMerging.Site roles),
                      Membership.mem.{0, 0} state.sites site →
                        Yulang.GeneralNominalSaturationState.Alias state first.occurrence.identity
                              site.occurrence.identity ∨
                            Yulang.GeneralNominalSaturationState.Alias state last.occurrence.identity
                              site.occurrence.identity →
                          Yulang.GeneralNominalJointCandidates.BranchAt registry state site.occurrence key model
@Yulang.GeneralDictionaryJointMerge.joint_merge_of_outputs : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSaturationState.State roles)
  (first last : Yulang.GeneralNominalDemandMerging.Site roles),
  (∀ (output : Yulang.GeneralSourceState.Output),
      Membership.mem.{0, 0} first.occurrence.demand.outputs output →
        Membership.mem.{0, 0} (Yulang.GeneralNominalState.sources state.context.state) output.target) →
    (∀ (output : Yulang.GeneralSourceState.Output),
        Membership.mem.{0, 0} last.occurrence.demand.outputs output →
          Membership.mem.{0, 0} (Yulang.GeneralNominalState.sources state.context.state) output.target) →
      ∀ (key : Nat),
        (∀ (packet : Yulang.GeneralNominalSaturationState.Packet roles),
            Membership.mem.{0, 0} state.packets packet →
              Yulang.GeneralNominalSaturationState.Alias state first.occurrence.identity
                    packet.site.occurrence.identity ∨
                  Yulang.GeneralNominalSaturationState.Alias state last.occurrence.identity
                    packet.site.occurrence.identity →
                Eq.{1} packet.declaration.id key) →
          Yulang.GeneralNominalDemandMerging.SameInputs (Yulang.GeneralNominalSaturationState.Models state) first last →
            ∀ (meaning : Yulang.GeneralNominalDemandMerging.AssociatedMeaning)
              (model : Yulang.GeneralNominalCommonBridge.Assignment),
              Yulang.GeneralNominalSaturationState.Models state model →
                Yulang.GeneralNominalDemandMerging.DictionaryOutputs meaning model first →
                  Yulang.GeneralNominalDemandMerging.DictionaryOutputs meaning model last →
                    Yulang.GeneralNominalJointCandidates.BranchAt registry state first.occurrence key model →
                      (∀ (site : Yulang.GeneralNominalDemandMerging.Site roles),
                          Membership.mem.{0, 0} state.sites site →
                            Yulang.GeneralNominalSaturationState.Alias state first.occurrence.identity
                                  site.occurrence.identity ∨
                                Yulang.GeneralNominalSaturationState.Alias state last.occurrence.identity
                                  site.occurrence.identity →
                              Yulang.GeneralNominalJointCandidates.BranchAt registry state site.occurrence key model) →
                        Yulang.GeneralNominalJointCandidates.Joint registry
                          (Yulang.GeneralNominalSaturationState.merge state first last) first.occurrence key
@Yulang.GeneralDictionaryJointMerge.branch_output_targets : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSaturationState.State roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (key : Nat)
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalJointCandidates.BranchAt registry state root key model →
    ∀ (output : Yulang.GeneralSourceState.Output),
      Membership.mem.{0, 0} root.demand.outputs output →
        Membership.mem.{0, 0} (Yulang.GeneralNominalState.sources state.context.state) output.target
@Yulang.GeneralDictionaryJointMerge.joint_merge_registered : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSaturationState.State roles)
  (first last : Yulang.GeneralNominalDemandMerging.Site roles),
  Membership.mem.{0, 0} state.sites last →
    ∀ (key : Nat),
      (∀ (packet : Yulang.GeneralNominalSaturationState.Packet roles),
          Membership.mem.{0, 0} state.packets packet →
            Yulang.GeneralNominalSaturationState.Alias state first.occurrence.identity packet.site.occurrence.identity ∨
                Yulang.GeneralNominalSaturationState.Alias state last.occurrence.identity
                  packet.site.occurrence.identity →
              Eq.{1} packet.declaration.id key) →
        ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
          Yulang.GeneralNominalSaturationState.Models state model →
            Yulang.PresenceNormalForm.All.{0, 0} Yulang.CommonNominalFullCarrier.model model
                (Yulang.GeneralNominalDemandMerging.outputAtoms first last) →
              Yulang.GeneralNominalJointCandidates.BranchAt registry state first.occurrence key model →
                (∀ (site : Yulang.GeneralNominalDemandMerging.Site roles),
                    Membership.mem.{0, 0} state.sites site →
                      Yulang.GeneralNominalSaturationState.Alias state first.occurrence.identity
                            site.occurrence.identity ∨
                          Yulang.GeneralNominalSaturationState.Alias state last.occurrence.identity
                            site.occurrence.identity →
                        Yulang.GeneralNominalJointCandidates.BranchAt registry state site.occurrence key model) →
                  Yulang.GeneralNominalJointCandidates.Joint registry
                    (Yulang.GeneralNominalSaturationState.merge state first last) first.occurrence key
@Yulang.GeneralDictionaryJointMerge.sourceformed_merge_joint : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (before : Yulang.GeneralNominalSupport.Tracked roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
  Yulang.GeneralNominalSupportSteps.SourceFormed registry root before →
    ∀ (first last : Yulang.GeneralNominalDemandMerging.Site roles)
      (support : List.{0} (Yulang.GeneralSourceDictionaries.Occurrence roles)),
      Yulang.GeneralNominalSaturationState.Generated before.current root first.occurrence →
        Membership.mem.{0, 0} before.current.sites first →
          Membership.mem.{0, 0} before.current.sites last →
            Yulang.GeneralNominalFeedbackSites.SameInputs before.current first last →
              ¬Yulang.GeneralNominalSaturationState.Alias before.current first.occurrence.identity
                    last.occurrence.identity →
                Yulang.GeneralNominalSupportChoices.MergeGuard before first last support →
                  ∀ (key : Nat),
                    (∀ (packet : Yulang.GeneralNominalSaturationState.Packet roles),
                        Membership.mem.{0, 0} before.current.packets packet →
                          Yulang.GeneralNominalSaturationState.Alias before.current first.occurrence.identity
                                packet.site.occurrence.identity ∨
                              Yulang.GeneralNominalSaturationState.Alias before.current last.occurrence.identity
                                packet.site.occurrence.identity →
                            Eq.{1} packet.declaration.id key) →
                      ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                        Yulang.GeneralNominalSaturationState.Models before.current model →
                          Yulang.PresenceNormalForm.All.{0, 0} Yulang.CommonNominalFullCarrier.model model
                              (Yulang.GeneralNominalDemandMerging.outputAtoms first last) →
                            Yulang.GeneralNominalJointCandidates.BranchAt registry before.current first.occurrence key
                                model →
                              (∀ (site : Yulang.GeneralNominalDemandMerging.Site roles),
                                  Membership.mem.{0, 0} before.current.sites site →
                                    Yulang.GeneralNominalSaturationState.Alias before.current first.occurrence.identity
                                          site.occurrence.identity ∨
                                        Yulang.GeneralNominalSaturationState.Alias before.current
                                          last.occurrence.identity site.occurrence.identity →
                                      Yulang.GeneralNominalJointCandidates.BranchAt registry before.current
                                        site.occurrence key model) →
                                Yulang.GeneralNominalSupportSteps.Step registry root before
                                    (Yulang.GeneralNominalSupportSteps.merge before first last support) ∧
                                  Yulang.GeneralNominalSupportSteps.SourceFormed registry root
                                      (Yulang.GeneralNominalSupportSteps.merge before first last support) ∧
                                    Yulang.GeneralNominalJointCandidates.Joint registry
                                      (Yulang.GeneralNominalSupportSteps.merge before first last support).current
                                      first.occurrence key
Yulang.GeneralDictionaryJointMergeEnabled.recovered : ∀ (identity target : Nat),
  Eq.{1}
    (Yulang.GeneralNominalFeedbackSites.recover Yulang.GeneralDictionaryJointMergeExample.before
      (Yulang.GeneralNominalDemandMerging.pointSite (Yulang.GeneralDictionaryJointMergeExample.root identity target)))
    (Yulang.GeneralNominalDemandMerging.pointSite (Yulang.GeneralDictionaryJointMergeExample.root identity target))
Yulang.GeneralDictionaryJointMergeEnabled.same : ∀ (models : Yulang.GeneralNominalCommonBridge.Assignment → Prop),
  Yulang.GeneralNominalDemandMerging.SameInputs models
    (Yulang.GeneralNominalFeedbackSites.recover Yulang.GeneralDictionaryJointMergeExample.before
      Yulang.GeneralDictionaryJointMergeExample.first)
    (Yulang.GeneralNominalFeedbackSites.recover Yulang.GeneralDictionaryJointMergeExample.before
      Yulang.GeneralDictionaryJointMergeExample.last)
Yulang.GeneralDictionaryJointMergeEnabled.guard : Yulang.GeneralNominalSupportChoices.MergeGuard
  Yulang.GeneralDictionaryJointMergeEnabled.tracked Yulang.GeneralDictionaryJointMergeExample.first
  Yulang.GeneralDictionaryJointMergeExample.last List.nil.{0}
Yulang.GeneralDictionaryJointMergeEnabled.distinct : ¬Yulang.GeneralNominalSaturationState.Alias
    Yulang.GeneralDictionaryJointMergeExample.before Yulang.GeneralDictionaryJointMergeExample.first.occurrence.identity
    Yulang.GeneralDictionaryJointMergeExample.last.occurrence.identity
Yulang.GeneralDictionaryJointMergeEnabled.actual_step : Yulang.GeneralNominalSupportSteps.Step
  Yulang.GeneralDictionaryJointMergeExample.registry Yulang.GeneralDictionaryJointMergeExample.first.occurrence
  Yulang.GeneralDictionaryJointMergeEnabled.tracked
  (Yulang.GeneralNominalSupportSteps.merge Yulang.GeneralDictionaryJointMergeEnabled.tracked
    Yulang.GeneralDictionaryJointMergeExample.first Yulang.GeneralDictionaryJointMergeExample.last List.nil.{0})
Yulang.GeneralDictionaryJointMergeEnabled.enabled_nonempty_joint : Yulang.GeneralNominalSupportSteps.Step
    Yulang.GeneralDictionaryJointMergeExample.registry Yulang.GeneralDictionaryJointMergeExample.first.occurrence
    Yulang.GeneralDictionaryJointMergeEnabled.tracked
    (Yulang.GeneralNominalSupportSteps.merge Yulang.GeneralDictionaryJointMergeEnabled.tracked
      Yulang.GeneralDictionaryJointMergeExample.first Yulang.GeneralDictionaryJointMergeExample.last List.nil.{0}) ∧
  Eq.{1}
      (Yulang.GeneralNominalDemandMerging.outputAtoms Yulang.GeneralDictionaryJointMergeExample.first
        Yulang.GeneralDictionaryJointMergeExample.last)
      (List.cons.{0}
        (Yulang.PresenceNormalForm.Atom.tyLe (Yulang.Core.PresenceGeneration.TyTerm.var 1)
          (Yulang.Core.PresenceGeneration.TyTerm.var 3))
        (List.cons.{0}
          (Yulang.PresenceNormalForm.Atom.tyLe (Yulang.Core.PresenceGeneration.TyTerm.var 3)
            (Yulang.Core.PresenceGeneration.TyTerm.var 1))
          List.nil.{0})) ∧
    Yulang.GeneralNominalJointCandidates.Joint Yulang.GeneralDictionaryJointMergeExample.registry
      (Yulang.GeneralNominalSupportSteps.merge Yulang.GeneralDictionaryJointMergeEnabled.tracked
          Yulang.GeneralDictionaryJointMergeExample.first Yulang.GeneralDictionaryJointMergeExample.last
          List.nil.{0}).current
      Yulang.GeneralDictionaryJointMergeExample.first.occurrence 7
Yulang.GeneralDictionaryJointMergeExample.terminal_checked : Yulang.GeneralDeclarations.DeclarationChecked
  Yulang.GeneralDeclarationExamples.constructors Yulang.GeneralDeclarationExamples.roles
  Yulang.GeneralDictionaryJointMergeExample.terminal
Yulang.GeneralDictionaryJointMergeExample.source_models : Yulang.GeneralNominalState.Models
  Yulang.GeneralDictionaryJointMergeExample.source Yulang.GeneralDictionaryJointMergeExample.model
Yulang.GeneralDictionaryJointMergeExample.report_exact : Eq.{1}
  (Yulang.GeneralNominalRecursiveCandidates.report Yulang.GeneralDictionaryJointMergeExample.context
    Yulang.GeneralDictionaryJointMergeExample.terminal (List.cons.{0} (Prod.mk.{0, 0} 1 1) List.nil.{0}))
  { captures := List.cons.{0} { name := 0, bounds := Prod.mk.{0, 0} 1 1, origin := none.{0} } List.nil.{0},
    checked := List.cons.{0} (Prod.mk.{0, 0} 1 1) (List.cons.{0} (Prod.mk.{0, 0} 1 1) List.nil.{0}) }
Yulang.GeneralDictionaryJointMergeExample.emissions_empty : ∀ (identity : Nat)
  (capture : Yulang.GeneralDeclarationDemands.Capture)
  (allocate :
    (clause : Yulang.GeneralDeclarations.Clause) →
      Yulang.GeneralDeclarationDemands.Allocation Yulang.GeneralDeclarationExamples.roles clause),
  Eq.{1}
    (Yulang.GeneralCanonicalChildOrder.canonicalEmit identity Yulang.GeneralDictionaryJointMergeExample.terminal
      Yulang.GeneralDictionaryJointMergeExample.terminal_checked capture allocate)
    List.nil.{0}
Yulang.GeneralDictionaryJointMergeExample.schema_exact : ∀ (identity target : Nat),
  Eq.{1}
    (Yulang.GeneralNominalRecursiveCandidates.generated Yulang.GeneralDictionaryJointMergeExample.registry
      Yulang.GeneralDictionaryJointMergeExample.context (Yulang.GeneralDictionaryJointMergeExample.root identity target)
      Yulang.GeneralDictionaryJointMergeExample.terminal Yulang.GeneralDictionaryJointMergeExample.terminal_checked
      (List.cons.{0} (Prod.mk.{0, 0} 1 1) List.nil.{0}))
    {
      tests :=
        List.cons.{0}
          (Prod.mk.{0, 0} (Yulang.GeneralNominalRecursiveInspection.Origin.source target)
            (Yulang.GeneralNominalRecursiveInspection.Test.scalar Yulang.Inference.Base.int))
          List.nil.{0} }
Yulang.GeneralDictionaryJointMergeExample.branch_models : ∀ (identity target : Nat),
  Ne.{1} target 0 →
    Yulang.GeneralNominalRecursiveCandidates.BranchModels Yulang.GeneralDictionaryJointMergeExample.registry
      Yulang.GeneralDictionaryJointMergeExample.context (Yulang.GeneralDictionaryJointMergeExample.root identity target)
      Yulang.GeneralDictionaryJointMergeExample.terminal Yulang.GeneralDictionaryJointMergeExample.terminal_checked
      (List.cons.{0} (Prod.mk.{0, 0} 1 1) List.nil.{0}) Yulang.GeneralDictionaryJointMergeExample.model
Yulang.GeneralDictionaryJointMergeExample.prepared : ∀ (identity target : Nat),
  Eq.{1} target 1 ∨ Eq.{1} target 3 →
    Yulang.GeneralNominalRecursiveCandidates.Prepared Yulang.GeneralDictionaryJointMergeExample.registry
      Yulang.GeneralDictionaryJointMergeExample.context (Yulang.GeneralDictionaryJointMergeExample.root identity target)
      Yulang.GeneralDictionaryJointMergeExample.terminal Yulang.GeneralDictionaryJointMergeExample.terminal_checked
Yulang.GeneralDictionaryJointMergeExample.before_models : Yulang.GeneralNominalSaturationState.Models
  Yulang.GeneralDictionaryJointMergeExample.before Yulang.GeneralDictionaryJointMergeExample.model
Yulang.GeneralDictionaryJointMergeExample.branch_at : ∀ (identity target : Nat),
  Eq.{1} target 1 ∨ Eq.{1} target 3 →
    Yulang.GeneralNominalJointCandidates.BranchAt Yulang.GeneralDictionaryJointMergeExample.registry
      Yulang.GeneralDictionaryJointMergeExample.before (Yulang.GeneralDictionaryJointMergeExample.root identity target)
      7 Yulang.GeneralDictionaryJointMergeExample.model
Yulang.GeneralDictionaryJointMergeExample.same_inputs : Yulang.GeneralNominalDemandMerging.SameInputs
  (Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryJointMergeExample.before)
  Yulang.GeneralDictionaryJointMergeExample.first Yulang.GeneralDictionaryJointMergeExample.last
Yulang.GeneralDictionaryJointMergeExample.dictionary_outputs : ∀ (identity target : Nat),
  Ne.{1} target 0 →
    Yulang.GeneralNominalDemandMerging.DictionaryOutputs Yulang.GeneralDictionaryJointMergeExample.meaning
      Yulang.GeneralDictionaryJointMergeExample.model
      (Yulang.GeneralNominalDemandMerging.pointSite (Yulang.GeneralDictionaryJointMergeExample.root identity target))
Yulang.GeneralDictionaryJointMergeExample.output_atoms_nonempty : Eq.{1}
  (Yulang.GeneralNominalDemandMerging.outputAtoms Yulang.GeneralDictionaryJointMergeExample.first
    Yulang.GeneralDictionaryJointMergeExample.last)
  (List.cons.{0}
    (Yulang.PresenceNormalForm.Atom.tyLe (Yulang.Core.PresenceGeneration.TyTerm.var 1)
      (Yulang.Core.PresenceGeneration.TyTerm.var 3))
    (List.cons.{0}
      (Yulang.PresenceNormalForm.Atom.tyLe (Yulang.Core.PresenceGeneration.TyTerm.var 3)
        (Yulang.Core.PresenceGeneration.TyTerm.var 1))
      List.nil.{0}))
Yulang.GeneralDictionaryJointMergeExample.output_atoms_hold : Yulang.PresenceNormalForm.All.{0, 0}
  Yulang.CommonNominalFullCarrier.model Yulang.GeneralDictionaryJointMergeExample.model
  (Yulang.GeneralNominalDemandMerging.outputAtoms Yulang.GeneralDictionaryJointMergeExample.first
    Yulang.GeneralDictionaryJointMergeExample.last)
Yulang.GeneralDictionaryJointMergeExample.merged_joint : Yulang.GeneralNominalJointCandidates.Joint
  Yulang.GeneralDictionaryJointMergeExample.registry
  (Yulang.GeneralNominalSaturationState.merge Yulang.GeneralDictionaryJointMergeExample.before
    Yulang.GeneralDictionaryJointMergeExample.first Yulang.GeneralDictionaryJointMergeExample.last)
  Yulang.GeneralDictionaryJointMergeExample.first.occurrence 7
Yulang.GeneralDictionaryJointMergeExample.source_evidence : ∀ (identity target : Nat),
  Eq.{1} target 1 ∨ Eq.{1} target 3 →
    Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralDictionaryJointMergeExample.registry
      Yulang.GeneralDictionaryJointMergeExample.context Yulang.GeneralDictionaryJointMergeExample.model
      (Yulang.GeneralDictionaryJointMergeExample.root identity target)
      (Yulang.CommonRoleOutermostResolver.Dictionary.node 7 List.nil.{0})
Yulang.GeneralDictionaryJointMergeExample.merged_evidence : Yulang.GeneralDictionaryRecursiveEvidence.Evidence
    Yulang.GeneralDictionaryJointMergeExample.registry
    (Yulang.GeneralNominalSaturationState.merge Yulang.GeneralDictionaryJointMergeExample.before
        Yulang.GeneralDictionaryJointMergeExample.first Yulang.GeneralDictionaryJointMergeExample.last).context
    Yulang.GeneralDictionaryJointMergeExample.model Yulang.GeneralDictionaryJointMergeExample.first.occurrence
    (Yulang.CommonRoleOutermostResolver.Dictionary.node 7 List.nil.{0}) ∧
  Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralDictionaryJointMergeExample.registry
    (Yulang.GeneralNominalSaturationState.merge Yulang.GeneralDictionaryJointMergeExample.before
        Yulang.GeneralDictionaryJointMergeExample.first Yulang.GeneralDictionaryJointMergeExample.last).context
    Yulang.GeneralDictionaryJointMergeExample.model Yulang.GeneralDictionaryJointMergeExample.last.occurrence
    (Yulang.CommonRoleOutermostResolver.Dictionary.node 7 List.nil.{0})
Yulang.GeneralDictionaryJointMergeJournalScope.bad_source_models : Yulang.GeneralNominalState.Models
  Yulang.GeneralDictionaryJointMergeExample.source Yulang.GeneralDictionaryJointMergeJournalScope.badModel
Yulang.GeneralDictionaryJointMergeJournalScope.bad_packet : ¬Yulang.GeneralDictionaryJointMergeJournalScope.lastPacket.Holds
    Yulang.GeneralDictionaryJointMergeJournalScope.badModel
Yulang.GeneralDictionaryJointMergeJournalScope.no_empty_facts_formation : ∀
  (current : Yulang.GeneralNominalSaturationState.State Yulang.GeneralDeclarationExamples.roles),
  Membership.mem.{0, 0} current.packets Yulang.GeneralDictionaryJointMergeJournalScope.lastPacket →
    ∀ (focus : Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles),
      ¬Yulang.GeneralNominalSupportSteps.SourceFormed Yulang.GeneralDictionaryJointMergeExample.registry focus
          { source := Yulang.GeneralDictionaryJointMergeExample.context, current := current }
@Yulang.GeneralDictionaryJointMergeResidual.separate_joint_merge_iff : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSaturationState.State roles)
  (first last : Yulang.GeneralNominalDemandMerging.Site roles),
  Membership.mem.{0, 0} state.sites first →
    ∀ (key : Nat),
      Yulang.GeneralNominalJointCandidates.Joint registry state first.occurrence key →
        Yulang.GeneralNominalJointCandidates.Joint registry state last.occurrence key →
          (Yulang.GeneralNominalJointCandidates.Joint registry
              (Yulang.GeneralNominalSaturationState.merge state first last) first.occurrence key ↔
            Yulang.GeneralDictionaryJointMergeResidual.Shared registry state first last key)
@Yulang.GeneralDictionaryJointMergeResidual.separate_joint_failure_iff : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSaturationState.State roles)
  (first last : Yulang.GeneralNominalDemandMerging.Site roles),
  Membership.mem.{0, 0} state.sites first →
    ∀ (key : Nat),
      Yulang.GeneralNominalJointCandidates.Joint registry state first.occurrence key →
        Yulang.GeneralNominalJointCandidates.Joint registry state last.occurrence key →
          (¬Yulang.GeneralNominalJointCandidates.Joint registry
                (Yulang.GeneralNominalSaturationState.merge state first last) first.occurrence key ↔
            ¬Yulang.GeneralDictionaryJointMergeResidual.Shared registry state first last key)
@Yulang.GeneralDictionaryJointMergeResidual.recorded_key_conflict : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSaturationState.State roles)
  (first last : Yulang.GeneralNominalDemandMerging.Site roles)
  (one two : Yulang.GeneralNominalSaturationState.Packet roles),
  Membership.mem.{0, 0} state.packets one →
    Membership.mem.{0, 0} state.packets two →
      Yulang.GeneralNominalSaturationState.Alias state first.occurrence.identity one.site.occurrence.identity →
        Yulang.GeneralNominalSaturationState.Alias state last.occurrence.identity two.site.occurrence.identity →
          Ne.{1} one.declaration.id two.declaration.id →
            ∀ (key : Nat),
              ¬Yulang.GeneralNominalJointCandidates.Joint registry
                  (Yulang.GeneralNominalSaturationState.merge state first last) first.occurrence key
@Yulang.GeneralDictionaryJointMergeSequence.sources_fold : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalSaturationState.State roles)
  (steps :
    List.{0}
      (Prod.{0, 0} (Yulang.GeneralNominalDemandMerging.Site roles) (Yulang.GeneralNominalDemandMerging.Site roles))),
  Yulang.GeneralDictionaryJointMergeSequence.Targets state steps →
    ∀ (source : Nat),
      Membership.mem.{0, 0}
          (Yulang.GeneralNominalState.sources
            (List.foldl.{0, 0}
                  (fun current pair =>
                    Yulang.GeneralNominalSaturationState.merge current (Prod.fst.{0, 0} pair) (Prod.snd.{0, 0} pair))
                  state steps).context.state)
          source ↔
        Membership.mem.{0, 0} (Yulang.GeneralNominalState.sources state.context.state) source
@Yulang.GeneralDictionaryJointMergeSequence.branch_fold : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSaturationState.State roles)
  (steps :
    List.{0}
      (Prod.{0, 0} (Yulang.GeneralNominalDemandMerging.Site roles) (Yulang.GeneralNominalDemandMerging.Site roles))),
  Yulang.GeneralDictionaryJointMergeSequence.Targets state steps →
    ∀ (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (key : Nat)
      (model : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.GeneralNominalJointCandidates.BranchAt registry
          (List.foldl.{0, 0}
            (fun current pair =>
              Yulang.GeneralNominalSaturationState.merge current (Prod.fst.{0, 0} pair) (Prod.snd.{0, 0} pair))
            state steps)
          root key model ↔
        Yulang.GeneralNominalJointCandidates.BranchAt registry state root key model ∧
          Yulang.PresenceNormalForm.All.{0, 0} Yulang.CommonNominalFullCarrier.model model
            (List.flatMap.{0, 0}
              (fun pair => Yulang.GeneralNominalDemandMerging.outputAtoms (Prod.fst.{0, 0} pair) (Prod.snd.{0, 0} pair))
              steps)
@Yulang.GeneralDictionaryJointMergeSequence.packets_fold : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalSaturationState.State roles)
  (steps :
    List.{0}
      (Prod.{0, 0} (Yulang.GeneralNominalDemandMerging.Site roles) (Yulang.GeneralNominalDemandMerging.Site roles))),
  Eq.{1}
    (List.foldl.{0, 0}
        (fun current pair =>
          Yulang.GeneralNominalSaturationState.merge current (Prod.fst.{0, 0} pair) (Prod.snd.{0, 0} pair))
        state steps).packets
    state.packets
@Yulang.GeneralDictionaryJointMergeSequence.sites_fold : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalSaturationState.State roles)
  (steps :
    List.{0}
      (Prod.{0, 0} (Yulang.GeneralNominalDemandMerging.Site roles) (Yulang.GeneralNominalDemandMerging.Site roles))),
  Eq.{1}
    (List.foldl.{0, 0}
        (fun current pair =>
          Yulang.GeneralNominalSaturationState.merge current (Prod.fst.{0, 0} pair) (Prod.snd.{0, 0} pair))
        state steps).sites
    state.sites
@Yulang.GeneralDictionaryJointMergeSequence.joint_fold : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSaturationState.State roles)
  (steps :
    List.{0}
      (Prod.{0, 0} (Yulang.GeneralNominalDemandMerging.Site roles) (Yulang.GeneralNominalDemandMerging.Site roles))),
  Yulang.GeneralDictionaryJointMergeSequence.Targets state steps →
    ∀ (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (key : Nat),
      have after :=
        List.foldl.{0, 0}
          (fun current pair =>
            Yulang.GeneralNominalSaturationState.merge current (Prod.fst.{0, 0} pair) (Prod.snd.{0, 0} pair))
          state steps;
      Yulang.GeneralNominalJointCandidates.Joint registry after root key ↔
        (∀ (packet : Yulang.GeneralNominalSaturationState.Packet roles),
            Membership.mem.{0, 0} state.packets packet →
              Yulang.GeneralNominalSaturationState.Alias after root.identity packet.site.occurrence.identity →
                Eq.{1} packet.declaration.id key) ∧
          Exists.{1} fun model =>
            Yulang.GeneralNominalSaturationState.Models state model ∧
              Yulang.PresenceNormalForm.All.{0, 0} Yulang.CommonNominalFullCarrier.model model
                  (List.flatMap.{0, 0}
                    (fun pair =>
                      Yulang.GeneralNominalDemandMerging.outputAtoms (Prod.fst.{0, 0} pair) (Prod.snd.{0, 0} pair))
                    steps) ∧
                Yulang.GeneralNominalJointCandidates.BranchAt registry state root key model ∧
                  ∀ (site : Yulang.GeneralNominalDemandMerging.Site roles),
                    Membership.mem.{0, 0} state.sites site →
                      Yulang.GeneralNominalSaturationState.Alias after root.identity site.occurrence.identity →
                        Yulang.GeneralNominalJointCandidates.BranchAt registry state site.occurrence key model
@Yulang.GeneralDictionaryJointMergeSequence.aliases_fold : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalSaturationState.State roles)
  (steps :
    List.{0}
      (Prod.{0, 0} (Yulang.GeneralNominalDemandMerging.Site roles) (Yulang.GeneralNominalDemandMerging.Site roles))),
  Eq.{1}
    (List.foldl.{0, 0}
        (fun current pair =>
          Yulang.GeneralNominalSaturationState.merge current (Prod.fst.{0, 0} pair) (Prod.snd.{0, 0} pair))
        state steps).aliases
    (HAppend.hAppend.{0, 0, 0}
      (List.map.{0, 0}
        (fun pair =>
          Prod.mk.{0, 0} (Prod.fst.{0, 0} pair).occurrence.identity (Prod.snd.{0, 0} pair).occurrence.identity)
        (List.reverse.{0} steps))
      state.aliases)
@Yulang.GeneralDictionaryJointMergeSequence.alias_edges_iff : ∀ {roles : Yulang.Roles.RoleDecls}
  (first last : Yulang.GeneralNominalSaturationState.State roles),
  (∀ (pair : Prod.{0, 0} Nat Nat), Membership.mem.{0, 0} first.aliases pair ↔ Membership.mem.{0, 0} last.aliases pair) →
    ∀ (a b : Nat),
      Yulang.GeneralNominalSaturationState.Alias first a b ↔ Yulang.GeneralNominalSaturationState.Alias last a b
@Yulang.GeneralDictionaryJointMergeSequence.alias_events_iff : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalSaturationState.State roles)
  (first last :
    List.{0}
      (Prod.{0, 0} (Yulang.GeneralNominalDemandMerging.Site roles) (Yulang.GeneralNominalDemandMerging.Site roles))),
  (∀
      (pair :
        Prod.{0, 0} (Yulang.GeneralNominalDemandMerging.Site roles) (Yulang.GeneralNominalDemandMerging.Site roles)),
      Membership.mem.{0, 0} first pair ↔ Membership.mem.{0, 0} last pair) →
    ∀ (a b : Nat),
      Yulang.GeneralNominalSaturationState.Alias
          (List.foldl.{0, 0}
            (fun current pair =>
              Yulang.GeneralNominalSaturationState.merge current (Prod.fst.{0, 0} pair) (Prod.snd.{0, 0} pair))
            state first)
          a b ↔
        Yulang.GeneralNominalSaturationState.Alias
          (List.foldl.{0, 0}
            (fun current pair =>
              Yulang.GeneralNominalSaturationState.merge current (Prod.fst.{0, 0} pair) (Prod.snd.{0, 0} pair))
            state last)
          a b
@Yulang.GeneralDictionaryJointMergeSequence.joint_events_iff : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSaturationState.State roles)
  (first last :
    List.{0}
      (Prod.{0, 0} (Yulang.GeneralNominalDemandMerging.Site roles) (Yulang.GeneralNominalDemandMerging.Site roles))),
  (∀
      (pair :
        Prod.{0, 0} (Yulang.GeneralNominalDemandMerging.Site roles) (Yulang.GeneralNominalDemandMerging.Site roles)),
      Membership.mem.{0, 0} first pair ↔ Membership.mem.{0, 0} last pair) →
    Yulang.GeneralDictionaryJointMergeSequence.Targets state first →
      ∀ (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (key : Nat),
        Yulang.GeneralNominalJointCandidates.Joint registry
            (List.foldl.{0, 0}
              (fun current pair =>
                Yulang.GeneralNominalSaturationState.merge current (Prod.fst.{0, 0} pair) (Prod.snd.{0, 0} pair))
              state first)
            root key ↔
          Yulang.GeneralNominalJointCandidates.Joint registry
            (List.foldl.{0, 0}
              (fun current pair =>
                Yulang.GeneralNominalSaturationState.merge current (Prod.fst.{0, 0} pair) (Prod.snd.{0, 0} pair))
              state last)
            root key
@Yulang.GeneralDictionaryMergeSequence.models_fold : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalSaturationState.State roles)
  (steps :
    List.{0}
      (Prod.{0, 0} (Yulang.GeneralNominalDemandMerging.Site roles) (Yulang.GeneralNominalDemandMerging.Site roles)))
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalSaturationState.Models
      (List.foldl.{0, 0}
        (fun current pair =>
          Yulang.GeneralNominalSaturationState.merge current (Prod.fst.{0, 0} pair) (Prod.snd.{0, 0} pair))
        state steps)
      model ↔
    Yulang.GeneralNominalSaturationState.Models state model ∧
      Yulang.PresenceNormalForm.All.{0, 0} Yulang.CommonNominalFullCarrier.model model
        (List.flatMap.{0, 0}
          (fun pair => Yulang.GeneralNominalDemandMerging.outputAtoms (Prod.fst.{0, 0} pair) (Prod.snd.{0, 0} pair))
          steps)
@Yulang.GeneralDictionaryMergeSequence.evidence_fold : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSaturationState.State roles)
  (steps :
    List.{0}
      (Prod.{0, 0} (Yulang.GeneralNominalDemandMerging.Site roles) (Yulang.GeneralNominalDemandMerging.Site roles)))
  (model : Yulang.GeneralNominalCommonBridge.Assignment) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (payload : Yulang.GeneralDictionaryReadback.Payload),
  Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry
      (List.foldl.{0, 0}
          (fun current pair =>
            Yulang.GeneralNominalSaturationState.merge current (Prod.fst.{0, 0} pair) (Prod.snd.{0, 0} pair))
          state steps).context
      model root payload ↔
    Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry state.context model root payload ∧
      Yulang.PresenceNormalForm.All.{0, 0} Yulang.CommonNominalFullCarrier.model model
        (List.flatMap.{0, 0}
          (fun pair => Yulang.GeneralNominalDemandMerging.outputAtoms (Prod.fst.{0, 0} pair) (Prod.snd.{0, 0} pair))
          steps)
@Yulang.GeneralDictionaryMergeSequence.evidence_at_final_model : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSaturationState.State roles)
  (steps :
    List.{0}
      (Prod.{0, 0} (Yulang.GeneralNominalDemandMerging.Site roles) (Yulang.GeneralNominalDemandMerging.Site roles)))
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalSaturationState.Models
      (List.foldl.{0, 0}
        (fun current pair =>
          Yulang.GeneralNominalSaturationState.merge current (Prod.fst.{0, 0} pair) (Prod.snd.{0, 0} pair))
        state steps)
      model →
    ∀ (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (payload : Yulang.GeneralDictionaryReadback.Payload),
      Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry state.context model root payload →
        Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry
          (List.foldl.{0, 0}
              (fun current pair =>
                Yulang.GeneralNominalSaturationState.merge current (Prod.fst.{0, 0} pair) (Prod.snd.{0, 0} pair))
              state steps).context
          model root payload
@Yulang.GeneralDictionaryMergeSequence.event_atoms_iff : ∀ {roles : Yulang.Roles.RoleDecls}
  (first last :
    List.{0}
      (Prod.{0, 0} (Yulang.GeneralNominalDemandMerging.Site roles) (Yulang.GeneralNominalDemandMerging.Site roles))),
  (∀
      (pair :
        Prod.{0, 0} (Yulang.GeneralNominalDemandMerging.Site roles) (Yulang.GeneralNominalDemandMerging.Site roles)),
      Membership.mem.{0, 0} first pair ↔ Membership.mem.{0, 0} last pair) →
    ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.PresenceNormalForm.All.{0, 0} Yulang.CommonNominalFullCarrier.model model
          (List.flatMap.{0, 0}
            (fun pair => Yulang.GeneralNominalDemandMerging.outputAtoms (Prod.fst.{0, 0} pair) (Prod.snd.{0, 0} pair))
            first) ↔
        Yulang.PresenceNormalForm.All.{0, 0} Yulang.CommonNominalFullCarrier.model model
          (List.flatMap.{0, 0}
            (fun pair => Yulang.GeneralNominalDemandMerging.outputAtoms (Prod.fst.{0, 0} pair) (Prod.snd.{0, 0} pair))
            last)
@Yulang.GeneralDictionaryMergeSequence.models_events_iff : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalSaturationState.State roles)
  (first last :
    List.{0}
      (Prod.{0, 0} (Yulang.GeneralNominalDemandMerging.Site roles) (Yulang.GeneralNominalDemandMerging.Site roles))),
  (∀
      (pair :
        Prod.{0, 0} (Yulang.GeneralNominalDemandMerging.Site roles) (Yulang.GeneralNominalDemandMerging.Site roles)),
      Membership.mem.{0, 0} first pair ↔ Membership.mem.{0, 0} last pair) →
    ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.GeneralNominalSaturationState.Models
          (List.foldl.{0, 0}
            (fun current pair =>
              Yulang.GeneralNominalSaturationState.merge current (Prod.fst.{0, 0} pair) (Prod.snd.{0, 0} pair))
            state first)
          model ↔
        Yulang.GeneralNominalSaturationState.Models
          (List.foldl.{0, 0}
            (fun current pair =>
              Yulang.GeneralNominalSaturationState.merge current (Prod.fst.{0, 0} pair) (Prod.snd.{0, 0} pair))
            state last)
          model
@Yulang.GeneralDictionaryMergeSequence.evidence_events_iff : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSaturationState.State roles)
  (first last :
    List.{0}
      (Prod.{0, 0} (Yulang.GeneralNominalDemandMerging.Site roles) (Yulang.GeneralNominalDemandMerging.Site roles))),
  (∀
      (pair :
        Prod.{0, 0} (Yulang.GeneralNominalDemandMerging.Site roles) (Yulang.GeneralNominalDemandMerging.Site roles)),
      Membership.mem.{0, 0} first pair ↔ Membership.mem.{0, 0} last pair) →
    ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
      (payload : Yulang.GeneralDictionaryReadback.Payload),
      Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry
          (List.foldl.{0, 0}
              (fun current pair =>
                Yulang.GeneralNominalSaturationState.merge current (Prod.fst.{0, 0} pair) (Prod.snd.{0, 0} pair))
              state first).context
          model root payload ↔
        Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry
          (List.foldl.{0, 0}
              (fun current pair =>
                Yulang.GeneralNominalSaturationState.merge current (Prod.fst.{0, 0} pair) (Prod.snd.{0, 0} pair))
              state last).context
          model root payload
Yulang.GeneralDictionaryOutputMergeReachable.checked : Yulang.GeneralDeclarations.DeclarationChecked
  Yulang.GeneralDeclarationExamples.constructors Yulang.GeneralDeclarationExamples.roles
  Yulang.GeneralDictionaryOutputMergeReachable.declaration
Yulang.GeneralDictionaryOutputMergeReachable.registry_checked : Yulang.GeneralDeclarations.Checked
  Yulang.GeneralDictionaryOutputMergeReachable.registry
Yulang.GeneralDictionaryOutputMergeReachable.all_source_decisions : ∀
  (root : Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles),
  (∀ (index : Fin (Yulang.GeneralDeclarationExamples.roles root.demand.role).arity),
      Eq.{1} (root.demand.arguments index) (Prod.mk.{0, 0} 0 0)) →
    Yulang.GeneralNominalSupport.DecisionGuard (Yulang.GeneralDictionaryOutputMergeReachable.start root)
      Yulang.GeneralDictionaryOutputMergeReachable.registry root List.nil.{0}
Yulang.GeneralDictionaryOutputMergeReachable.query : Eq.{1}
  (Yulang.GeneralNominalInspection.queries (Yulang.GeneralNominalExamples.state true)
    Yulang.GeneralNominalExamples.interpretation Yulang.GeneralDictionaryOutputMergeReachable.declaration)
  (List.cons.{0}
    (Yulang.GeneralNominalInspection.Query.nominal 0
      (List.cons.{0} (Yulang.GeneralNominalInspection.Query.variables (List.cons.{0} 0 List.nil.{0})) List.nil.{0}))
    List.nil.{0})
Yulang.GeneralDictionaryOutputMergeReachable.output_nonzero : ∀ (n : Nat),
  Ne.{1} (Yulang.GeneralDictionaryOutputMergeReachable.outputTarget n) 0
Yulang.GeneralDictionaryOutputMergeReachable.schema : Eq.{1}
  (Yulang.GeneralNominalRecursiveCandidates.generated Yulang.GeneralDictionaryOutputMergeReachable.registry
    (Yulang.GeneralNominalExamples.context true) Yulang.GeneralNominalExamples.displayRoot
    Yulang.GeneralDictionaryOutputMergeReachable.declaration Yulang.GeneralDictionaryOutputMergeReachable.checked
    (List.cons.{0} (Prod.mk.{0, 0} 0 0) List.nil.{0}))
  {
    tests :=
      List.cons.{0}
        (Prod.mk.{0, 0}
          (Yulang.GeneralNominalRecursiveInspection.Origin.source
            (Yulang.GeneralDictionaryOutputMergeReachable.outputTarget 10))
          (Yulang.GeneralNominalRecursiveInspection.Test.scalar Yulang.Inference.Base.int))
        (List.cons.{0}
          (Prod.mk.{0, 0}
            (Yulang.GeneralNominalRecursiveInspection.Origin.source
              (Yulang.GeneralDictionaryOutputMergeReachable.outputTarget 11))
            (Yulang.GeneralNominalRecursiveInspection.Test.scalar Yulang.Inference.Base.int))
          List.nil.{0}) }
Yulang.GeneralDictionaryOutputMergeReachable.branch : Yulang.GeneralNominalRecursiveCandidates.BranchModels
  Yulang.GeneralDictionaryOutputMergeReachable.registry (Yulang.GeneralNominalExamples.context true)
  Yulang.GeneralNominalExamples.displayRoot Yulang.GeneralDictionaryOutputMergeReachable.declaration
  Yulang.GeneralDictionaryOutputMergeReachable.checked (List.cons.{0} (Prod.mk.{0, 0} 0 0) List.nil.{0})
  Yulang.GeneralNominalExamples.model
Yulang.GeneralDictionaryOutputMergeReachable.prepared : Yulang.GeneralNominalRecursiveCandidates.Prepared
  Yulang.GeneralDictionaryOutputMergeReachable.registry (Yulang.GeneralNominalExamples.context true)
  Yulang.GeneralNominalExamples.displayRoot Yulang.GeneralDictionaryOutputMergeReachable.declaration
  Yulang.GeneralDictionaryOutputMergeReachable.checked
Yulang.GeneralDictionaryOutputMergeReachable.survivor : Yulang.GeneralNominalRecursiveCandidates.Survivor
  Yulang.GeneralDictionaryOutputMergeReachable.registry (Yulang.GeneralNominalExamples.context true)
  Yulang.GeneralNominalExamples.displayRoot 1 Yulang.GeneralDictionaryOutputMergeReachable.children
Yulang.GeneralDictionaryOutputMergeReachable.selected : Yulang.GeneralNominalSupportBoundary.Local
  Yulang.GeneralDictionaryOutputMergeReachable.registry
  (Yulang.GeneralDictionaryOutputMergeReachable.start Yulang.GeneralNominalExamples.displayRoot)
  Yulang.GeneralNominalExamples.displayRoot
  (Yulang.CommonRoleOutermostResolver.Frontier.selected.{0} 1 Yulang.GeneralDictionaryOutputMergeReachable.children)
Yulang.GeneralDictionaryOutputMergeReachable.children_exact : Eq.{1}
  Yulang.GeneralDictionaryOutputMergeReachable.children
  (List.cons.{0} (Yulang.GeneralDictionaryOutputMergeReachable.child 10)
    (List.cons.{0} (Yulang.GeneralDictionaryOutputMergeReachable.child 11) List.nil.{0}))
Yulang.GeneralDictionaryOutputMergeReachable.enabled : Yulang.GeneralNominalFeedbackSteps.Installable
  Yulang.GeneralDictionaryOutputMergeReachable.registry
  (Yulang.GeneralDictionaryOutputMergeReachable.start Yulang.GeneralNominalExamples.displayRoot).current
  Yulang.GeneralDictionaryOutputMergeReachable.packet
Yulang.GeneralDictionaryOutputMergeReachable.packet_guard : Yulang.GeneralNominalSupportSteps.PacketGuard
  (Yulang.GeneralDictionaryOutputMergeReachable.start Yulang.GeneralNominalExamples.displayRoot)
  Yulang.GeneralDictionaryOutputMergeReachable.packet List.nil.{0}
Yulang.GeneralDictionaryOutputMergeReachable.novel : ¬Yulang.GeneralNominalFeedbackSteps.Committed
    (Yulang.GeneralDictionaryOutputMergeReachable.start Yulang.GeneralNominalExamples.displayRoot).current
    Yulang.GeneralDictionaryOutputMergeReachable.packet
Yulang.GeneralDictionaryOutputMergeReachable.source : Yulang.GeneralNominalSourceFormation.InitialSource
  Yulang.GeneralDictionaryOutputMergeReachable.registry (Yulang.GeneralNominalExamples.context true)
  Yulang.GeneralNominalExamples.displayRoot
Yulang.GeneralDictionaryOutputMergeReachable.before_scheduled : Yulang.GeneralDictionaryEarlyMergeChoices.Scheduled
  Yulang.GeneralDictionaryOutputMergeReachable.registry Yulang.GeneralNominalExamples.displayRoot
  Yulang.GeneralDictionaryOutputMergeReachable.before
Yulang.GeneralDictionaryOutputMergeReachable.before_model : Yulang.GeneralNominalSaturationState.Models
  Yulang.GeneralDictionaryOutputMergeReachable.before.current Yulang.GeneralNominalExamples.model
Yulang.GeneralDictionaryOutputMergeReachable.site_present : ∀ (n : Nat),
  Eq.{1} n 10 ∨ Eq.{1} n 11 →
    Membership.mem.{0, 0} Yulang.GeneralDictionaryOutputMergeReachable.before.current.sites
      (Yulang.GeneralDictionaryOutputMergeReachable.site n)
Yulang.GeneralDictionaryOutputMergeReachable.inputs_same : Yulang.GeneralNominalFeedbackSites.SameInputs
  Yulang.GeneralDictionaryOutputMergeReachable.before.current (Yulang.GeneralDictionaryOutputMergeReachable.site 10)
  (Yulang.GeneralDictionaryOutputMergeReachable.site 11)
Yulang.GeneralDictionaryOutputMergeReachable.actual_early_merge : Yulang.GeneralDictionaryEarlyMergeChoices.Scheduled
    Yulang.GeneralDictionaryOutputMergeReachable.registry Yulang.GeneralNominalExamples.displayRoot
    Yulang.GeneralDictionaryOutputMergeReachable.finish ∧
  Yulang.GeneralNominalSupportSteps.Step Yulang.GeneralDictionaryOutputMergeReachable.registry
      Yulang.GeneralNominalExamples.displayRoot Yulang.GeneralDictionaryOutputMergeReachable.before
      Yulang.GeneralDictionaryOutputMergeReachable.finish ∧
    Ne.{1} Yulang.GeneralDictionaryOutputMergeReachable.finish.current.packets List.nil.{0} ∧
      Ne.{1} Yulang.GeneralDictionaryOutputMergeReachable.finish.current.aliases List.nil.{0}
Yulang.GeneralDictionaryOutputMergeReachable.finish_model : Yulang.GeneralNominalSaturationState.Models
  Yulang.GeneralDictionaryOutputMergeReachable.finish.current Yulang.GeneralNominalExamples.model
Yulang.GeneralDictionaryOutputMergeReachable.actual_path : Yulang.B4Target.Steps.{1}
  (Yulang.GeneralNominalSupportSteps.Step Yulang.GeneralDictionaryOutputMergeReachable.registry
    Yulang.GeneralNominalExamples.displayRoot)
  (Yulang.GeneralDictionaryOutputMergeReachable.start Yulang.GeneralNominalExamples.displayRoot)
  Yulang.GeneralDictionaryOutputMergeReachable.finish
Yulang.GeneralDictionaryOutputMergeReachable.reachable : Yulang.B4TargetV5.Reachable.{0}
  (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
  Yulang.GeneralDictionaryOutputMergeReachable.registry Yulang.GeneralNominalExamples.displayRoot
  Yulang.GeneralDictionaryOutputMergeReachable.finish
Yulang.GeneralDictionaryOutputMergeReachable.inhabited_early_merge : Yulang.B4TargetV5.Reachable.{0}
    (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
    Yulang.GeneralDictionaryOutputMergeReachable.registry Yulang.GeneralNominalExamples.displayRoot
    Yulang.GeneralDictionaryOutputMergeReachable.finish ∧
  Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryOutputMergeReachable.finish.current
      Yulang.GeneralNominalExamples.model ∧
    Ne.{1} Yulang.GeneralDictionaryOutputMergeReachable.finish.current.packets List.nil.{0} ∧
      Ne.{1} Yulang.GeneralDictionaryOutputMergeReachable.finish.current.aliases List.nil.{0} ∧
        Yulang.GeneralDictionarySupportChoices.Coherent Yulang.GeneralDictionaryOutputMergeReachable.finish.current
Yulang.GeneralDictionaryOutputMergeReachable.output_atoms_exact : Eq.{1}
  (Yulang.GeneralNominalDemandMerging.outputAtoms (Yulang.GeneralDictionaryOutputMergeReachable.site 10)
    (Yulang.GeneralDictionaryOutputMergeReachable.site 11))
  (List.cons.{0}
    (Yulang.PresenceNormalForm.Atom.tyLe
      (Yulang.Core.PresenceGeneration.TyTerm.var (Yulang.GeneralDictionaryOutputMergeReachable.outputTarget 10))
      (Yulang.Core.PresenceGeneration.TyTerm.var (Yulang.GeneralDictionaryOutputMergeReachable.outputTarget 11)))
    (List.cons.{0}
      (Yulang.PresenceNormalForm.Atom.tyLe
        (Yulang.Core.PresenceGeneration.TyTerm.var (Yulang.GeneralDictionaryOutputMergeReachable.outputTarget 11))
        (Yulang.Core.PresenceGeneration.TyTerm.var (Yulang.GeneralDictionaryOutputMergeReachable.outputTarget 10)))
      List.nil.{0}))
Yulang.GeneralDictionaryOutputMergeReachable.output_targets_distinct : Ne.{1}
  (Yulang.GeneralDictionaryOutputMergeReachable.outputTarget 10)
  (Yulang.GeneralDictionaryOutputMergeReachable.outputTarget 11)
Yulang.GeneralDictionaryOutputMergeReachable.finish_sourceformed : Yulang.GeneralNominalSupportSteps.SourceFormed
  Yulang.GeneralDictionaryOutputMergeReachable.registry Yulang.GeneralNominalExamples.displayRoot
  Yulang.GeneralDictionaryOutputMergeReachable.finish
Yulang.GeneralDictionaryOutputMergeReachable.reachable_nonempty_output_merge : Yulang.GeneralNominalSupportSteps.SourceFormed
    Yulang.GeneralDictionaryOutputMergeReachable.registry Yulang.GeneralNominalExamples.displayRoot
    Yulang.GeneralDictionaryOutputMergeReachable.finish ∧
  Yulang.B4TargetV5.Reachable.{0}
      (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
      Yulang.GeneralDictionaryOutputMergeReachable.registry Yulang.GeneralNominalExamples.displayRoot
      Yulang.GeneralDictionaryOutputMergeReachable.finish ∧
    Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryOutputMergeReachable.finish.current
        Yulang.GeneralNominalExamples.model ∧
      Ne.{1} (Yulang.GeneralDictionaryOutputMergeReachable.outputTarget 10)
          (Yulang.GeneralDictionaryOutputMergeReachable.outputTarget 11) ∧
        Ne.{1}
          (Yulang.GeneralNominalDemandMerging.outputAtoms (Yulang.GeneralDictionaryOutputMergeReachable.site 10)
            (Yulang.GeneralDictionaryOutputMergeReachable.site 11))
          List.nil.{0}
Yulang.GeneralDictionaryOutputMergeRootEvidence.parent_instance : Yulang.GeneralDictionaryRecursiveEvidence.Instance
  Yulang.GeneralDictionaryOutputMergeSuccess.registry (Yulang.GeneralNominalExamples.context true)
  Yulang.GeneralNominalExamples.model Yulang.GeneralNominalExamples.displayRoot 1
  (List.cons.{0} (Yulang.GeneralDictionaryOutputMergeSuccess.child 10)
    (List.cons.{0} (Yulang.GeneralDictionaryOutputMergeSuccess.child 11) List.nil.{0}))
Yulang.GeneralDictionaryOutputMergeRootEvidence.current_parent_instance : Yulang.GeneralDictionaryRecursiveEvidence.Instance
  Yulang.GeneralDictionaryOutputMergeSuccess.registry Yulang.GeneralDictionaryOutputMergeSuccess.current
  Yulang.GeneralNominalExamples.model Yulang.GeneralNominalExamples.displayRoot 1
  (List.cons.{0} (Yulang.GeneralDictionaryOutputMergeSuccess.child 10)
    (List.cons.{0} (Yulang.GeneralDictionaryOutputMergeSuccess.child 11) List.nil.{0}))
Yulang.GeneralDictionaryOutputMergeRootEvidence.root_evidence : Yulang.GeneralDictionaryRecursiveEvidence.Evidence
  Yulang.GeneralDictionaryOutputMergeSuccess.registry Yulang.GeneralDictionaryOutputMergeSuccess.current
  Yulang.GeneralNominalExamples.model Yulang.GeneralNominalExamples.displayRoot
  Yulang.GeneralDictionaryOutputMergeRootEvidence.rootPayload
Yulang.GeneralDictionaryOutputMergeRootEvidence.reachable_full_dictionary : Yulang.GeneralNominalSupportSteps.SourceFormed
    Yulang.GeneralDictionaryOutputMergeSuccess.registry Yulang.GeneralNominalExamples.displayRoot
    Yulang.GeneralDictionaryOutputMergeSuccess.finish ∧
  Yulang.B4TargetV5.Reachable.{0}
      (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
      Yulang.GeneralDictionaryOutputMergeSuccess.registry Yulang.GeneralNominalExamples.displayRoot
      Yulang.GeneralDictionaryOutputMergeSuccess.finish ∧
    Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryOutputMergeSuccess.finish.current
        Yulang.GeneralNominalExamples.model ∧
      Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralDictionaryOutputMergeSuccess.registry
          Yulang.GeneralDictionaryOutputMergeSuccess.current Yulang.GeneralNominalExamples.model
          Yulang.GeneralNominalExamples.displayRoot Yulang.GeneralDictionaryOutputMergeRootEvidence.rootPayload ∧
        Yulang.GeneralNominalJointCandidates.Joint Yulang.GeneralDictionaryOutputMergeSuccess.registry
            Yulang.GeneralDictionaryOutputMergeSuccess.finish.current
            (Yulang.GeneralDictionaryOutputMergeSuccess.child 10) 7 ∧
          Ne.{1} (Yulang.GeneralDictionaryOutputMergeSuccess.outputTarget 10)
              (Yulang.GeneralDictionaryOutputMergeSuccess.outputTarget 11) ∧
            Ne.{1}
              (Yulang.GeneralNominalDemandMerging.outputAtoms (Yulang.GeneralDictionaryOutputMergeSuccess.site 10)
                (Yulang.GeneralDictionaryOutputMergeSuccess.site 11))
              List.nil.{0}
Yulang.GeneralDictionaryOutputMergeScalarFacts.packet_present : Membership.mem.{0, 0}
  Yulang.GeneralDictionaryOutputMergeReachable.before.current.packets
  Yulang.GeneralDictionaryOutputMergeReachable.packet
Yulang.GeneralDictionaryOutputMergeScalarFacts.requests : ∀ (n : Nat),
  Eq.{1} n 10 ∨ Eq.{1} n 11 →
    Yulang.GeneralDictionaryScalarJournalMerge.Requests Yulang.GeneralDictionaryOutputMergeReachable.packet
      (Yulang.GeneralDictionaryOutputMergeReachable.site n) fun x => Yulang.Inference.Base.int
Yulang.GeneralDictionaryOutputMergeScalarFacts.all_models_unchanged : ∀
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryOutputMergeReachable.finish.current model ↔
    Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryOutputMergeReachable.before.current model
Yulang.GeneralDictionaryOutputMergeScalarFacts.all_models_evidence_unchanged : ∀
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryOutputMergeReachable.before.current model →
    ∀ (root : Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)
      (payload : Yulang.GeneralDictionaryReadback.Payload),
      Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralDictionaryOutputMergeReachable.registry
          Yulang.GeneralDictionaryOutputMergeReachable.finish.current.context model root payload ↔
        Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralDictionaryOutputMergeReachable.registry
          Yulang.GeneralDictionaryOutputMergeReachable.before.current.context model root payload
Yulang.GeneralDictionaryOutputMergeScope.child_no_branch : ∀
  (state : Yulang.GeneralNominalSaturationState.State Yulang.GeneralDeclarationExamples.roles) (n key : Nat)
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  ¬Yulang.GeneralNominalJointCandidates.BranchAt Yulang.GeneralDictionaryOutputMergeReachable.registry state
      (Yulang.GeneralDictionaryOutputMergeReachable.child n) key model
Yulang.GeneralDictionaryOutputMergeScope.child_no_joint : ∀
  (state : Yulang.GeneralNominalSaturationState.State Yulang.GeneralDeclarationExamples.roles) (n key : Nat),
  ¬Yulang.GeneralNominalJointCandidates.Joint Yulang.GeneralDictionaryOutputMergeReachable.registry state
      (Yulang.GeneralDictionaryOutputMergeReachable.child n) key
Yulang.GeneralDictionaryOutputMergeScope.child_no_instance : ∀ (context : Yulang.GeneralNominalCandidates.Context)
  (model : Yulang.GeneralNominalCommonBridge.Assignment) (n key : Nat)
  (children : List.{0} (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)),
  ¬Yulang.GeneralDictionaryRecursiveEvidence.Instance Yulang.GeneralDictionaryOutputMergeReachable.registry context
      model (Yulang.GeneralDictionaryOutputMergeReachable.child n) key children
Yulang.GeneralDictionaryOutputMergeScope.child_no_evidence : ∀ (context : Yulang.GeneralNominalCandidates.Context)
  (model : Yulang.GeneralNominalCommonBridge.Assignment) (n : Nat) (payload : Yulang.GeneralDictionaryReadback.Payload),
  ¬Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralDictionaryOutputMergeReachable.registry context
      model (Yulang.GeneralDictionaryOutputMergeReachable.child n) payload
Yulang.GeneralDictionaryOutputMergeScope.reachable_without_child_evidence : Yulang.GeneralNominalSupportSteps.SourceFormed
    Yulang.GeneralDictionaryOutputMergeReachable.registry Yulang.GeneralNominalExamples.displayRoot
    Yulang.GeneralDictionaryOutputMergeReachable.finish ∧
  Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryOutputMergeReachable.finish.current
      Yulang.GeneralNominalExamples.model ∧
    ∀ (n : Nat) (payload : Yulang.GeneralDictionaryReadback.Payload),
      ¬Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralDictionaryOutputMergeReachable.registry
          Yulang.GeneralDictionaryOutputMergeReachable.finish.current.context Yulang.GeneralNominalExamples.model
          (Yulang.GeneralDictionaryOutputMergeReachable.child n) payload
Yulang.GeneralDictionaryOutputMergeSuccess.checked : Yulang.GeneralDeclarations.DeclarationChecked
  Yulang.GeneralDeclarationExamples.constructors Yulang.GeneralDeclarationExamples.roles
  Yulang.GeneralDictionaryOutputMergeSuccess.declaration
Yulang.GeneralDictionaryOutputMergeSuccess.registry_checked : Yulang.GeneralDeclarations.Checked
  Yulang.GeneralDictionaryOutputMergeSuccess.registry
Yulang.GeneralDictionaryOutputMergeSuccess.all_source_decisions : ∀
  (root : Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles),
  (∀ (index : Fin (Yulang.GeneralDeclarationExamples.roles root.demand.role).arity),
      Eq.{1} (root.demand.arguments index) (Prod.mk.{0, 0} 0 0)) →
    Yulang.GeneralNominalSupport.DecisionGuard (Yulang.GeneralDictionaryOutputMergeSuccess.start root)
      Yulang.GeneralDictionaryOutputMergeSuccess.registry root List.nil.{0}
Yulang.GeneralDictionaryOutputMergeSuccess.query : Eq.{1}
  (Yulang.GeneralNominalInspection.queries (Yulang.GeneralNominalExamples.state true)
    Yulang.GeneralNominalExamples.interpretation Yulang.GeneralDictionaryOutputMergeSuccess.declaration)
  (List.cons.{0}
    (Yulang.GeneralNominalInspection.Query.nominal 0
      (List.cons.{0} (Yulang.GeneralNominalInspection.Query.variables (List.cons.{0} 0 List.nil.{0})) List.nil.{0}))
    List.nil.{0})
Yulang.GeneralDictionaryOutputMergeSuccess.output_nonzero : ∀ (n : Nat),
  Ne.{1} (Yulang.GeneralDictionaryOutputMergeSuccess.outputTarget n) 0
Yulang.GeneralDictionaryOutputMergeSuccess.schema : Eq.{1}
  (Yulang.GeneralNominalRecursiveCandidates.generated Yulang.GeneralDictionaryOutputMergeSuccess.registry
    (Yulang.GeneralNominalExamples.context true) Yulang.GeneralNominalExamples.displayRoot
    Yulang.GeneralDictionaryOutputMergeSuccess.declaration Yulang.GeneralDictionaryOutputMergeSuccess.checked
    (List.cons.{0} (Prod.mk.{0, 0} 0 0) List.nil.{0}))
  {
    tests :=
      List.cons.{0}
        (Prod.mk.{0, 0}
          (Yulang.GeneralNominalRecursiveInspection.Origin.source
            (Yulang.GeneralDictionaryOutputMergeSuccess.outputTarget 10))
          (Yulang.GeneralNominalRecursiveInspection.Test.scalar Yulang.Inference.Base.int))
        (List.cons.{0}
          (Prod.mk.{0, 0}
            (Yulang.GeneralNominalRecursiveInspection.Origin.source
              (Yulang.GeneralDictionaryOutputMergeSuccess.outputTarget 11))
            (Yulang.GeneralNominalRecursiveInspection.Test.scalar Yulang.Inference.Base.int))
          List.nil.{0}) }
Yulang.GeneralDictionaryOutputMergeSuccess.branch : Yulang.GeneralNominalRecursiveCandidates.BranchModels
  Yulang.GeneralDictionaryOutputMergeSuccess.registry (Yulang.GeneralNominalExamples.context true)
  Yulang.GeneralNominalExamples.displayRoot Yulang.GeneralDictionaryOutputMergeSuccess.declaration
  Yulang.GeneralDictionaryOutputMergeSuccess.checked (List.cons.{0} (Prod.mk.{0, 0} 0 0) List.nil.{0})
  Yulang.GeneralNominalExamples.model
Yulang.GeneralDictionaryOutputMergeSuccess.prepared : Yulang.GeneralNominalRecursiveCandidates.Prepared
  Yulang.GeneralDictionaryOutputMergeSuccess.registry (Yulang.GeneralNominalExamples.context true)
  Yulang.GeneralNominalExamples.displayRoot Yulang.GeneralDictionaryOutputMergeSuccess.declaration
  Yulang.GeneralDictionaryOutputMergeSuccess.checked
Yulang.GeneralDictionaryOutputMergeSuccess.survivor : Yulang.GeneralNominalRecursiveCandidates.Survivor
  Yulang.GeneralDictionaryOutputMergeSuccess.registry (Yulang.GeneralNominalExamples.context true)
  Yulang.GeneralNominalExamples.displayRoot 1 Yulang.GeneralDictionaryOutputMergeSuccess.children
Yulang.GeneralDictionaryOutputMergeSuccess.selected : Yulang.GeneralNominalSupportBoundary.Local
  Yulang.GeneralDictionaryOutputMergeSuccess.registry
  (Yulang.GeneralDictionaryOutputMergeSuccess.start Yulang.GeneralNominalExamples.displayRoot)
  Yulang.GeneralNominalExamples.displayRoot
  (Yulang.CommonRoleOutermostResolver.Frontier.selected.{0} 1 Yulang.GeneralDictionaryOutputMergeSuccess.children)
Yulang.GeneralDictionaryOutputMergeSuccess.children_exact : Eq.{1} Yulang.GeneralDictionaryOutputMergeSuccess.children
  (List.cons.{0} (Yulang.GeneralDictionaryOutputMergeSuccess.child 10)
    (List.cons.{0} (Yulang.GeneralDictionaryOutputMergeSuccess.child 11) List.nil.{0}))
Yulang.GeneralDictionaryOutputMergeSuccess.enabled : Yulang.GeneralNominalFeedbackSteps.Installable
  Yulang.GeneralDictionaryOutputMergeSuccess.registry
  (Yulang.GeneralDictionaryOutputMergeSuccess.start Yulang.GeneralNominalExamples.displayRoot).current
  Yulang.GeneralDictionaryOutputMergeSuccess.packet
Yulang.GeneralDictionaryOutputMergeSuccess.packet_guard : Yulang.GeneralNominalSupportSteps.PacketGuard
  (Yulang.GeneralDictionaryOutputMergeSuccess.start Yulang.GeneralNominalExamples.displayRoot)
  Yulang.GeneralDictionaryOutputMergeSuccess.packet List.nil.{0}
Yulang.GeneralDictionaryOutputMergeSuccess.novel : ¬Yulang.GeneralNominalFeedbackSteps.Committed
    (Yulang.GeneralDictionaryOutputMergeSuccess.start Yulang.GeneralNominalExamples.displayRoot).current
    Yulang.GeneralDictionaryOutputMergeSuccess.packet
Yulang.GeneralDictionaryOutputMergeSuccess.source : Yulang.GeneralNominalSourceFormation.InitialSource
  Yulang.GeneralDictionaryOutputMergeSuccess.registry (Yulang.GeneralNominalExamples.context true)
  Yulang.GeneralNominalExamples.displayRoot
Yulang.GeneralDictionaryOutputMergeSuccess.before_scheduled : Yulang.GeneralDictionaryEarlyMergeChoices.Scheduled
  Yulang.GeneralDictionaryOutputMergeSuccess.registry Yulang.GeneralNominalExamples.displayRoot
  Yulang.GeneralDictionaryOutputMergeSuccess.before
Yulang.GeneralDictionaryOutputMergeSuccess.before_model : Yulang.GeneralNominalSaturationState.Models
  Yulang.GeneralDictionaryOutputMergeSuccess.before.current Yulang.GeneralNominalExamples.model
Yulang.GeneralDictionaryOutputMergeSuccess.site_present : ∀ (n : Nat),
  Eq.{1} n 10 ∨ Eq.{1} n 11 →
    Membership.mem.{0, 0} Yulang.GeneralDictionaryOutputMergeSuccess.before.current.sites
      (Yulang.GeneralDictionaryOutputMergeSuccess.site n)
Yulang.GeneralDictionaryOutputMergeSuccess.inputs_same : Yulang.GeneralNominalFeedbackSites.SameInputs
  Yulang.GeneralDictionaryOutputMergeSuccess.before.current (Yulang.GeneralDictionaryOutputMergeSuccess.site 10)
  (Yulang.GeneralDictionaryOutputMergeSuccess.site 11)
Yulang.GeneralDictionaryOutputMergeSuccess.actual_early_merge : Yulang.GeneralDictionaryEarlyMergeChoices.Scheduled
    Yulang.GeneralDictionaryOutputMergeSuccess.registry Yulang.GeneralNominalExamples.displayRoot
    Yulang.GeneralDictionaryOutputMergeSuccess.finish ∧
  Yulang.GeneralNominalSupportSteps.Step Yulang.GeneralDictionaryOutputMergeSuccess.registry
      Yulang.GeneralNominalExamples.displayRoot Yulang.GeneralDictionaryOutputMergeSuccess.before
      Yulang.GeneralDictionaryOutputMergeSuccess.finish ∧
    Ne.{1} Yulang.GeneralDictionaryOutputMergeSuccess.finish.current.packets List.nil.{0} ∧
      Ne.{1} Yulang.GeneralDictionaryOutputMergeSuccess.finish.current.aliases List.nil.{0}
Yulang.GeneralDictionaryOutputMergeSuccess.finish_model : Yulang.GeneralNominalSaturationState.Models
  Yulang.GeneralDictionaryOutputMergeSuccess.finish.current Yulang.GeneralNominalExamples.model
Yulang.GeneralDictionaryOutputMergeSuccess.actual_path : Yulang.B4Target.Steps.{1}
  (Yulang.GeneralNominalSupportSteps.Step Yulang.GeneralDictionaryOutputMergeSuccess.registry
    Yulang.GeneralNominalExamples.displayRoot)
  (Yulang.GeneralDictionaryOutputMergeSuccess.start Yulang.GeneralNominalExamples.displayRoot)
  Yulang.GeneralDictionaryOutputMergeSuccess.finish
Yulang.GeneralDictionaryOutputMergeSuccess.reachable : Yulang.B4TargetV5.Reachable.{0}
  (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
  Yulang.GeneralDictionaryOutputMergeSuccess.registry Yulang.GeneralNominalExamples.displayRoot
  Yulang.GeneralDictionaryOutputMergeSuccess.finish
Yulang.GeneralDictionaryOutputMergeSuccess.inhabited_early_merge : Yulang.B4TargetV5.Reachable.{0}
    (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
    Yulang.GeneralDictionaryOutputMergeSuccess.registry Yulang.GeneralNominalExamples.displayRoot
    Yulang.GeneralDictionaryOutputMergeSuccess.finish ∧
  Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryOutputMergeSuccess.finish.current
      Yulang.GeneralNominalExamples.model ∧
    Ne.{1} Yulang.GeneralDictionaryOutputMergeSuccess.finish.current.packets List.nil.{0} ∧
      Ne.{1} Yulang.GeneralDictionaryOutputMergeSuccess.finish.current.aliases List.nil.{0} ∧
        Yulang.GeneralDictionarySupportChoices.Coherent Yulang.GeneralDictionaryOutputMergeSuccess.finish.current
Yulang.GeneralDictionaryOutputMergeSuccess.output_atoms_exact : Eq.{1}
  (Yulang.GeneralNominalDemandMerging.outputAtoms (Yulang.GeneralDictionaryOutputMergeSuccess.site 10)
    (Yulang.GeneralDictionaryOutputMergeSuccess.site 11))
  (List.cons.{0}
    (Yulang.PresenceNormalForm.Atom.tyLe
      (Yulang.Core.PresenceGeneration.TyTerm.var (Yulang.GeneralDictionaryOutputMergeSuccess.outputTarget 10))
      (Yulang.Core.PresenceGeneration.TyTerm.var (Yulang.GeneralDictionaryOutputMergeSuccess.outputTarget 11)))
    (List.cons.{0}
      (Yulang.PresenceNormalForm.Atom.tyLe
        (Yulang.Core.PresenceGeneration.TyTerm.var (Yulang.GeneralDictionaryOutputMergeSuccess.outputTarget 11))
        (Yulang.Core.PresenceGeneration.TyTerm.var (Yulang.GeneralDictionaryOutputMergeSuccess.outputTarget 10)))
      List.nil.{0}))
Yulang.GeneralDictionaryOutputMergeSuccess.output_targets_distinct : Ne.{1}
  (Yulang.GeneralDictionaryOutputMergeSuccess.outputTarget 10)
  (Yulang.GeneralDictionaryOutputMergeSuccess.outputTarget 11)
Yulang.GeneralDictionaryOutputMergeSuccess.finish_sourceformed : Yulang.GeneralNominalSupportSteps.SourceFormed
  Yulang.GeneralDictionaryOutputMergeSuccess.registry Yulang.GeneralNominalExamples.displayRoot
  Yulang.GeneralDictionaryOutputMergeSuccess.finish
Yulang.GeneralDictionaryOutputMergeSuccess.reachable_nonempty_output_merge : Yulang.GeneralNominalSupportSteps.SourceFormed
    Yulang.GeneralDictionaryOutputMergeSuccess.registry Yulang.GeneralNominalExamples.displayRoot
    Yulang.GeneralDictionaryOutputMergeSuccess.finish ∧
  Yulang.B4TargetV5.Reachable.{0}
      (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
      Yulang.GeneralDictionaryOutputMergeSuccess.registry Yulang.GeneralNominalExamples.displayRoot
      Yulang.GeneralDictionaryOutputMergeSuccess.finish ∧
    Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryOutputMergeSuccess.finish.current
        Yulang.GeneralNominalExamples.model ∧
      Ne.{1} (Yulang.GeneralDictionaryOutputMergeSuccess.outputTarget 10)
          (Yulang.GeneralDictionaryOutputMergeSuccess.outputTarget 11) ∧
        Ne.{1}
          (Yulang.GeneralNominalDemandMerging.outputAtoms (Yulang.GeneralDictionaryOutputMergeSuccess.site 10)
            (Yulang.GeneralDictionaryOutputMergeSuccess.site 11))
          List.nil.{0}
Yulang.GeneralDictionaryOutputMergeSuccess.terminal_report : Eq.{1}
  (Yulang.GeneralNominalRecursiveCandidates.report (Yulang.GeneralNominalExamples.context true)
    Yulang.GeneralDictionaryOutputMergeSuccess.terminal (List.cons.{0} (Prod.mk.{0, 0} 1 1) List.nil.{0}))
  { captures := List.cons.{0} { name := 0, bounds := Prod.mk.{0, 0} 1 1, origin := none.{0} } List.nil.{0},
    checked := List.cons.{0} (Prod.mk.{0, 0} 1 1) (List.cons.{0} (Prod.mk.{0, 0} 1 1) List.nil.{0}) }
Yulang.GeneralDictionaryOutputMergeSuccess.terminal_schema : ∀ (n : Nat),
  Eq.{1}
    (Yulang.GeneralNominalRecursiveCandidates.generated Yulang.GeneralDictionaryOutputMergeSuccess.registry
      (Yulang.GeneralNominalExamples.context true) (Yulang.GeneralDictionaryOutputMergeSuccess.child n)
      Yulang.GeneralDictionaryOutputMergeSuccess.terminal Yulang.GeneralDictionaryOutputMergeSuccess.terminal_checked
      (List.cons.{0} (Prod.mk.{0, 0} 1 1) List.nil.{0}))
    {
      tests :=
        List.cons.{0}
          (Prod.mk.{0, 0}
            (Yulang.GeneralNominalRecursiveInspection.Origin.source
              (Yulang.GeneralDictionaryOutputMergeSuccess.outputTarget n))
            (Yulang.GeneralNominalRecursiveInspection.Test.scalar Yulang.Inference.Base.int))
          List.nil.{0} }
Yulang.GeneralDictionaryOutputMergeSuccess.terminal_branch : ∀ (n : Nat),
  Yulang.GeneralNominalRecursiveCandidates.BranchModels Yulang.GeneralDictionaryOutputMergeSuccess.registry
    (Yulang.GeneralNominalExamples.context true) (Yulang.GeneralDictionaryOutputMergeSuccess.child n)
    Yulang.GeneralDictionaryOutputMergeSuccess.terminal Yulang.GeneralDictionaryOutputMergeSuccess.terminal_checked
    (List.cons.{0} (Prod.mk.{0, 0} 1 1) List.nil.{0}) Yulang.GeneralNominalExamples.model
Yulang.GeneralDictionaryOutputMergeSuccess.terminal_instance : ∀ (n : Nat),
  Yulang.GeneralDictionaryRecursiveEvidence.Instance Yulang.GeneralDictionaryOutputMergeSuccess.registry
    (Yulang.GeneralNominalExamples.context true) Yulang.GeneralNominalExamples.model
    (Yulang.GeneralDictionaryOutputMergeSuccess.child n) 7 List.nil.{0}
Yulang.GeneralDictionaryOutputMergeSuccess.final_extension : Yulang.GeneralDictionaryOrdinaryTrace.Extension
  (Yulang.GeneralNominalExamples.context true) Yulang.GeneralDictionaryOutputMergeSuccess.finish.current.context
Yulang.GeneralDictionaryOutputMergeSuccess.current_terminal_instance : ∀ (n : Nat),
  Yulang.GeneralDictionaryRecursiveEvidence.Instance Yulang.GeneralDictionaryOutputMergeSuccess.registry
    Yulang.GeneralDictionaryOutputMergeSuccess.finish.current.context Yulang.GeneralNominalExamples.model
    (Yulang.GeneralDictionaryOutputMergeSuccess.child n) 7 List.nil.{0}
Yulang.GeneralDictionaryOutputMergeSuccess.output_reserved : ∀ (n : Nat),
  Eq.{1} n 10 ∨ Eq.{1} n 11 →
    Membership.mem.{0, 0}
      (Yulang.GeneralNominalAllocation.reserved (Yulang.GeneralNominalExamples.state true)
        Yulang.GeneralDictionaryOutputMergeSuccess.registry Yulang.GeneralNominalExamples.displayRoot.identity)
      (Yulang.GeneralDictionaryOutputMergeSuccess.outputTarget n)
Yulang.GeneralDictionaryOutputMergeSuccess.sources_shape : ∀ (identity : Nat),
  Membership.mem.{0, 0} (Yulang.GeneralNominalState.sources Yulang.GeneralDictionaryOutputMergeSuccess.current.state)
      identity →
    Eq.{1} identity 0 ∨
      Eq.{1} identity 1 ∨
        Membership.mem.{0, 0}
          (Yulang.GeneralNominalAllocation.reserved (Yulang.GeneralNominalExamples.state true)
            Yulang.GeneralDictionaryOutputMergeSuccess.registry Yulang.GeneralNominalExamples.displayRoot.identity)
          identity
Yulang.GeneralDictionaryOutputMergeSuccess.current_fresh : ∀ (identity : Nat),
  Yulang.GeneralNominalAllocation.Fresh Yulang.GeneralDictionaryOutputMergeSuccess.current.state
    Yulang.GeneralDictionaryOutputMergeSuccess.registry identity
Yulang.GeneralDictionaryOutputMergeSuccess.child_linked : ∀ (n : Nat),
  Eq.{1} n 10 ∨ Eq.{1} n 11 →
    Yulang.GeneralNominalState.Linked Yulang.GeneralDictionaryOutputMergeSuccess.current.state
      (Yulang.GeneralDictionaryOutputMergeSuccess.child n).demand
Yulang.GeneralDictionaryOutputMergeSuccess.child_branch_at : ∀ (n : Nat),
  Eq.{1} n 10 ∨ Eq.{1} n 11 →
    Yulang.GeneralNominalJointCandidates.BranchAt Yulang.GeneralDictionaryOutputMergeSuccess.registry
      Yulang.GeneralDictionaryOutputMergeSuccess.finish.current (Yulang.GeneralDictionaryOutputMergeSuccess.child n) 7
      Yulang.GeneralNominalExamples.model
@Yulang.GeneralDictionaryOutputMergeSuccess.old_alias_eq : ∀ {a b : Nat},
  Yulang.GeneralNominalSaturationState.Alias Yulang.GeneralDictionaryOutputMergeSuccess.before.current a b → Eq.{1} a b
Yulang.GeneralDictionaryOutputMergeSuccess.first_not_parent : Ne.{1}
  (Yulang.GeneralDictionaryOutputMergeSuccess.child 10).identity Yulang.GeneralNominalExamples.displayRoot.identity
Yulang.GeneralDictionaryOutputMergeSuccess.last_not_parent : Ne.{1}
  (Yulang.GeneralDictionaryOutputMergeSuccess.child 11).identity Yulang.GeneralNominalExamples.displayRoot.identity
Yulang.GeneralDictionaryOutputMergeSuccess.sites_exact : Eq.{1}
  Yulang.GeneralDictionaryOutputMergeSuccess.finish.current.sites
  (List.cons.{0} (Yulang.GeneralNominalDemandMerging.pointSite Yulang.GeneralNominalExamples.displayRoot)
    (List.cons.{0} (Yulang.GeneralDictionaryOutputMergeSuccess.site 10)
      (List.cons.{0} (Yulang.GeneralDictionaryOutputMergeSuccess.site 11) List.nil.{0})))
Yulang.GeneralDictionaryOutputMergeSuccess.merged_alias_identity : ∀ (identity : Nat),
  Yulang.GeneralNominalSaturationState.Alias Yulang.GeneralDictionaryOutputMergeSuccess.finish.current
      (Yulang.GeneralDictionaryOutputMergeSuccess.child 10).identity identity →
    Eq.{1} (Yulang.GeneralDictionaryOutputMergeSuccess.child 10).identity identity ∨
      Eq.{1} (Yulang.GeneralDictionaryOutputMergeSuccess.child 11).identity identity
Yulang.GeneralDictionaryOutputMergeSuccess.merged_child_joint : Yulang.GeneralNominalJointCandidates.Joint
  Yulang.GeneralDictionaryOutputMergeSuccess.registry Yulang.GeneralDictionaryOutputMergeSuccess.finish.current
  (Yulang.GeneralDictionaryOutputMergeSuccess.child 10) 7
Yulang.GeneralDictionaryOutputMergeSuccess.merged_child_evidence : ∀ (n : Nat),
  Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralDictionaryOutputMergeSuccess.registry
    Yulang.GeneralDictionaryOutputMergeSuccess.current Yulang.GeneralNominalExamples.model
    (Yulang.GeneralDictionaryOutputMergeSuccess.child n)
    (Yulang.CommonRoleOutermostResolver.Dictionary.node 7 List.nil.{0})
Yulang.GeneralDictionaryOutputMergeSuccess.reachable_joint_evidence : Yulang.GeneralNominalSupportSteps.SourceFormed
    Yulang.GeneralDictionaryOutputMergeSuccess.registry Yulang.GeneralNominalExamples.displayRoot
    Yulang.GeneralDictionaryOutputMergeSuccess.finish ∧
  Yulang.B4TargetV5.Reachable.{0}
      (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
      Yulang.GeneralDictionaryOutputMergeSuccess.registry Yulang.GeneralNominalExamples.displayRoot
      Yulang.GeneralDictionaryOutputMergeSuccess.finish ∧
    Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryOutputMergeSuccess.finish.current
        Yulang.GeneralNominalExamples.model ∧
      Yulang.GeneralNominalJointCandidates.Joint Yulang.GeneralDictionaryOutputMergeSuccess.registry
          Yulang.GeneralDictionaryOutputMergeSuccess.finish.current
          (Yulang.GeneralDictionaryOutputMergeSuccess.child 10) 7 ∧
        Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralDictionaryOutputMergeSuccess.registry
            Yulang.GeneralDictionaryOutputMergeSuccess.current Yulang.GeneralNominalExamples.model
            (Yulang.GeneralDictionaryOutputMergeSuccess.child 10)
            (Yulang.CommonRoleOutermostResolver.Dictionary.node 7 List.nil.{0}) ∧
          Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralDictionaryOutputMergeSuccess.registry
              Yulang.GeneralDictionaryOutputMergeSuccess.current Yulang.GeneralNominalExamples.model
              (Yulang.GeneralDictionaryOutputMergeSuccess.child 11)
              (Yulang.CommonRoleOutermostResolver.Dictionary.node 7 List.nil.{0}) ∧
            Ne.{1} (Yulang.GeneralDictionaryOutputMergeSuccess.outputTarget 10)
                (Yulang.GeneralDictionaryOutputMergeSuccess.outputTarget 11) ∧
              Ne.{1}
                (Yulang.GeneralNominalDemandMerging.outputAtoms (Yulang.GeneralDictionaryOutputMergeSuccess.site 10)
                  (Yulang.GeneralDictionaryOutputMergeSuccess.site 11))
                List.nil.{0}
@Yulang.GeneralDictionaryScalarJournalMerge.outputs_from_packets : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalSaturationState.State roles)
  (first last : Yulang.GeneralNominalDemandMerging.Site roles)
  (leftPacket rightPacket : Yulang.GeneralNominalSaturationState.Packet roles),
  Membership.mem.{0, 0} state.packets leftPacket →
    Membership.mem.{0, 0} state.packets rightPacket →
      ∀ (scalars : Nat → Yulang.Inference.Base),
        Yulang.GeneralDictionaryScalarJournalMerge.Requests leftPacket first scalars →
          Yulang.GeneralDictionaryScalarJournalMerge.Requests rightPacket last scalars →
            ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
              Yulang.GeneralNominalSaturationState.Models state model →
                Yulang.PresenceNormalForm.All.{0, 0} Yulang.CommonNominalFullCarrier.model model
                  (Yulang.GeneralNominalDemandMerging.outputAtoms first last)
@Yulang.GeneralDictionaryScalarJournalMerge.models_merge_iff : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalSaturationState.State roles)
  (first last : Yulang.GeneralNominalDemandMerging.Site roles)
  (leftPacket rightPacket : Yulang.GeneralNominalSaturationState.Packet roles),
  Membership.mem.{0, 0} state.packets leftPacket →
    Membership.mem.{0, 0} state.packets rightPacket →
      ∀ (scalars : Nat → Yulang.Inference.Base),
        Yulang.GeneralDictionaryScalarJournalMerge.Requests leftPacket first scalars →
          Yulang.GeneralDictionaryScalarJournalMerge.Requests rightPacket last scalars →
            ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
              Yulang.GeneralNominalSaturationState.Models (Yulang.GeneralNominalSaturationState.merge state first last)
                  model ↔
                Yulang.GeneralNominalSaturationState.Models state model
@Yulang.GeneralDictionaryScalarJournalMerge.evidence_merge_iff : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSaturationState.State roles)
  (first last : Yulang.GeneralNominalDemandMerging.Site roles)
  (leftPacket rightPacket : Yulang.GeneralNominalSaturationState.Packet roles),
  Membership.mem.{0, 0} state.packets leftPacket →
    Membership.mem.{0, 0} state.packets rightPacket →
      ∀ (scalars : Nat → Yulang.Inference.Base),
        Yulang.GeneralDictionaryScalarJournalMerge.Requests leftPacket first scalars →
          Yulang.GeneralDictionaryScalarJournalMerge.Requests rightPacket last scalars →
            ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
              Yulang.GeneralNominalSaturationState.Models state model →
                ∀ (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
                  (payload : Yulang.GeneralDictionaryReadback.Payload),
                  Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry
                      (Yulang.GeneralNominalSaturationState.merge state first last).context model root payload ↔
                    Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry state.context model root payload
@Yulang.GeneralDictionaryScalarMerge.output_atoms_of_scalar_tests : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSaturationState.State roles)
  (first last : Yulang.GeneralNominalDemandMerging.Site roles)
  (leftDecl rightDecl : Yulang.GeneralDeclarations.Declaration)
  (leftChecked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles leftDecl)
  (rightChecked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles rightDecl)
  (leftBounds rightBounds : List.{0} (Yulang.GeneralNominalInspection.Bounds state.context.state))
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalRecursiveCandidates.BranchModels registry state.context first.occurrence leftDecl leftChecked
      leftBounds model →
    Yulang.GeneralNominalRecursiveCandidates.BranchModels registry state.context last.occurrence rightDecl rightChecked
        rightBounds model →
      ∀ (scalars : Nat → Yulang.Inference.Base),
        (∀ (output : Yulang.GeneralSourceState.Output),
            Membership.mem.{0, 0} first.occurrence.demand.outputs output →
              Membership.mem.{0, 0}
                (Yulang.GeneralNominalRecursiveCandidates.generated registry state.context first.occurrence leftDecl
                    leftChecked leftBounds).tests
                (Prod.mk.{0, 0} (Yulang.GeneralNominalRecursiveInspection.Origin.source output.target)
                  (Yulang.GeneralNominalRecursiveInspection.Test.scalar (scalars output.name)))) →
          (∀ (output : Yulang.GeneralSourceState.Output),
              Membership.mem.{0, 0} last.occurrence.demand.outputs output →
                Membership.mem.{0, 0}
                  (Yulang.GeneralNominalRecursiveCandidates.generated registry state.context last.occurrence rightDecl
                      rightChecked rightBounds).tests
                  (Prod.mk.{0, 0} (Yulang.GeneralNominalRecursiveInspection.Origin.source output.target)
                    (Yulang.GeneralNominalRecursiveInspection.Test.scalar (scalars output.name)))) →
            Yulang.PresenceNormalForm.All.{0, 0} Yulang.CommonNominalFullCarrier.model model
              (Yulang.GeneralNominalDemandMerging.outputAtoms first last)
@Yulang.GeneralDictionaryScalarMerge.evidence_merge_of_scalar_tests : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSaturationState.State roles)
  (first last : Yulang.GeneralNominalDemandMerging.Site roles)
  (leftDecl rightDecl : Yulang.GeneralDeclarations.Declaration)
  (leftChecked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles leftDecl)
  (rightChecked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles rightDecl)
  (leftBounds rightBounds : List.{0} (Yulang.GeneralNominalInspection.Bounds state.context.state))
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalRecursiveCandidates.BranchModels registry state.context first.occurrence leftDecl leftChecked
      leftBounds model →
    Yulang.GeneralNominalRecursiveCandidates.BranchModels registry state.context last.occurrence rightDecl rightChecked
        rightBounds model →
      ∀ (scalars : Nat → Yulang.Inference.Base),
        (∀ (output : Yulang.GeneralSourceState.Output),
            Membership.mem.{0, 0} first.occurrence.demand.outputs output →
              Membership.mem.{0, 0}
                (Yulang.GeneralNominalRecursiveCandidates.generated registry state.context first.occurrence leftDecl
                    leftChecked leftBounds).tests
                (Prod.mk.{0, 0} (Yulang.GeneralNominalRecursiveInspection.Origin.source output.target)
                  (Yulang.GeneralNominalRecursiveInspection.Test.scalar (scalars output.name)))) →
          (∀ (output : Yulang.GeneralSourceState.Output),
              Membership.mem.{0, 0} last.occurrence.demand.outputs output →
                Membership.mem.{0, 0}
                  (Yulang.GeneralNominalRecursiveCandidates.generated registry state.context last.occurrence rightDecl
                      rightChecked rightBounds).tests
                  (Prod.mk.{0, 0} (Yulang.GeneralNominalRecursiveInspection.Origin.source output.target)
                    (Yulang.GeneralNominalRecursiveInspection.Test.scalar (scalars output.name)))) →
            ∀ (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
              (payload : Yulang.GeneralDictionaryReadback.Payload),
              Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry state.context model root payload →
                Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry
                  (Yulang.GeneralNominalSaturationState.merge state first last).context model root payload
Yulang.GeneralDictionaryScalarMergeExample.generated_output_equations : Yulang.PresenceNormalForm.All.{0, 0}
  Yulang.CommonNominalFullCarrier.model Yulang.GeneralDictionaryJointMergeExample.model
  (Yulang.GeneralNominalDemandMerging.outputAtoms Yulang.GeneralDictionaryJointMergeExample.first
    Yulang.GeneralDictionaryJointMergeExample.last)
Yulang.GeneralDictionaryScalarMergeExample.complete_evidence_from_requests : Yulang.GeneralDictionaryRecursiveEvidence.Evidence
    Yulang.GeneralDictionaryJointMergeExample.registry
    (Yulang.GeneralNominalSaturationState.merge Yulang.GeneralDictionaryJointMergeExample.before
        Yulang.GeneralDictionaryJointMergeExample.first Yulang.GeneralDictionaryJointMergeExample.last).context
    Yulang.GeneralDictionaryJointMergeExample.model Yulang.GeneralDictionaryJointMergeExample.first.occurrence
    (Yulang.CommonRoleOutermostResolver.Dictionary.node 7 List.nil.{0}) ∧
  Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralDictionaryJointMergeExample.registry
    (Yulang.GeneralNominalSaturationState.merge Yulang.GeneralDictionaryJointMergeExample.before
        Yulang.GeneralDictionaryJointMergeExample.first Yulang.GeneralDictionaryJointMergeExample.last).context
    Yulang.GeneralDictionaryJointMergeExample.model Yulang.GeneralDictionaryJointMergeExample.last.occurrence
    (Yulang.CommonRoleOutermostResolver.Dictionary.node 7 List.nil.{0})

```
