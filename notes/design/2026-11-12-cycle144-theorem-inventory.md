# Cycle144 公開定理索引

18 modules・126 public theorems。本文報告のA〜Eに日本語の主張と適用範囲を記した。private補助は数えない。末尾の型は`lake env lean --trust=0`で全公開宣言に`#check @名前`を適用した出力そのもので、暗黙の量化子も展開する。

## Yulang.GeneralDictionaryEarlyMergeNoEvidence

`child_no_instance`, `child_no_evidence`, `root_no_evidence`, `inhabited_no_evidence`

## Yulang.GeneralDictionaryEarlyMergeClosure

`models_of_source`, `varying_model`, `refresh_large_unknown`, `context_complete`, `point_closed`, `sites_exact`, `edges_exact`, `generated_cases`, `sameInputs_no_cross`, `merges_closed`, `installs_committed`, `feedback_stable`, `stable`, `stable_diagnostic_without_classify`

## Yulang.GeneralDictionaryDiagnosticTotality

`diagnostic_exists`, `diagnostic_iff_accessible`, `closure_local`, `diagnostic_iff`

## Yulang.GeneralDictionaryDiagnosticAccessibility

`resolved_accessible`, `resolved_children_accessible`, `actual_accessible_without_classify`

## Yulang.GeneralDictionaryEarlyMergeDiagnostics

`parent_instance`, `acyclic`, `parent_selected`, `child_rejected`, `supported_parent`, `supported_child`, `diagnostic`, `child_no_dictionary`, `root_no_classify`, `reachable_diagnostic`

## Yulang.GeneralDictionarySupportLocalOrder

`inspection`, `decision_guard_forward`, `decision_guard`, `support_pending`, `local_forward`, `local_iff`, `boundary_local`, `resolves`, `child`, `whereAccessible_iff`, `classify`

## Yulang.GeneralDictionarySupportRecursiveTrace

`initial_packet_unique`, `initial_no_administrative`, `first_step_unique`, `finish_no_step`, `trace_endpoints`, `initial_not_stable`, `stable_endpoint_iff`

## Yulang.GeneralDictionaryEarlyMergeExample

`checked`, `registry_checked`, `all_source_decisions`, `query`, `schema`, `branch`, `prepared`, `survivor`, `selected`, `children_exact`, `enabled`, `packet_guard`, `novel`, `source`, `before_scheduled`, `before_model`, `site_present`, `inputs_same`, `actual_early_merge`, `finish_model`, `actual_path`, `reachable`, `inhabited_early_merge`

## Yulang.GeneralDictionarySupportReadbackRegression

`accessible`, `generated_selected`, `extracted`, `extracted_exact`

## Yulang.GeneralDictionarySupportRecursiveJoint

`parent_branch_at`, `leaf_branch_at`, `parent_joint`, `leaf_joint`, `generated_selected_joint`

## Yulang.GeneralDictionarySupportRecursiveClosure

`varying_source`, `varying_model`, `refresh_large_unknown`, `context_complete`, `point_closed`, `sites_exact`, `edges_exact`, `generated_cases`, `sameInputs_no_cross`, `merges_closed`, `installs_committed`, `feedback_stable`, `stable`, `resolves`, `completed`

## Yulang.GeneralDictionaryLocalReadbackExact

`classified_accessible`, `children_accessible`, `closure_selected`, `success_iff`

## Yulang.GeneralDictionarySupportRecursiveClassification

`models_of_source`, `current_model`, `acyclic`, `parent_selected`, `leaf_selected`, `supported_parent_selected`, `supported_leaf_selected`, `classified`, `reachable_classified_dictionary`

## Yulang.GeneralDictionaryEarlyMergeBoundary

`packetFree_no_merge`, `initial_install_merge`

## Yulang.GeneralDictionaryLocalReadback

`classified_exists`, `support_dictionary`

## Yulang.GeneralDictionarySupportReadback

`classified_exists`, `uniform_dictionary`, `premises_inhabited`

## Yulang.GeneralDictionaryEarlyMergeChoices

`merge_coherent`, `scheduled_formed`, `scheduled_coherent`, `recorded_choices`

## Yulang.GeneralDictionaryEarlyMergeRegression

`scheduled`, `coherent_not_current`

## Leanが検証した量化子・前提付き型

```text
@Yulang.GeneralDictionarySupportReadback.classified_exists : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSupport.Tracked roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
  Yulang.B4TargetV5.Reachable (Yulang.GeneralNominalSupportBoundary.boundary roles) registry root state →
    Yulang.GeneralNominalSupportSteps.Stable registry state root →
      (∀ (focus : Yulang.GeneralSourceDictionaries.Occurrence roles),
          Yulang.GeneralNominalSaturationState.Generated state.current root focus →
            ∃ key children,
              Yulang.GeneralNominalSupportBoundary.Local registry state focus
                (Yulang.CommonRoleOutermostResolver.Frontier.selected key children)) →
        (∀ (focus : Yulang.GeneralSourceDictionaries.Occurrence roles),
            Yulang.GeneralNominalSaturationState.Generated state.current root focus →
              ∀ (key : Nat) (children : List (Yulang.GeneralNominalSupportBoundary.vocabulary roles).Demand),
                Yulang.GeneralNominalSupportBoundary.Local registry state focus
                    (Yulang.CommonRoleOutermostResolver.Frontier.selected key children) →
                  Yulang.GeneralNominalJointCandidates.Joint registry state.current focus key) →
          Acc
              (Yulang.CommonRoleOutermostResolver.Child
                (Yulang.B4TargetV3.Local (Yulang.GeneralNominalSupportBoundary.boundary roles).toSourceBoundary registry
                  state))
              root →
            ∃ dictionary,
              Yulang.B4TargetV3.Classify (Yulang.GeneralNominalSupportBoundary.boundary roles).toSourceBoundary registry
                state root (Yulang.CommonRoleOutermostResolver.Result.selected dictionary)
@Yulang.GeneralDictionarySupportReadback.uniform_dictionary : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSupport.Tracked roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
  Yulang.B4TargetV5.Reachable (Yulang.GeneralNominalSupportBoundary.boundary roles) registry root state →
    Yulang.GeneralNominalSupportSteps.Stable registry state root →
      (∀ (focus : Yulang.GeneralSourceDictionaries.Occurrence roles),
          Yulang.GeneralNominalSaturationState.Generated state.current root focus →
            ∃ key children,
              Yulang.GeneralNominalSupportBoundary.Local registry state focus
                (Yulang.CommonRoleOutermostResolver.Frontier.selected key children)) →
        (∀ (focus : Yulang.GeneralSourceDictionaries.Occurrence roles),
            Yulang.GeneralNominalSaturationState.Generated state.current root focus →
              ∀ (key : Nat) (children : List (Yulang.GeneralNominalSupportBoundary.vocabulary roles).Demand),
                Yulang.GeneralNominalSupportBoundary.Local registry state focus
                    (Yulang.CommonRoleOutermostResolver.Frontier.selected key children) →
                  Yulang.GeneralNominalJointCandidates.Joint registry state.current focus key) →
          Acc
              (Yulang.CommonRoleOutermostResolver.Child
                (Yulang.B4TargetV3.Local (Yulang.GeneralNominalSupportBoundary.boundary roles).toSourceBoundary registry
                  state))
              root →
            ∃ dictionary,
              Yulang.B4TargetV3.Classify (Yulang.GeneralNominalSupportBoundary.boundary roles).toSourceBoundary registry
                  state root (Yulang.CommonRoleOutermostResolver.Result.selected dictionary) ∧
                ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                  Yulang.GeneralNominalSaturationState.Models state.current model →
                    Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context model root
                      dictionary
@Yulang.GeneralDictionarySupportReadback.premises_inhabited : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSupport.Tracked roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
  (∀ (focus : Yulang.GeneralSourceDictionaries.Occurrence roles),
      Yulang.GeneralNominalSaturationState.Generated state.current root focus →
        ∃ key children,
          Yulang.GeneralNominalSupportBoundary.Local registry state focus
            (Yulang.CommonRoleOutermostResolver.Frontier.selected key children)) →
    (∀ (focus : Yulang.GeneralSourceDictionaries.Occurrence roles),
        Yulang.GeneralNominalSaturationState.Generated state.current root focus →
          ∀ (key : Nat) (children : List (Yulang.GeneralNominalSupportBoundary.vocabulary roles).Demand),
            Yulang.GeneralNominalSupportBoundary.Local registry state focus
                (Yulang.CommonRoleOutermostResolver.Frontier.selected key children) →
              Yulang.GeneralNominalJointCandidates.Joint registry state.current focus key) →
      ∃ model, Yulang.GeneralNominalSaturationState.Models state.current model
@Yulang.GeneralDictionaryEarlyMergeChoices.merge_coherent : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalSaturationState.State roles)
  (first last : Yulang.GeneralNominalDemandMerging.Site roles),
  Yulang.GeneralDictionarySupportChoices.Coherent state →
    Yulang.GeneralDictionaryEarlyMergeChoices.Early state first last →
      Yulang.GeneralDictionarySupportChoices.Coherent (Yulang.GeneralNominalSaturationState.merge state first last)
@Yulang.GeneralDictionaryEarlyMergeChoices.scheduled_formed : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (state : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.GeneralDictionaryEarlyMergeChoices.Scheduled registry root state →
    Yulang.GeneralNominalSupportSteps.SourceFormed registry root state
@Yulang.GeneralDictionaryEarlyMergeChoices.scheduled_coherent : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (state : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.GeneralDictionaryEarlyMergeChoices.Scheduled registry root state →
    Yulang.GeneralDictionarySupportChoices.Coherent state.current
@Yulang.GeneralDictionaryEarlyMergeChoices.recorded_choices : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root focus : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (state : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.GeneralDictionaryEarlyMergeChoices.Scheduled registry root state →
    ∀ (packet : Yulang.GeneralNominalSaturationState.Packet roles),
      packet ∈ state.current.packets →
        packet.site.occurrence.identity = focus.identity →
          ∀ (prior : Yulang.GeneralNominalSaturationState.Packet roles),
            prior ∈ state.current.packets →
              Yulang.GeneralNominalSaturationState.Alias state.current focus.identity prior.site.occurrence.identity →
                prior.declaration.id = packet.declaration.id
Yulang.GeneralDictionaryEarlyMergeRegression.scheduled : Yulang.GeneralDictionaryEarlyMergeChoices.Scheduled
  Yulang.GeneralNominalFeedbackObstruction.registry Yulang.GeneralNominalFeedbackObstruction.root
  Yulang.GeneralDictionarySupportRevisionObstruction.finish
Yulang.GeneralDictionaryEarlyMergeRegression.coherent_not_current : Yulang.GeneralDictionarySupportChoices.Coherent
    Yulang.GeneralDictionarySupportRevisionObstruction.finish.current ∧
  Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionarySupportRevisionObstruction.finish.current
      Yulang.GeneralNominalFeedbackObstruction.model ∧
    Yulang.GeneralDictionarySupportRevisionObstruction.finish.current.packets ≠ [] ∧
      ¬Yulang.GeneralDictionaryCurrentJournal.Current Yulang.GeneralNominalFeedbackObstruction.registry
          Yulang.GeneralDictionarySupportRevisionObstruction.finish.current
@Yulang.GeneralDictionaryLocalReadback.classified_exists : ∀ {v : Yulang.B4Target.Vocabulary}
  (b : Yulang.B4Target.SourceBoundary v) (registry : v.Registry) (state : v.State) (root : v.Demand),
  (∀ (focus : v.Demand),
      Yulang.GeneralDictionaryLocalReadback.Reach (Yulang.B4TargetV3.Local b registry state) root focus →
        ∃ key children,
          Yulang.B4TargetV3.Local b registry state focus
            (Yulang.CommonRoleOutermostResolver.Frontier.selected key children)) →
    Acc (Yulang.CommonRoleOutermostResolver.Child (Yulang.B4TargetV3.Local b registry state)) root →
      ∃ dictionary,
        Yulang.B4TargetV3.Classify b registry state root (Yulang.CommonRoleOutermostResolver.Result.selected dictionary)
@Yulang.GeneralDictionaryLocalReadback.support_dictionary : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSupport.Tracked roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
  Yulang.B4TargetV5.Reachable (Yulang.GeneralNominalSupportBoundary.boundary roles) registry root state →
    Yulang.GeneralNominalSupportSteps.Stable registry state root →
      (∀ (focus : (Yulang.GeneralNominalSupportBoundary.vocabulary roles).Demand),
          Yulang.GeneralDictionaryLocalReadback.Reach
              (Yulang.B4TargetV3.Local (Yulang.GeneralNominalSupportBoundary.boundary roles).toSourceBoundary registry
                state)
              root focus →
            ∃ key children,
              Yulang.GeneralNominalSupportBoundary.Local registry state focus
                (Yulang.CommonRoleOutermostResolver.Frontier.selected key children)) →
        ((∃ model, Yulang.GeneralNominalSaturationState.Models state.current model) →
            ∀ (focus : Yulang.GeneralSourceDictionaries.Occurrence roles),
              Yulang.GeneralNominalSaturationState.Generated state.current root focus →
                ∀ (key : Nat) (children : List (Yulang.GeneralNominalSupportBoundary.vocabulary roles).Demand),
                  Yulang.GeneralNominalSupportBoundary.Local registry state focus
                      (Yulang.CommonRoleOutermostResolver.Frontier.selected key children) →
                    Yulang.GeneralNominalJointCandidates.Joint registry state.current focus key) →
          Acc
              (Yulang.CommonRoleOutermostResolver.Child
                (Yulang.B4TargetV3.Local (Yulang.GeneralNominalSupportBoundary.boundary roles).toSourceBoundary registry
                  state))
              root →
            ∃ dictionary,
              Yulang.B4TargetV3.Classify (Yulang.GeneralNominalSupportBoundary.boundary roles).toSourceBoundary registry
                  state root (Yulang.CommonRoleOutermostResolver.Result.selected dictionary) ∧
                ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                  Yulang.GeneralNominalSaturationState.Models state.current model →
                    Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context model root
                      dictionary
@Yulang.GeneralDictionaryEarlyMergeBoundary.packetFree_no_merge : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (state : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.B4TargetV5.Reachable (Yulang.GeneralNominalSupportBoundary.boundary roles) registry root state →
    state.current.packets = [] →
      ∀ (first last : Yulang.GeneralNominalDemandMerging.Site roles),
        first ∈ state.current.sites →
          last ∈ state.current.sites →
            Yulang.GeneralNominalSaturationState.Alias state.current first.occurrence.identity last.occurrence.identity
@Yulang.GeneralDictionaryEarlyMergeBoundary.initial_install_merge : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (context : Yulang.GeneralNominalCandidates.Context),
  Yulang.GeneralNominalSourceFormation.InitialSource registry context root →
    ∀ (packet : Yulang.GeneralNominalSaturationState.Packet roles)
      (support : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
      packet.site.occurrence = root →
        Yulang.GeneralNominalFeedbackSteps.Installable registry
            (Yulang.GeneralNominalSupport.initial context root).current packet →
          ¬Yulang.GeneralNominalFeedbackSteps.Committed (Yulang.GeneralNominalSupport.initial context root).current
                packet →
            Yulang.GeneralNominalSupportSteps.PacketGuard (Yulang.GeneralNominalSupport.initial context root) packet
                support →
              ∀ (child : Yulang.GeneralSourceDictionaries.Occurrence roles),
                child ∈ packet.children →
                  child.identity ≠ root.identity →
                    ∀ (last : Yulang.GeneralNominalDemandMerging.Site roles),
                      last ∈
                          (Yulang.GeneralNominalSupportSteps.install (Yulang.GeneralNominalSupport.initial context root)
                                packet support).current.sites →
                        child.identity ≠ last.occurrence.identity →
                          Yulang.GeneralNominalFeedbackSites.SameInputs
                              (Yulang.GeneralNominalSupportSteps.install
                                  (Yulang.GeneralNominalSupport.initial context root) packet support).current
                              (Yulang.GeneralNominalFeedbackSites.childSite packet child) last →
                            have before :=
                              Yulang.GeneralNominalSupportSteps.install
                                (Yulang.GeneralNominalSupport.initial context root) packet support;
                            have first := Yulang.GeneralNominalFeedbackSites.childSite packet child;
                            have after :=
                              Yulang.GeneralNominalSupportSteps.merge before first last
                                (Yulang.GeneralNominalSupportChoices.dependencyPool before);
                            Yulang.GeneralDictionaryEarlyMergeChoices.Scheduled registry root after ∧
                              Yulang.GeneralNominalSupportSteps.Step registry root before after ∧
                                after.current.packets ≠ [] ∧ after.current.aliases ≠ []
Yulang.GeneralDictionarySupportRecursiveClassification.current_model : Yulang.GeneralNominalSaturationState.Models
  Yulang.GeneralDictionarySupportRecursiveExample.finish.current Yulang.GeneralNominalExamples.model
Yulang.GeneralDictionarySupportRecursiveClassification.acyclic : ∀ (source : Nat),
  ¬Yulang.GeneralNominalFeedbackK2.Cycle Yulang.GeneralDictionarySupportRecursiveExample.finish.current source
Yulang.GeneralDictionarySupportRecursiveClassification.parent_selected : Yulang.GeneralNominalFeedbackK2.Local
  Yulang.GeneralNominalExamples.registry Yulang.GeneralDictionarySupportRecursiveExample.finish.current
  Yulang.GeneralNominalExamples.displayRoot
  (Yulang.CommonRoleOutermostResolver.Frontier.selected 1 [Yulang.GeneralNominalExamples.displayChild])
Yulang.GeneralDictionarySupportRecursiveClassification.leaf_selected : Yulang.GeneralNominalFeedbackK2.Local
  Yulang.GeneralNominalExamples.registry Yulang.GeneralDictionarySupportRecursiveExample.finish.current
  Yulang.GeneralNominalExamples.displayChild (Yulang.CommonRoleOutermostResolver.Frontier.selected 3 [])
Yulang.GeneralDictionarySupportRecursiveClassification.supported_parent_selected : Yulang.GeneralNominalSupportBoundary.Local
  Yulang.GeneralNominalExamples.registry Yulang.GeneralDictionarySupportRecursiveExample.finish
  Yulang.GeneralNominalExamples.displayRoot
  (Yulang.CommonRoleOutermostResolver.Frontier.selected 1 [Yulang.GeneralNominalExamples.displayChild])
Yulang.GeneralDictionarySupportRecursiveClassification.supported_leaf_selected : Yulang.GeneralNominalSupportBoundary.Local
  Yulang.GeneralNominalExamples.registry Yulang.GeneralDictionarySupportRecursiveExample.finish
  Yulang.GeneralNominalExamples.displayChild (Yulang.CommonRoleOutermostResolver.Frontier.selected 3 [])
Yulang.GeneralDictionarySupportRecursiveClassification.classified : Yulang.B4TargetV3.Classify
  (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles).toSourceBoundary
  Yulang.GeneralNominalExamples.registry Yulang.GeneralDictionarySupportRecursiveExample.finish
  Yulang.GeneralNominalExamples.displayRoot
  (Yulang.CommonRoleOutermostResolver.Result.selected
    (Yulang.CommonRoleOutermostResolver.Dictionary.node 1 [Yulang.CommonRoleOutermostResolver.Dictionary.node 3 []]))
Yulang.GeneralDictionarySupportRecursiveClassification.reachable_classified_dictionary : Yulang.B4TargetV5.Reachable
    (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
    Yulang.GeneralNominalExamples.registry Yulang.GeneralNominalExamples.displayRoot
    Yulang.GeneralDictionarySupportRecursiveExample.finish ∧
  Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionarySupportRecursiveExample.finish.current
      Yulang.GeneralNominalExamples.model ∧
    Yulang.B4TargetV3.Classify
        (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles).toSourceBoundary
        Yulang.GeneralNominalExamples.registry Yulang.GeneralDictionarySupportRecursiveExample.finish
        Yulang.GeneralNominalExamples.displayRoot
        (Yulang.CommonRoleOutermostResolver.Result.selected
          (Yulang.CommonRoleOutermostResolver.Dictionary.node 1
            [Yulang.CommonRoleOutermostResolver.Dictionary.node 3 []])) ∧
      ∀ (m : Yulang.GeneralNominalCommonBridge.Assignment),
        Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionarySupportRecursiveExample.finish.current m →
          Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralNominalExamples.registry
            Yulang.GeneralDictionarySupportRecursiveClassification.current m Yulang.GeneralNominalExamples.displayRoot
            (Yulang.CommonRoleOutermostResolver.Dictionary.node 1
              [Yulang.CommonRoleOutermostResolver.Dictionary.node 3 []])
@Yulang.GeneralDictionaryLocalReadbackExact.classified_accessible : ∀ {v : Yulang.B4Target.Vocabulary}
  (b : Yulang.B4Target.SourceBoundary v) (registry : v.Registry) (state : v.State) (root : v.Demand)
  (dictionary : Yulang.CommonRoleOutermostResolver.Dictionary),
  Yulang.B4TargetV3.Classify b registry state root (Yulang.CommonRoleOutermostResolver.Result.selected dictionary) →
    Acc (Yulang.CommonRoleOutermostResolver.Child (Yulang.B4TargetV3.Local b registry state)) root
@Yulang.GeneralDictionaryLocalReadbackExact.children_accessible : ∀ {v : Yulang.B4Target.Vocabulary}
  (b : Yulang.B4Target.SourceBoundary v) (registry : v.Registry) (state : v.State) (children : List v.Demand)
  (dictionaries : List Yulang.CommonRoleOutermostResolver.Dictionary),
  Yulang.CommonRoleOutermostResolver.All₂
      (fun child dictionary =>
        Yulang.B4TargetV3.Classify b registry state child
          (Yulang.CommonRoleOutermostResolver.Result.selected dictionary))
      children dictionaries →
    ∀ (child : v.Demand),
      child ∈ children → Acc (Yulang.CommonRoleOutermostResolver.Child (Yulang.B4TargetV3.Local b registry state)) child
@Yulang.GeneralDictionaryLocalReadbackExact.closure_selected : ∀ {v : Yulang.B4Target.Vocabulary}
  (b : Yulang.B4Target.SourceBoundary v) (registry : v.Registry) (state : v.State) (root : v.Demand)
  (dictionary : Yulang.CommonRoleOutermostResolver.Dictionary),
  Yulang.B4TargetV3.Classify b registry state root (Yulang.CommonRoleOutermostResolver.Result.selected dictionary) →
    ∀ (focus : v.Demand),
      Yulang.GeneralDictionaryLocalReadback.Reach (Yulang.B4TargetV3.Local b registry state) root focus →
        ∃ key children,
          Yulang.B4TargetV3.Local b registry state focus
            (Yulang.CommonRoleOutermostResolver.Frontier.selected key children)
@Yulang.GeneralDictionaryLocalReadbackExact.success_iff : ∀ {v : Yulang.B4Target.Vocabulary}
  (b : Yulang.B4Target.SourceBoundary v) (registry : v.Registry) (state : v.State) (root : v.Demand),
  (∃ dictionary,
      Yulang.B4TargetV3.Classify b registry state root
        (Yulang.CommonRoleOutermostResolver.Result.selected dictionary)) ↔
    (∀ (focus : v.Demand),
        Yulang.GeneralDictionaryLocalReadback.Reach (Yulang.B4TargetV3.Local b registry state) root focus →
          ∃ key children,
            Yulang.B4TargetV3.Local b registry state focus
              (Yulang.CommonRoleOutermostResolver.Frontier.selected key children)) ∧
      Acc (Yulang.CommonRoleOutermostResolver.Child (Yulang.B4TargetV3.Local b registry state)) root
Yulang.GeneralDictionarySupportRecursiveClosure.varying_source : ∀ (name : Nat),
  2 ≤ name →
    Yulang.GeneralNominalState.Models (Yulang.GeneralNominalExamples.state true)
      (Yulang.GeneralDictionarySupportRecursiveClosure.varying name)
Yulang.GeneralDictionarySupportRecursiveClosure.varying_model : ∀ (name : Nat),
  2 ≤ name →
    Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionarySupportRecursiveExample.finish.current
      (Yulang.GeneralDictionarySupportRecursiveClosure.varying name)
Yulang.GeneralDictionarySupportRecursiveClosure.refresh_large_unknown : ∀
  (next : Yulang.GeneralNominalCandidates.Context)
  (certificate :
    Yulang.GeneralNominalCycleSteps.Refresh Yulang.GeneralDictionarySupportRecursiveExample.finish.current next)
  (source : Nat), 2 ≤ source → ¬Yulang.GeneralNominalState.Known next.state source
Yulang.GeneralDictionarySupportRecursiveClosure.context_complete : Yulang.GeneralNominalSaturationState.ContextComplete
  Yulang.GeneralDictionarySupportRecursiveExample.finish.current
Yulang.GeneralDictionarySupportRecursiveClosure.point_closed : Yulang.GeneralNominalReobservationSteps.PointClosed
  Yulang.GeneralDictionarySupportRecursiveClassification.current.state
Yulang.GeneralDictionarySupportRecursiveClosure.sites_exact : Yulang.GeneralDictionarySupportRecursiveExample.finish.current.sites =
  [Yulang.GeneralDictionarySupportRecursiveClosure.rootSite, Yulang.GeneralDictionarySupportRecursiveClosure.leafSite]
Yulang.GeneralDictionarySupportRecursiveClosure.edges_exact : Yulang.GeneralDictionarySupportRecursiveExample.finish.current.edges =
  [(Yulang.GeneralNominalExamples.displayRoot, Yulang.GeneralNominalExamples.displayChild)]
Yulang.GeneralDictionarySupportRecursiveClosure.generated_cases : ∀
  (focus : Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles),
  Yulang.GeneralNominalSaturationState.Generated Yulang.GeneralDictionarySupportRecursiveExample.finish.current
      Yulang.GeneralNominalExamples.displayRoot focus →
    focus = Yulang.GeneralNominalExamples.displayRoot ∨ focus = Yulang.GeneralNominalExamples.displayChild
Yulang.GeneralDictionarySupportRecursiveClosure.sameInputs_no_cross : ¬Yulang.GeneralNominalFeedbackSites.SameInputs
    Yulang.GeneralDictionarySupportRecursiveExample.finish.current
    Yulang.GeneralDictionarySupportRecursiveClosure.rootSite Yulang.GeneralDictionarySupportRecursiveClosure.leafSite
Yulang.GeneralDictionarySupportRecursiveClosure.merges_closed : ∀
  (first last : Yulang.GeneralNominalDemandMerging.Site Yulang.GeneralDeclarationExamples.roles),
  first ∈ Yulang.GeneralDictionarySupportRecursiveExample.finish.current.sites →
    last ∈ Yulang.GeneralDictionarySupportRecursiveExample.finish.current.sites →
      Yulang.GeneralNominalFeedbackSites.SameInputs Yulang.GeneralDictionarySupportRecursiveExample.finish.current first
          last →
        Yulang.GeneralNominalSaturationState.Alias Yulang.GeneralDictionarySupportRecursiveExample.finish.current
          first.occurrence.identity last.occurrence.identity
Yulang.GeneralDictionarySupportRecursiveClosure.installs_committed : ∀
  (p : Yulang.GeneralNominalSaturationState.Packet Yulang.GeneralDeclarationExamples.roles),
  Yulang.GeneralNominalSaturationState.Generated Yulang.GeneralDictionarySupportRecursiveExample.finish.current
      Yulang.GeneralNominalExamples.displayRoot p.site.occurrence →
    Yulang.GeneralNominalFeedbackSteps.Installable Yulang.GeneralNominalExamples.registry
        Yulang.GeneralDictionarySupportRecursiveExample.finish.current p →
      Yulang.GeneralNominalFeedbackSteps.Committed Yulang.GeneralDictionarySupportRecursiveExample.finish.current p
Yulang.GeneralDictionarySupportRecursiveClosure.feedback_stable : Yulang.GeneralNominalFeedbackSteps.Stable
  Yulang.GeneralNominalExamples.registry Yulang.GeneralDictionarySupportRecursiveExample.finish.current
  Yulang.GeneralNominalExamples.displayRoot
Yulang.GeneralDictionarySupportRecursiveClosure.stable : Yulang.GeneralNominalSupportSteps.Stable
  Yulang.GeneralNominalExamples.registry Yulang.GeneralDictionarySupportRecursiveExample.finish
  Yulang.GeneralNominalExamples.displayRoot
Yulang.GeneralDictionarySupportRecursiveClosure.resolves : Yulang.CommonRoleOutermostResolver.Resolves
  (Yulang.B4TargetV3.Local
    (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles).toSourceBoundary
    Yulang.GeneralNominalExamples.registry Yulang.GeneralDictionarySupportRecursiveExample.finish)
  Yulang.GeneralNominalExamples.displayRoot
  (Yulang.CommonRoleOutermostResolver.Tree.selected 1 [Yulang.CommonRoleOutermostResolver.Tree.selected 3 []])
Yulang.GeneralDictionarySupportRecursiveClosure.completed : Yulang.B4TargetV5.Reachable
    (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
    Yulang.GeneralNominalExamples.registry Yulang.GeneralNominalExamples.displayRoot
    Yulang.GeneralDictionarySupportRecursiveExample.finish ∧
  Yulang.GeneralNominalSupportSteps.Stable Yulang.GeneralNominalExamples.registry
      Yulang.GeneralDictionarySupportRecursiveExample.finish Yulang.GeneralNominalExamples.displayRoot ∧
    Yulang.GeneralDictionarySupportRecursiveExample.finish.current.packets ≠ [] ∧
      Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionarySupportRecursiveExample.finish.current
          Yulang.GeneralNominalExamples.model ∧
        Yulang.B4TargetV3.Classify
            (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles).toSourceBoundary
            Yulang.GeneralNominalExamples.registry Yulang.GeneralDictionarySupportRecursiveExample.finish
            Yulang.GeneralNominalExamples.displayRoot
            (Yulang.CommonRoleOutermostResolver.Result.selected
              (Yulang.CommonRoleOutermostResolver.Dictionary.node 1
                [Yulang.CommonRoleOutermostResolver.Dictionary.node 3 []])) ∧
          ∀ (m : Yulang.GeneralNominalCommonBridge.Assignment),
            Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionarySupportRecursiveExample.finish.current
                m →
              Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralNominalExamples.registry
                Yulang.GeneralDictionarySupportRecursiveClassification.current m
                Yulang.GeneralNominalExamples.displayRoot
                (Yulang.CommonRoleOutermostResolver.Dictionary.node 1
                  [Yulang.CommonRoleOutermostResolver.Dictionary.node 3 []])
Yulang.GeneralDictionarySupportRecursiveClassification.models_of_source : ∀
  (m : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models (Yulang.GeneralNominalExamples.state true) m →
    Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionarySupportRecursiveExample.finish.current m
Yulang.GeneralDictionarySupportRecursiveJoint.parent_branch_at : ∀ (m : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionarySupportRecursiveExample.finish.current m →
    Yulang.GeneralNominalJointCandidates.BranchAt Yulang.GeneralNominalExamples.registry
      Yulang.GeneralDictionarySupportRecursiveExample.finish.current Yulang.GeneralNominalExamples.displayRoot 1 m
Yulang.GeneralDictionarySupportRecursiveJoint.leaf_branch_at : ∀ (m : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionarySupportRecursiveExample.finish.current m →
    Yulang.GeneralNominalJointCandidates.BranchAt Yulang.GeneralNominalExamples.registry
      Yulang.GeneralDictionarySupportRecursiveExample.finish.current Yulang.GeneralNominalExamples.displayChild 3 m
Yulang.GeneralDictionarySupportRecursiveJoint.parent_joint : Yulang.GeneralNominalJointCandidates.Joint
  Yulang.GeneralNominalExamples.registry Yulang.GeneralDictionarySupportRecursiveExample.finish.current
  Yulang.GeneralNominalExamples.displayRoot 1
Yulang.GeneralDictionarySupportRecursiveJoint.leaf_joint : Yulang.GeneralNominalJointCandidates.Joint
  Yulang.GeneralNominalExamples.registry Yulang.GeneralDictionarySupportRecursiveExample.finish.current
  Yulang.GeneralNominalExamples.displayChild 3
Yulang.GeneralDictionarySupportRecursiveJoint.generated_selected_joint : ∀
  (focus : Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles),
  Yulang.GeneralNominalSaturationState.Generated Yulang.GeneralDictionarySupportRecursiveExample.finish.current
      Yulang.GeneralNominalExamples.displayRoot focus →
    ∀ (key : Nat)
      (children : List (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)),
      Yulang.GeneralNominalSupportBoundary.Local Yulang.GeneralNominalExamples.registry
          Yulang.GeneralDictionarySupportRecursiveExample.finish focus
          (Yulang.CommonRoleOutermostResolver.Frontier.selected key children) →
        Yulang.GeneralNominalJointCandidates.Joint Yulang.GeneralNominalExamples.registry
          Yulang.GeneralDictionarySupportRecursiveExample.finish.current focus key
Yulang.GeneralDictionarySupportReadbackRegression.accessible : Acc
  (Yulang.CommonRoleOutermostResolver.Child Yulang.GeneralDictionarySupportReadbackRegression.actualLocal)
  Yulang.GeneralNominalExamples.displayRoot
Yulang.GeneralDictionarySupportReadbackRegression.generated_selected : ∀
  (focus : Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles),
  Yulang.GeneralNominalSaturationState.Generated Yulang.GeneralDictionarySupportRecursiveExample.finish.current
      Yulang.GeneralNominalExamples.displayRoot focus →
    ∃ key children,
      Yulang.GeneralNominalSupportBoundary.Local Yulang.GeneralNominalExamples.registry
        Yulang.GeneralDictionarySupportRecursiveExample.finish focus
        (Yulang.CommonRoleOutermostResolver.Frontier.selected key children)
Yulang.GeneralDictionarySupportReadbackRegression.extracted : ∃ dictionary,
  Yulang.B4TargetV3.Classify
      (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles).toSourceBoundary
      Yulang.GeneralNominalExamples.registry Yulang.GeneralDictionarySupportRecursiveExample.finish
      Yulang.GeneralNominalExamples.displayRoot (Yulang.CommonRoleOutermostResolver.Result.selected dictionary) ∧
    ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionarySupportRecursiveExample.finish.current model →
        Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralNominalExamples.registry
          Yulang.GeneralDictionarySupportRecursiveExample.finish.current.context model
          Yulang.GeneralNominalExamples.displayRoot dictionary
Yulang.GeneralDictionarySupportReadbackRegression.extracted_exact : ∃ dictionary,
  dictionary =
      Yulang.CommonRoleOutermostResolver.Dictionary.node 1 [Yulang.CommonRoleOutermostResolver.Dictionary.node 3 []] ∧
    Yulang.B4TargetV3.Classify
        (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles).toSourceBoundary
        Yulang.GeneralNominalExamples.registry Yulang.GeneralDictionarySupportRecursiveExample.finish
        Yulang.GeneralNominalExamples.displayRoot (Yulang.CommonRoleOutermostResolver.Result.selected dictionary) ∧
      ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
        Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionarySupportRecursiveExample.finish.current
            model →
          Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralNominalExamples.registry
            Yulang.GeneralDictionarySupportRecursiveExample.finish.current.context model
            Yulang.GeneralNominalExamples.displayRoot dictionary
Yulang.GeneralDictionaryEarlyMergeExample.checked : Yulang.GeneralDeclarations.DeclarationChecked
  Yulang.GeneralDeclarationExamples.constructors Yulang.GeneralDeclarationExamples.roles
  Yulang.GeneralDictionaryEarlyMergeExample.declaration
Yulang.GeneralDictionaryEarlyMergeExample.registry_checked : Yulang.GeneralDeclarations.Checked
  Yulang.GeneralDictionaryEarlyMergeExample.registry
Yulang.GeneralDictionaryEarlyMergeExample.all_source_decisions : ∀
  (root : Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles),
  (∀ (index : Fin (Yulang.GeneralDeclarationExamples.roles root.demand.role).arity),
      root.demand.arguments index = (0, 0)) →
    Yulang.GeneralNominalSupport.DecisionGuard (Yulang.GeneralDictionaryEarlyMergeExample.start root)
      Yulang.GeneralDictionaryEarlyMergeExample.registry root []
Yulang.GeneralDictionaryEarlyMergeExample.query : Yulang.GeneralNominalInspection.queries
    (Yulang.GeneralNominalExamples.state true) Yulang.GeneralNominalExamples.interpretation
    Yulang.GeneralDictionaryEarlyMergeExample.declaration =
  [Yulang.GeneralNominalInspection.Query.nominal 0 [Yulang.GeneralNominalInspection.Query.variables [0]]]
Yulang.GeneralDictionaryEarlyMergeExample.schema : Yulang.GeneralNominalRecursiveCandidates.generated
    Yulang.GeneralDictionaryEarlyMergeExample.registry (Yulang.GeneralNominalExamples.context true)
    Yulang.GeneralNominalExamples.displayRoot Yulang.GeneralDictionaryEarlyMergeExample.declaration
    Yulang.GeneralDictionaryEarlyMergeExample.checked [(0, 0)] =
  { }
Yulang.GeneralDictionaryEarlyMergeExample.branch : ∀ (m : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models (Yulang.GeneralNominalExamples.state true) m →
    Yulang.GeneralNominalRecursiveCandidates.BranchModels Yulang.GeneralDictionaryEarlyMergeExample.registry
      (Yulang.GeneralNominalExamples.context true) Yulang.GeneralNominalExamples.displayRoot
      Yulang.GeneralDictionaryEarlyMergeExample.declaration Yulang.GeneralDictionaryEarlyMergeExample.checked [(0, 0)] m
Yulang.GeneralDictionaryEarlyMergeExample.prepared : Yulang.GeneralNominalRecursiveCandidates.Prepared
  Yulang.GeneralDictionaryEarlyMergeExample.registry (Yulang.GeneralNominalExamples.context true)
  Yulang.GeneralNominalExamples.displayRoot Yulang.GeneralDictionaryEarlyMergeExample.declaration
  Yulang.GeneralDictionaryEarlyMergeExample.checked
Yulang.GeneralDictionaryEarlyMergeExample.survivor : Yulang.GeneralNominalRecursiveCandidates.Survivor
  Yulang.GeneralDictionaryEarlyMergeExample.registry (Yulang.GeneralNominalExamples.context true)
  Yulang.GeneralNominalExamples.displayRoot 1 Yulang.GeneralDictionaryEarlyMergeExample.children
Yulang.GeneralDictionaryEarlyMergeExample.selected : Yulang.GeneralNominalSupportBoundary.Local
  Yulang.GeneralDictionaryEarlyMergeExample.registry
  (Yulang.GeneralDictionaryEarlyMergeExample.start Yulang.GeneralNominalExamples.displayRoot)
  Yulang.GeneralNominalExamples.displayRoot
  (Yulang.CommonRoleOutermostResolver.Frontier.selected 1 Yulang.GeneralDictionaryEarlyMergeExample.children)
Yulang.GeneralDictionaryEarlyMergeExample.children_exact : Yulang.GeneralDictionaryEarlyMergeExample.children =
  [Yulang.GeneralDictionaryEarlyMergeExample.child 10, Yulang.GeneralDictionaryEarlyMergeExample.child 11]
Yulang.GeneralDictionaryEarlyMergeExample.enabled : Yulang.GeneralNominalFeedbackSteps.Installable
  Yulang.GeneralDictionaryEarlyMergeExample.registry
  (Yulang.GeneralDictionaryEarlyMergeExample.start Yulang.GeneralNominalExamples.displayRoot).current
  Yulang.GeneralDictionaryEarlyMergeExample.packet
Yulang.GeneralDictionaryEarlyMergeExample.packet_guard : Yulang.GeneralNominalSupportSteps.PacketGuard
  (Yulang.GeneralDictionaryEarlyMergeExample.start Yulang.GeneralNominalExamples.displayRoot)
  Yulang.GeneralDictionaryEarlyMergeExample.packet []
Yulang.GeneralDictionaryEarlyMergeExample.novel : ¬Yulang.GeneralNominalFeedbackSteps.Committed
    (Yulang.GeneralDictionaryEarlyMergeExample.start Yulang.GeneralNominalExamples.displayRoot).current
    Yulang.GeneralDictionaryEarlyMergeExample.packet
Yulang.GeneralDictionaryEarlyMergeExample.source : Yulang.GeneralNominalSourceFormation.InitialSource
  Yulang.GeneralDictionaryEarlyMergeExample.registry (Yulang.GeneralNominalExamples.context true)
  Yulang.GeneralNominalExamples.displayRoot
Yulang.GeneralDictionaryEarlyMergeExample.before_scheduled : Yulang.GeneralDictionaryEarlyMergeChoices.Scheduled
  Yulang.GeneralDictionaryEarlyMergeExample.registry Yulang.GeneralNominalExamples.displayRoot
  Yulang.GeneralDictionaryEarlyMergeExample.before
Yulang.GeneralDictionaryEarlyMergeExample.before_model : Yulang.GeneralNominalSaturationState.Models
  Yulang.GeneralDictionaryEarlyMergeExample.before.current Yulang.GeneralNominalExamples.model
Yulang.GeneralDictionaryEarlyMergeExample.site_present : ∀ (n : Nat),
  n = 10 ∨ n = 11 →
    Yulang.GeneralDictionaryEarlyMergeExample.site n ∈ Yulang.GeneralDictionaryEarlyMergeExample.before.current.sites
Yulang.GeneralDictionaryEarlyMergeExample.inputs_same : Yulang.GeneralNominalFeedbackSites.SameInputs
  Yulang.GeneralDictionaryEarlyMergeExample.before.current (Yulang.GeneralDictionaryEarlyMergeExample.site 10)
  (Yulang.GeneralDictionaryEarlyMergeExample.site 11)
Yulang.GeneralDictionaryEarlyMergeExample.actual_early_merge : Yulang.GeneralDictionaryEarlyMergeChoices.Scheduled
    Yulang.GeneralDictionaryEarlyMergeExample.registry Yulang.GeneralNominalExamples.displayRoot
    Yulang.GeneralDictionaryEarlyMergeExample.finish ∧
  Yulang.GeneralNominalSupportSteps.Step Yulang.GeneralDictionaryEarlyMergeExample.registry
      Yulang.GeneralNominalExamples.displayRoot Yulang.GeneralDictionaryEarlyMergeExample.before
      Yulang.GeneralDictionaryEarlyMergeExample.finish ∧
    Yulang.GeneralDictionaryEarlyMergeExample.finish.current.packets ≠ [] ∧
      Yulang.GeneralDictionaryEarlyMergeExample.finish.current.aliases ≠ []
Yulang.GeneralDictionaryEarlyMergeExample.finish_model : Yulang.GeneralNominalSaturationState.Models
  Yulang.GeneralDictionaryEarlyMergeExample.finish.current Yulang.GeneralNominalExamples.model
Yulang.GeneralDictionaryEarlyMergeExample.actual_path : Yulang.B4Target.Steps
  (Yulang.GeneralNominalSupportSteps.Step Yulang.GeneralDictionaryEarlyMergeExample.registry
    Yulang.GeneralNominalExamples.displayRoot)
  (Yulang.GeneralDictionaryEarlyMergeExample.start Yulang.GeneralNominalExamples.displayRoot)
  Yulang.GeneralDictionaryEarlyMergeExample.finish
Yulang.GeneralDictionaryEarlyMergeExample.reachable : Yulang.B4TargetV5.Reachable
  (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
  Yulang.GeneralDictionaryEarlyMergeExample.registry Yulang.GeneralNominalExamples.displayRoot
  Yulang.GeneralDictionaryEarlyMergeExample.finish
Yulang.GeneralDictionaryEarlyMergeExample.inhabited_early_merge : Yulang.B4TargetV5.Reachable
    (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
    Yulang.GeneralDictionaryEarlyMergeExample.registry Yulang.GeneralNominalExamples.displayRoot
    Yulang.GeneralDictionaryEarlyMergeExample.finish ∧
  Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryEarlyMergeExample.finish.current
      Yulang.GeneralNominalExamples.model ∧
    Yulang.GeneralDictionaryEarlyMergeExample.finish.current.packets ≠ [] ∧
      Yulang.GeneralDictionaryEarlyMergeExample.finish.current.aliases ≠ [] ∧
        Yulang.GeneralDictionarySupportChoices.Coherent Yulang.GeneralDictionaryEarlyMergeExample.finish.current
Yulang.GeneralDictionarySupportRecursiveTrace.initial_packet_unique : ∀
  (p : Yulang.GeneralNominalSaturationState.Packet Yulang.GeneralDeclarationExamples.roles),
  Yulang.GeneralNominalFeedbackSteps.Installable Yulang.GeneralNominalExamples.registry
      Yulang.GeneralDictionarySupportRecursiveExample.start.current p →
    p = Yulang.GeneralDictionarySupportRecursiveExample.packet
Yulang.GeneralDictionarySupportRecursiveTrace.initial_no_administrative : ∀
  (after : Yulang.GeneralNominalSaturationState.State Yulang.GeneralDeclarationExamples.roles),
  Yulang.GeneralNominalSupportSteps.Administrative Yulang.GeneralNominalExamples.registry
      Yulang.GeneralDictionarySupportRecursiveExample.start.current Yulang.GeneralNominalExamples.displayRoot after →
    False
Yulang.GeneralDictionarySupportRecursiveTrace.first_step_unique : ∀
  (after : Yulang.GeneralNominalSupport.Tracked Yulang.GeneralDeclarationExamples.roles),
  Yulang.GeneralNominalSupportSteps.Step Yulang.GeneralNominalExamples.registry
      Yulang.GeneralNominalExamples.displayRoot Yulang.GeneralDictionarySupportRecursiveExample.start after →
    after = Yulang.GeneralDictionarySupportRecursiveExample.finish
Yulang.GeneralDictionarySupportRecursiveTrace.finish_no_step : ∀
  (after : Yulang.GeneralNominalSupport.Tracked Yulang.GeneralDeclarationExamples.roles),
  ¬Yulang.GeneralNominalSupportSteps.Step Yulang.GeneralNominalExamples.registry
      Yulang.GeneralNominalExamples.displayRoot Yulang.GeneralDictionarySupportRecursiveExample.finish after
Yulang.GeneralDictionarySupportRecursiveTrace.trace_endpoints : ∀
  (after : Yulang.GeneralNominalSupport.Tracked Yulang.GeneralDeclarationExamples.roles),
  Yulang.B4Target.Steps
      (Yulang.GeneralNominalSupportSteps.Step Yulang.GeneralNominalExamples.registry
        Yulang.GeneralNominalExamples.displayRoot)
      Yulang.GeneralDictionarySupportRecursiveExample.start after →
    after = Yulang.GeneralDictionarySupportRecursiveExample.start ∨
      after = Yulang.GeneralDictionarySupportRecursiveExample.finish
Yulang.GeneralDictionarySupportRecursiveTrace.initial_not_stable : ¬Yulang.GeneralNominalSupportSteps.Stable
    Yulang.GeneralNominalExamples.registry Yulang.GeneralDictionarySupportRecursiveExample.start
    Yulang.GeneralNominalExamples.displayRoot
Yulang.GeneralDictionarySupportRecursiveTrace.stable_endpoint_iff : ∀
  (after : Yulang.GeneralNominalSupport.Tracked Yulang.GeneralDeclarationExamples.roles),
  Yulang.B4Target.Steps
      (Yulang.GeneralNominalSupportSteps.Step Yulang.GeneralNominalExamples.registry
        Yulang.GeneralNominalExamples.displayRoot)
      Yulang.GeneralDictionarySupportRecursiveExample.start after →
    (Yulang.GeneralNominalSupportSteps.Stable Yulang.GeneralNominalExamples.registry after
        Yulang.GeneralNominalExamples.displayRoot ↔
      after = Yulang.GeneralDictionarySupportRecursiveExample.finish)
@Yulang.GeneralDictionarySupportLocalOrder.inspection : ∀ {roles : Yulang.Roles.RoleDecls}
  {a b : Yulang.GeneralDeclarations.Declaration},
  Yulang.GeneralRegistryReordering.DeclarationReorders a b →
    ∀ (state : Yulang.GeneralNominalSupport.Tracked roles)
      (support : List (Yulang.GeneralSourceDictionaries.Occurrence roles))
      (bounds : List (Yulang.GeneralNominalInspection.Bounds state.current.context.state)),
      Yulang.GeneralNominalSupport.Inspection state support a bounds ↔
        Yulang.GeneralNominalSupport.Inspection state support b bounds
@Yulang.GeneralDictionarySupportLocalOrder.decision_guard_forward : ∀ {roles : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralDeclarations.Registry},
  Yulang.GeneralRegistryReordering.Reorders first last →
    ∀ (state : Yulang.GeneralNominalSupport.Tracked roles) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
      (support : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
      Yulang.GeneralNominalSupport.DecisionGuard state first root support →
        Yulang.GeneralNominalSupport.DecisionGuard state last root support
@Yulang.GeneralDictionarySupportLocalOrder.decision_guard : ∀ {roles : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralDeclarations.Registry},
  Yulang.GeneralRegistryReordering.Reorders first last →
    ∀ (state : Yulang.GeneralNominalSupport.Tracked roles) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
      (support : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
      Yulang.GeneralNominalSupport.DecisionGuard state first root support ↔
        Yulang.GeneralNominalSupport.DecisionGuard state last root support
@Yulang.GeneralDictionarySupportLocalOrder.support_pending : ∀ {roles : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralDeclarations.Registry},
  Yulang.GeneralRegistryReordering.Reorders first last →
    ∀ (state : Yulang.GeneralNominalSupport.Tracked roles) (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
      Yulang.GeneralNominalSupportBoundary.SupportPending first state root ↔
        Yulang.GeneralNominalSupportBoundary.SupportPending last state root
@Yulang.GeneralDictionarySupportLocalOrder.local_forward : ∀ {roles : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralDeclarations.Registry},
  Yulang.GeneralRegistryReordering.Reorders first last →
    first.roles = roles →
      ∀ (state : Yulang.GeneralNominalSupport.Tracked roles) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
        (frontier : Yulang.CommonRoleOutermostResolver.Frontier (Yulang.GeneralSourceDictionaries.Occurrence roles)),
        Yulang.GeneralNominalSupportBoundary.Local first state root frontier →
          Yulang.GeneralNominalSupportBoundary.Local last state root frontier
@Yulang.GeneralDictionarySupportLocalOrder.local_iff : ∀ {roles : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralDeclarations.Registry},
  Yulang.GeneralRegistryReordering.Reorders first last →
    first.roles = roles →
      ∀ (state : Yulang.GeneralNominalSupport.Tracked roles) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
        (frontier : Yulang.CommonRoleOutermostResolver.Frontier (Yulang.GeneralSourceDictionaries.Occurrence roles)),
        Yulang.GeneralNominalSupportBoundary.Local first state root frontier ↔
          Yulang.GeneralNominalSupportBoundary.Local last state root frontier
@Yulang.GeneralDictionarySupportLocalOrder.boundary_local : ∀ {roles : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralDeclarations.Registry},
  Yulang.GeneralRegistryReordering.Reorders first last →
    first.roles = roles →
      ∀ (state : Yulang.GeneralNominalSupport.Tracked roles) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
        (frontier : Yulang.CommonRoleOutermostResolver.Frontier (Yulang.GeneralSourceDictionaries.Occurrence roles)),
        Yulang.B4TargetV3.Local (Yulang.GeneralNominalSupportBoundary.boundary roles).toSourceBoundary first state root
            frontier ↔
          Yulang.B4TargetV3.Local (Yulang.GeneralNominalSupportBoundary.boundary roles).toSourceBoundary last state root
            frontier
@Yulang.GeneralDictionarySupportLocalOrder.resolves : ∀ {roles : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralDeclarations.Registry},
  Yulang.GeneralRegistryReordering.Reorders first last →
    first.roles = roles →
      ∀ (state : Yulang.GeneralNominalSupport.Tracked roles) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
        (tree : Yulang.CommonRoleOutermostResolver.Tree),
        Yulang.CommonRoleOutermostResolver.Resolves
            (Yulang.B4TargetV3.Local (Yulang.GeneralNominalSupportBoundary.boundary roles).toSourceBoundary first state)
            root tree ↔
          Yulang.CommonRoleOutermostResolver.Resolves
            (Yulang.B4TargetV3.Local (Yulang.GeneralNominalSupportBoundary.boundary roles).toSourceBoundary last state)
            root tree
@Yulang.GeneralDictionarySupportLocalOrder.child : ∀ {roles : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralDeclarations.Registry},
  Yulang.GeneralRegistryReordering.Reorders first last →
    first.roles = roles →
      ∀ (state : Yulang.GeneralNominalSupport.Tracked roles)
        (descendant parent : Yulang.GeneralSourceDictionaries.Occurrence roles),
        Yulang.CommonRoleOutermostResolver.Child
            (Yulang.B4TargetV3.Local (Yulang.GeneralNominalSupportBoundary.boundary roles).toSourceBoundary first state)
            descendant parent ↔
          Yulang.CommonRoleOutermostResolver.Child
            (Yulang.B4TargetV3.Local (Yulang.GeneralNominalSupportBoundary.boundary roles).toSourceBoundary last state)
            descendant parent
@Yulang.GeneralDictionarySupportLocalOrder.whereAccessible_iff : ∀ {roles : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralDeclarations.Registry},
  Yulang.GeneralRegistryReordering.Reorders first last →
    first.roles = roles →
      ∀ (state : Yulang.GeneralNominalSupport.Tracked roles) (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
        Acc
            (Yulang.CommonRoleOutermostResolver.Child
              (Yulang.B4TargetV3.Local (Yulang.GeneralNominalSupportBoundary.boundary roles).toSourceBoundary first
                state))
            root ↔
          Acc
            (Yulang.CommonRoleOutermostResolver.Child
              (Yulang.B4TargetV3.Local (Yulang.GeneralNominalSupportBoundary.boundary roles).toSourceBoundary last
                state))
            root
@Yulang.GeneralDictionarySupportLocalOrder.classify : ∀ {roles : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralDeclarations.Registry},
  Yulang.GeneralRegistryReordering.Reorders first last →
    first.roles = roles →
      ∀ (state : Yulang.GeneralNominalSupport.Tracked roles) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
        (outcome : Yulang.CommonRoleOutermostResolver.Result),
        Yulang.B4TargetV3.Classify (Yulang.GeneralNominalSupportBoundary.boundary roles).toSourceBoundary first state
            root outcome ↔
          Yulang.B4TargetV3.Classify (Yulang.GeneralNominalSupportBoundary.boundary roles).toSourceBoundary last state
            root outcome
Yulang.GeneralDictionaryEarlyMergeDiagnostics.parent_instance : Yulang.GeneralDictionaryRecursiveEvidence.Instance
  Yulang.GeneralDictionaryEarlyMergeExample.registry Yulang.GeneralDictionaryEarlyMergeDiagnostics.current
  Yulang.GeneralNominalExamples.model Yulang.GeneralNominalExamples.displayRoot 1
  Yulang.GeneralDictionaryEarlyMergeExample.children
Yulang.GeneralDictionaryEarlyMergeDiagnostics.acyclic : ∀ (source : Nat),
  ¬Yulang.GeneralNominalFeedbackK2.Cycle Yulang.GeneralDictionaryEarlyMergeExample.finish.current source
Yulang.GeneralDictionaryEarlyMergeDiagnostics.parent_selected : Yulang.GeneralNominalFeedbackK2.Local
  Yulang.GeneralDictionaryEarlyMergeExample.registry Yulang.GeneralDictionaryEarlyMergeExample.finish.current
  Yulang.GeneralNominalExamples.displayRoot
  (Yulang.CommonRoleOutermostResolver.Frontier.selected 1 Yulang.GeneralDictionaryEarlyMergeExample.children)
Yulang.GeneralDictionaryEarlyMergeDiagnostics.child_rejected : ∀ (n : Nat),
  Yulang.GeneralNominalFeedbackK2.Local Yulang.GeneralDictionaryEarlyMergeExample.registry
    Yulang.GeneralDictionaryEarlyMergeExample.finish.current (Yulang.GeneralDictionaryEarlyMergeExample.child n)
    Yulang.CommonRoleOutermostResolver.Frontier.rejected
Yulang.GeneralDictionaryEarlyMergeDiagnostics.supported_parent : Yulang.GeneralNominalSupportBoundary.Local
  Yulang.GeneralDictionaryEarlyMergeExample.registry Yulang.GeneralDictionaryEarlyMergeExample.finish
  Yulang.GeneralNominalExamples.displayRoot
  (Yulang.CommonRoleOutermostResolver.Frontier.selected 1 Yulang.GeneralDictionaryEarlyMergeExample.children)
Yulang.GeneralDictionaryEarlyMergeDiagnostics.supported_child : ∀ (n : Nat),
  Yulang.GeneralNominalSupportBoundary.Local Yulang.GeneralDictionaryEarlyMergeExample.registry
    Yulang.GeneralDictionaryEarlyMergeExample.finish (Yulang.GeneralDictionaryEarlyMergeExample.child n)
    Yulang.CommonRoleOutermostResolver.Frontier.rejected
Yulang.GeneralDictionaryEarlyMergeDiagnostics.diagnostic : Yulang.CommonRoleOutermostResolver.Resolves
  (Yulang.B4TargetV3.Local
    (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles).toSourceBoundary
    Yulang.GeneralDictionaryEarlyMergeExample.registry Yulang.GeneralDictionaryEarlyMergeExample.finish)
  Yulang.GeneralNominalExamples.displayRoot
  (Yulang.CommonRoleOutermostResolver.Tree.selected 1
    [Yulang.CommonRoleOutermostResolver.Tree.rejected, Yulang.CommonRoleOutermostResolver.Tree.rejected])
Yulang.GeneralDictionaryEarlyMergeDiagnostics.child_no_dictionary : ∀ (n : Nat)
  (dictionary : Yulang.CommonRoleOutermostResolver.Dictionary),
  ¬Yulang.B4TargetV3.Classify
      (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles).toSourceBoundary
      Yulang.GeneralDictionaryEarlyMergeExample.registry Yulang.GeneralDictionaryEarlyMergeExample.finish
      (Yulang.GeneralDictionaryEarlyMergeExample.child n)
      (Yulang.CommonRoleOutermostResolver.Result.selected dictionary)
Yulang.GeneralDictionaryEarlyMergeDiagnostics.root_no_classify : ∀
  (outcome : Yulang.CommonRoleOutermostResolver.Result),
  ¬Yulang.B4TargetV3.Classify
      (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles).toSourceBoundary
      Yulang.GeneralDictionaryEarlyMergeExample.registry Yulang.GeneralDictionaryEarlyMergeExample.finish
      Yulang.GeneralNominalExamples.displayRoot outcome
Yulang.GeneralDictionaryEarlyMergeDiagnostics.reachable_diagnostic : Yulang.B4TargetV5.Reachable
    (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
    Yulang.GeneralDictionaryEarlyMergeExample.registry Yulang.GeneralNominalExamples.displayRoot
    Yulang.GeneralDictionaryEarlyMergeExample.finish ∧
  Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryEarlyMergeExample.finish.current
      Yulang.GeneralNominalExamples.model ∧
    Yulang.GeneralDictionaryEarlyMergeExample.finish.current.packets ≠ [] ∧
      Yulang.GeneralDictionaryEarlyMergeExample.finish.current.aliases ≠ [] ∧
        Yulang.CommonRoleOutermostResolver.Resolves
            (Yulang.B4TargetV3.Local
              (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles).toSourceBoundary
              Yulang.GeneralDictionaryEarlyMergeExample.registry Yulang.GeneralDictionaryEarlyMergeExample.finish)
            Yulang.GeneralNominalExamples.displayRoot
            (Yulang.CommonRoleOutermostResolver.Tree.selected 1
              [Yulang.CommonRoleOutermostResolver.Tree.rejected, Yulang.CommonRoleOutermostResolver.Tree.rejected]) ∧
          ∀ (outcome : Yulang.CommonRoleOutermostResolver.Result),
            ¬Yulang.B4TargetV3.Classify
                (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles).toSourceBoundary
                Yulang.GeneralDictionaryEarlyMergeExample.registry Yulang.GeneralDictionaryEarlyMergeExample.finish
                Yulang.GeneralNominalExamples.displayRoot outcome
@Yulang.GeneralDictionaryDiagnosticAccessibility.resolved_accessible : ∀ {v : Yulang.B4Target.Vocabulary}
  (b : Yulang.B4Target.SourceBoundary v) (registry : v.Registry) (state : v.State) (root : v.Demand)
  (tree : Yulang.CommonRoleOutermostResolver.Tree),
  Yulang.CommonRoleOutermostResolver.Resolves (Yulang.B4TargetV3.Local b registry state) root tree →
    Acc (Yulang.CommonRoleOutermostResolver.Child (Yulang.B4TargetV3.Local b registry state)) root
@Yulang.GeneralDictionaryDiagnosticAccessibility.resolved_children_accessible : ∀ {v : Yulang.B4Target.Vocabulary}
  (b : Yulang.B4Target.SourceBoundary v) (registry : v.Registry) (state : v.State) (children : List v.Demand)
  (trees : List Yulang.CommonRoleOutermostResolver.Tree),
  Yulang.CommonRoleOutermostResolver.All₂
      (Yulang.CommonRoleOutermostResolver.Resolves (Yulang.B4TargetV3.Local b registry state)) children trees →
    ∀ (child : v.Demand),
      child ∈ children → Acc (Yulang.CommonRoleOutermostResolver.Child (Yulang.B4TargetV3.Local b registry state)) child
Yulang.GeneralDictionaryDiagnosticAccessibility.actual_accessible_without_classify : have registry :=
  Yulang.GeneralDictionaryEarlyMergeExample.registry;
have state := Yulang.GeneralDictionaryEarlyMergeExample.finish;
have root := Yulang.GeneralNominalExamples.displayRoot;
have b := (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles).toSourceBoundary;
Yulang.B4TargetV5.Reachable (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
    registry root state ∧
  Yulang.GeneralNominalSaturationState.Models state.current Yulang.GeneralNominalExamples.model ∧
    Acc (Yulang.CommonRoleOutermostResolver.Child (Yulang.B4TargetV3.Local b registry state)) root ∧
      ∀ (outcome : Yulang.CommonRoleOutermostResolver.Result), ¬Yulang.B4TargetV3.Classify b registry state root outcome
@Yulang.GeneralDictionaryDiagnosticTotality.diagnostic_exists : ∀ {v : Yulang.B4Target.Vocabulary}
  (b : Yulang.B4Target.SourceBoundary v) (registry : v.Registry) (state : v.State) (root : v.Demand),
  (∀ (focus : v.Demand),
      Yulang.GeneralDictionaryLocalReadback.Reach (Yulang.B4TargetV3.Local b registry state) root focus →
        ∃ frontier, Yulang.B4TargetV3.Local b registry state focus frontier) →
    Acc (Yulang.CommonRoleOutermostResolver.Child (Yulang.B4TargetV3.Local b registry state)) root →
      ∃ tree, Yulang.CommonRoleOutermostResolver.Resolves (Yulang.B4TargetV3.Local b registry state) root tree
@Yulang.GeneralDictionaryDiagnosticTotality.diagnostic_iff_accessible : ∀ {v : Yulang.B4Target.Vocabulary}
  (b : Yulang.B4Target.SourceBoundary v) (registry : v.Registry) (state : v.State) (root : v.Demand),
  (∀ (focus : v.Demand),
      Yulang.GeneralDictionaryLocalReadback.Reach (Yulang.B4TargetV3.Local b registry state) root focus →
        ∃ frontier, Yulang.B4TargetV3.Local b registry state focus frontier) →
    ((∃ tree, Yulang.CommonRoleOutermostResolver.Resolves (Yulang.B4TargetV3.Local b registry state) root tree) ↔
      Acc (Yulang.CommonRoleOutermostResolver.Child (Yulang.B4TargetV3.Local b registry state)) root)
@Yulang.GeneralDictionaryDiagnosticTotality.closure_local : ∀ {v : Yulang.B4Target.Vocabulary}
  (b : Yulang.B4Target.SourceBoundary v) (registry : v.Registry) (state : v.State) (root : v.Demand)
  (tree : Yulang.CommonRoleOutermostResolver.Tree),
  Yulang.CommonRoleOutermostResolver.Resolves (Yulang.B4TargetV3.Local b registry state) root tree →
    ∀ (focus : v.Demand),
      Yulang.GeneralDictionaryLocalReadback.Reach (Yulang.B4TargetV3.Local b registry state) root focus →
        ∃ frontier, Yulang.B4TargetV3.Local b registry state focus frontier
@Yulang.GeneralDictionaryDiagnosticTotality.diagnostic_iff : ∀ {v : Yulang.B4Target.Vocabulary}
  (b : Yulang.B4Target.SourceBoundary v) (registry : v.Registry) (state : v.State) (root : v.Demand),
  (∃ tree, Yulang.CommonRoleOutermostResolver.Resolves (Yulang.B4TargetV3.Local b registry state) root tree) ↔
    (∀ (focus : v.Demand),
        Yulang.GeneralDictionaryLocalReadback.Reach (Yulang.B4TargetV3.Local b registry state) root focus →
          ∃ frontier, Yulang.B4TargetV3.Local b registry state focus frontier) ∧
      Acc (Yulang.CommonRoleOutermostResolver.Child (Yulang.B4TargetV3.Local b registry state)) root
Yulang.GeneralDictionaryEarlyMergeClosure.models_of_source : ∀ (m : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models (Yulang.GeneralNominalExamples.state true) m →
    Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryEarlyMergeExample.finish.current m
Yulang.GeneralDictionaryEarlyMergeClosure.varying_model : ∀ (name : Nat),
  2 ≤ name →
    Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryEarlyMergeExample.finish.current
      (Yulang.GeneralDictionaryEarlyMergeClosure.varying name)
Yulang.GeneralDictionaryEarlyMergeClosure.refresh_large_unknown : ∀ (next : Yulang.GeneralNominalCandidates.Context)
  (certificate : Yulang.GeneralNominalCycleSteps.Refresh Yulang.GeneralDictionaryEarlyMergeExample.finish.current next)
  (source : Nat), 2 ≤ source → ¬Yulang.GeneralNominalState.Known next.state source
Yulang.GeneralDictionaryEarlyMergeClosure.context_complete : Yulang.GeneralNominalSaturationState.ContextComplete
  Yulang.GeneralDictionaryEarlyMergeExample.finish.current
Yulang.GeneralDictionaryEarlyMergeClosure.point_closed : Yulang.GeneralNominalReobservationSteps.PointClosed
  Yulang.GeneralDictionaryEarlyMergeDiagnostics.current.state
Yulang.GeneralDictionaryEarlyMergeClosure.sites_exact : Yulang.GeneralDictionaryEarlyMergeExample.finish.current.sites =
  [Yulang.GeneralDictionaryEarlyMergeClosure.rootSite, Yulang.GeneralDictionaryEarlyMergeExample.site 10,
    Yulang.GeneralDictionaryEarlyMergeExample.site 11]
Yulang.GeneralDictionaryEarlyMergeClosure.edges_exact : Yulang.GeneralDictionaryEarlyMergeExample.finish.current.edges =
  [(Yulang.GeneralNominalExamples.displayRoot, Yulang.GeneralDictionaryEarlyMergeExample.child 10),
    (Yulang.GeneralNominalExamples.displayRoot, Yulang.GeneralDictionaryEarlyMergeExample.child 11)]
Yulang.GeneralDictionaryEarlyMergeClosure.generated_cases : ∀
  (focus : Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles),
  Yulang.GeneralNominalSaturationState.Generated Yulang.GeneralDictionaryEarlyMergeExample.finish.current
      Yulang.GeneralNominalExamples.displayRoot focus →
    focus = Yulang.GeneralNominalExamples.displayRoot ∨
      focus = Yulang.GeneralDictionaryEarlyMergeExample.child 10 ∨
        focus = Yulang.GeneralDictionaryEarlyMergeExample.child 11
Yulang.GeneralDictionaryEarlyMergeClosure.sameInputs_no_cross : ∀ (n : Nat),
  ¬Yulang.GeneralNominalFeedbackSites.SameInputs Yulang.GeneralDictionaryEarlyMergeExample.finish.current
      Yulang.GeneralDictionaryEarlyMergeClosure.rootSite (Yulang.GeneralDictionaryEarlyMergeExample.site n)
Yulang.GeneralDictionaryEarlyMergeClosure.merges_closed : ∀
  (first last : Yulang.GeneralNominalDemandMerging.Site Yulang.GeneralDeclarationExamples.roles),
  first ∈ Yulang.GeneralDictionaryEarlyMergeExample.finish.current.sites →
    last ∈ Yulang.GeneralDictionaryEarlyMergeExample.finish.current.sites →
      Yulang.GeneralNominalFeedbackSites.SameInputs Yulang.GeneralDictionaryEarlyMergeExample.finish.current first
          last →
        Yulang.GeneralNominalSaturationState.Alias Yulang.GeneralDictionaryEarlyMergeExample.finish.current
          first.occurrence.identity last.occurrence.identity
Yulang.GeneralDictionaryEarlyMergeClosure.installs_committed : ∀
  (p : Yulang.GeneralNominalSaturationState.Packet Yulang.GeneralDeclarationExamples.roles),
  Yulang.GeneralNominalSaturationState.Generated Yulang.GeneralDictionaryEarlyMergeExample.finish.current
      Yulang.GeneralNominalExamples.displayRoot p.site.occurrence →
    Yulang.GeneralNominalFeedbackSteps.Installable Yulang.GeneralDictionaryEarlyMergeExample.registry
        Yulang.GeneralDictionaryEarlyMergeExample.finish.current p →
      Yulang.GeneralNominalFeedbackSteps.Committed Yulang.GeneralDictionaryEarlyMergeExample.finish.current p
Yulang.GeneralDictionaryEarlyMergeClosure.feedback_stable : Yulang.GeneralNominalFeedbackSteps.Stable
  Yulang.GeneralDictionaryEarlyMergeExample.registry Yulang.GeneralDictionaryEarlyMergeExample.finish.current
  Yulang.GeneralNominalExamples.displayRoot
Yulang.GeneralDictionaryEarlyMergeClosure.stable : Yulang.GeneralNominalSupportSteps.Stable
  Yulang.GeneralDictionaryEarlyMergeExample.registry Yulang.GeneralDictionaryEarlyMergeExample.finish
  Yulang.GeneralNominalExamples.displayRoot
Yulang.GeneralDictionaryEarlyMergeClosure.stable_diagnostic_without_classify : Yulang.B4TargetV5.Reachable
    (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
    Yulang.GeneralDictionaryEarlyMergeExample.registry Yulang.GeneralNominalExamples.displayRoot
    Yulang.GeneralDictionaryEarlyMergeExample.finish ∧
  Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryEarlyMergeExample.finish.current
      Yulang.GeneralNominalExamples.model ∧
    Yulang.GeneralNominalSupportSteps.Stable Yulang.GeneralDictionaryEarlyMergeExample.registry
        Yulang.GeneralDictionaryEarlyMergeExample.finish Yulang.GeneralNominalExamples.displayRoot ∧
      Acc
          (Yulang.CommonRoleOutermostResolver.Child
            (Yulang.B4TargetV3.Local
              (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles).toSourceBoundary
              Yulang.GeneralDictionaryEarlyMergeExample.registry Yulang.GeneralDictionaryEarlyMergeExample.finish))
          Yulang.GeneralNominalExamples.displayRoot ∧
        ∀ (outcome : Yulang.CommonRoleOutermostResolver.Result),
          ¬Yulang.B4TargetV3.Classify
              (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles).toSourceBoundary
              Yulang.GeneralDictionaryEarlyMergeExample.registry Yulang.GeneralDictionaryEarlyMergeExample.finish
              Yulang.GeneralNominalExamples.displayRoot outcome
Yulang.GeneralDictionaryEarlyMergeNoEvidence.child_no_instance : ∀ (n : Nat)
  (valuation : Yulang.GeneralNominalCommonBridge.Assignment) (key : Nat)
  (children : List (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)),
  ¬Yulang.GeneralDictionaryRecursiveEvidence.Instance Yulang.GeneralDictionaryEarlyMergeExample.registry
      Yulang.GeneralDictionaryEarlyMergeExample.finish.current.context valuation
      (Yulang.GeneralDictionaryEarlyMergeExample.child n) key children
Yulang.GeneralDictionaryEarlyMergeNoEvidence.child_no_evidence : ∀ (n : Nat)
  (valuation : Yulang.GeneralNominalCommonBridge.Assignment) (payload : Yulang.GeneralDictionaryReadback.Payload),
  ¬Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralDictionaryEarlyMergeExample.registry
      Yulang.GeneralDictionaryEarlyMergeExample.finish.current.context valuation
      (Yulang.GeneralDictionaryEarlyMergeExample.child n) payload
Yulang.GeneralDictionaryEarlyMergeNoEvidence.root_no_evidence : ∀
  (valuation : Yulang.GeneralNominalCommonBridge.Assignment) (payload : Yulang.GeneralDictionaryReadback.Payload),
  ¬Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralDictionaryEarlyMergeExample.registry
      Yulang.GeneralDictionaryEarlyMergeExample.finish.current.context valuation
      Yulang.GeneralNominalExamples.displayRoot payload
Yulang.GeneralDictionaryEarlyMergeNoEvidence.inhabited_no_evidence : Yulang.B4TargetV5.Reachable
    (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
    Yulang.GeneralDictionaryEarlyMergeExample.registry Yulang.GeneralNominalExamples.displayRoot
    Yulang.GeneralDictionaryEarlyMergeExample.finish ∧
  Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryEarlyMergeExample.finish.current
      Yulang.GeneralNominalExamples.model ∧
    Yulang.GeneralDictionaryEarlyMergeExample.finish.current.packets ≠ [] ∧
      Yulang.GeneralDictionaryEarlyMergeExample.finish.current.aliases ≠ [] ∧
        ∀ (payload : Yulang.GeneralDictionaryReadback.Payload),
          ¬Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralDictionaryEarlyMergeExample.registry
              Yulang.GeneralDictionaryEarlyMergeExample.finish.current.context Yulang.GeneralNominalExamples.model
              Yulang.GeneralNominalExamples.displayRoot payload
```
