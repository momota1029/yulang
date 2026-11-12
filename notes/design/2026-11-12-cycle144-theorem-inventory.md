# Cycle144 公開定理索引

量化子・前提は各Lean宣言の型が正本。以下の抜粋ではmoduleのnamespace/open/variable文脈を省略しているため、暗黙変数の展開はリンク元Leanを参照。本文報告のA〜Dに日本語の主張と適用範囲を記した。private補助はこの一覧に数えない。

## Yulang.GeneralDictionaryDiagnosticTotality

宣言: `diagnostic_exists`, `diagnostic_iff_accessible`, `closure_local`, `diagnostic_iff`

```lean
theorem diagnostic_exists (root : v.Demand)
    (localExists : ∀ focus, Reach (B4TargetV3.Local b registry state) root focus →
      ∃ frontier, B4TargetV3.Local b registry state focus frontier)
    (accessible : Acc (Child (B4TargetV3.Local b registry state)) root) :
    ∃ tree, Resolves (B4TargetV3.Local b registry state) root tree
```

```lean
theorem diagnostic_iff_accessible (root : v.Demand)
    (localExists : ∀ focus, Reach (B4TargetV3.Local b registry state) root focus →
      ∃ frontier, B4TargetV3.Local b registry state focus frontier) :
    (∃ tree, Resolves (B4TargetV3.Local b registry state) root tree) ↔
      Acc (Child (B4TargetV3.Local b registry state)) root
```

```lean
theorem closure_local (root : v.Demand) (tree : Tree)
    (resolved : Resolves (B4TargetV3.Local b registry state) root tree) :
    ∀ focus, Reach (B4TargetV3.Local b registry state) root focus →
      ∃ frontier, B4TargetV3.Local b registry state focus frontier
```

```lean
theorem diagnostic_iff (root : v.Demand) :
    (∃ tree, Resolves (B4TargetV3.Local b registry state) root tree) ↔
    (∀ focus, Reach (B4TargetV3.Local b registry state) root focus →
      ∃ frontier, B4TargetV3.Local b registry state focus frontier) ∧
      Acc (Child (B4TargetV3.Local b registry state)) root
```


## Yulang.GeneralDictionaryDiagnosticAccessibility

宣言: `resolved_accessible`, `resolved_children_accessible`, `actual_accessible_without_classify`

```lean
theorem resolved_accessible (root : v.Demand) (tree : Tree)
    (resolved : Resolves (B4TargetV3.Local b registry state) root tree) :
    Acc (Child (B4TargetV3.Local b registry state)) root
```

```lean
theorem resolved_children_accessible (children : List v.Demand) (trees : List Tree)
    (resolved : All₂ (Resolves (B4TargetV3.Local b registry state)) children trees) :
    ∀ child ∈ children, Acc (Child (B4TargetV3.Local b registry state)) child
```

```lean
theorem actual_accessible_without_classify :
    let registry
```


## Yulang.GeneralDictionaryEarlyMergeDiagnostics

宣言: `parent_instance`, `acyclic`, `parent_selected`, `child_rejected`, `supported_parent`, `supported_child`, `diagnostic`, `child_no_dictionary`, `root_no_classify`, `reachable_diagnostic`

```lean
theorem parent_instance : GeneralDictionaryRecursiveEvidence.Instance registry current model displayRoot 1 children
```

```lean
theorem acyclic (source : Nat) : ¬ GeneralNominalFeedbackK2.Cycle finish.current source
```

```lean
theorem parent_selected : GeneralNominalFeedbackK2.Local registry finish.current displayRoot (.selected 1 children)
```

```lean
theorem child_rejected (n : Nat) : GeneralNominalFeedbackK2.Local registry finish.current (child n) .rejected
```

```lean
theorem supported_parent : GeneralNominalSupportBoundary.Local registry finish displayRoot (.selected 1 children)
```

```lean
theorem supported_child (n : Nat) : GeneralNominalSupportBoundary.Local registry finish (child n) .rejected
```

```lean
theorem diagnostic : Resolves
    (B4TargetV3.Local (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary registry finish)
    displayRoot (.selected 1 [.rejected,.rejected])
```

```lean
theorem child_no_dictionary (n : Nat) (dictionary : Dictionary) :
    ¬ B4TargetV3.Classify (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary registry finish
      (child n) (.selected dictionary)
```

```lean
theorem root_no_classify (outcome : Result) :
    ¬ B4TargetV3.Classify (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary registry finish displayRoot outcome
```

```lean
theorem reachable_diagnostic :
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry displayRoot finish ∧
    Models finish.current model ∧ finish.current.packets ≠ [] ∧ finish.current.aliases ≠ [] ∧
    Resolves (B4TargetV3.Local (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary registry finish)
      displayRoot (.selected 1 [.rejected,.rejected]) ∧
    ∀ outcome, ¬ B4TargetV3.Classify (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary
      registry finish displayRoot outcome
```


## Yulang.GeneralDictionarySupportLocalOrder

宣言: `inspection`, `decision_guard_forward`, `decision_guard`, `support_pending`, `local_forward`, `local_iff`, `boundary_local`, `resolves`, `child`, `whereAccessible_iff`, `classify`

```lean
theorem inspection (pair : DeclarationReorders a b) (state : GeneralNominalSupport.Tracked roles)
    (support : List (Occurrence roles))
    (bounds : List (GeneralNominalInspection.Bounds state.current.context.state)) :
    GeneralNominalSupport.Inspection state support a bounds ↔
      GeneralNominalSupport.Inspection state support b bounds
```

```lean
theorem decision_guard_forward (order : Reorders first last)
    (state : GeneralNominalSupport.Tracked roles) (root : Occurrence roles) (support : List (Occurrence roles))
    (guard : GeneralNominalSupport.DecisionGuard state first root support) :
    GeneralNominalSupport.DecisionGuard state last root support
```

```lean
theorem decision_guard (order : Reorders first last)
    (state : GeneralNominalSupport.Tracked roles) (root : Occurrence roles) (support : List (Occurrence roles)) :
    GeneralNominalSupport.DecisionGuard state first root support ↔
      GeneralNominalSupport.DecisionGuard state last root support
```

```lean
theorem support_pending (order : Reorders first last)
    (state : GeneralNominalSupport.Tracked roles) (root : Occurrence roles) :
    GeneralNominalSupportBoundary.SupportPending first state root ↔
      GeneralNominalSupportBoundary.SupportPending last state root
```

```lean
theorem local_forward (order : Reorders first last) (roleEq : first.roles = roles)
    (state : GeneralNominalSupport.Tracked roles) (root : Occurrence roles) (frontier : Frontier (Occurrence roles))
    (valid : GeneralNominalSupportBoundary.Local first state root frontier) :
    GeneralNominalSupportBoundary.Local last state root frontier
```

```lean
theorem local_iff (order : Reorders first last) (roleEq : first.roles = roles)
    (state : GeneralNominalSupport.Tracked roles) (root : Occurrence roles) (frontier : Frontier (Occurrence roles)) :
    GeneralNominalSupportBoundary.Local first state root frontier ↔
      GeneralNominalSupportBoundary.Local last state root frontier
```

```lean
theorem boundary_local (order : Reorders first last) (roleEq : first.roles = roles)
    (state : GeneralNominalSupport.Tracked roles) (root : Occurrence roles) (frontier : Frontier (Occurrence roles)) :
    B4TargetV3.Local (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary first state root frontier ↔
      B4TargetV3.Local (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary last state root frontier
```

```lean
theorem resolves (order : Reorders first last) (roleEq : first.roles = roles)
    (state : GeneralNominalSupport.Tracked roles) (root : Occurrence roles) (tree : Tree) :
    Resolves (B4TargetV3.Local (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary first state) root tree ↔
      Resolves (B4TargetV3.Local (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary last state) root tree
```

```lean
theorem child (order : Reorders first last) (roleEq : first.roles = roles)
    (state : GeneralNominalSupport.Tracked roles) (descendant parent : Occurrence roles) :
    Child (B4TargetV3.Local (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary first state) descendant parent ↔
      Child (B4TargetV3.Local (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary last state) descendant parent
```

```lean
theorem whereAccessible_iff (order : Reorders first last) (roleEq : first.roles = roles)
    (state : GeneralNominalSupport.Tracked roles) (root : Occurrence roles) :
    Acc (Child (B4TargetV3.Local (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary first state)) root ↔
      Acc (Child (B4TargetV3.Local (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary last state)) root
```

```lean
theorem classify (order : Reorders first last) (roleEq : first.roles = roles)
    (state : GeneralNominalSupport.Tracked roles) (root : Occurrence roles) (outcome : Result) :
    B4TargetV3.Classify (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary first state root outcome ↔
      B4TargetV3.Classify (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary last state root outcome
```


## Yulang.GeneralDictionarySupportRecursiveTrace

宣言: `initial_packet_unique`, `initial_no_administrative`, `first_step_unique`, `finish_no_step`, `trace_endpoints`, `initial_not_stable`, `stable_endpoint_iff`

```lean
theorem initial_packet_unique (p : Packet roles)
    (enabled : GeneralNominalFeedbackSteps.Installable registry start.current p) : p = packet
```

```lean
theorem initial_no_administrative (after : State roles)
    (update : GeneralNominalSupportSteps.Administrative registry start.current displayRoot after) : False
```

```lean
theorem first_step_unique (after : GeneralNominalSupport.Tracked roles)
    (step : GeneralNominalSupportSteps.Step registry displayRoot start after) : after = finish
```

```lean
theorem finish_no_step (after : GeneralNominalSupport.Tracked roles) :
    ¬ GeneralNominalSupportSteps.Step registry displayRoot finish after
```

```lean
theorem trace_endpoints (after : GeneralNominalSupport.Tracked roles)
    (path : B4Target.Steps (GeneralNominalSupportSteps.Step registry displayRoot) start after) :
    after = start ∨ after = finish
```

```lean
theorem initial_not_stable : ¬ GeneralNominalSupportSteps.Stable registry start displayRoot
```

```lean
theorem stable_endpoint_iff (after : GeneralNominalSupport.Tracked roles)
    (path : B4Target.Steps (GeneralNominalSupportSteps.Step registry displayRoot) start after) :
    GeneralNominalSupportSteps.Stable registry after displayRoot ↔ after = finish
```


## Yulang.GeneralDictionaryEarlyMergeExample

宣言: `checked`, `registry_checked`, `all_source_decisions`, `query`, `schema`, `branch`, `prepared`, `survivor`, `selected`, `children_exact`, `enabled`, `packet_guard`, `novel`, `source`, `before_scheduled`, `before_model`, `site_present`, `inputs_same`, `actual_early_merge`, `finish_model`, `actual_path`, `reachable`, `inhabited_early_merge`

```lean
theorem checked : DeclarationChecked constructors roles declaration
```

```lean
theorem registry_checked : Checked registry
```

```lean
theorem all_source_decisions (root : Occurrence roles) (arguments : ∀ index, root.demand.arguments index = (0,0)) :
    DecisionGuard (start root) registry root []
```

```lean
theorem query : GeneralNominalInspection.queries (state true) interpretation declaration = [.nominal 0 [.variables [0]]]
```

```lean
theorem schema : generated registry (context true) displayRoot declaration checked [(0,0)] = {}
```

```lean
theorem branch (m : GeneralNominalCommonBridge.Assignment) (valid : GeneralNominalState.Models (state true) m) :
    BranchModels registry (context true) displayRoot declaration checked [(0,0)] m
```

```lean
theorem prepared : Prepared registry (context true) displayRoot declaration checked
```

```lean
theorem survivor : Survivor registry (context true) displayRoot 1 children
```

```lean
theorem selected : GeneralNominalSupportBoundary.Local registry (start displayRoot) displayRoot (.selected 1 children)
```

```lean
theorem children_exact : children = [child 10,child 11]
```

```lean
theorem enabled : GeneralNominalFeedbackSteps.Installable registry (start displayRoot).current packet
```

```lean
theorem packet_guard : PacketGuard (start displayRoot) packet []
```

```lean
theorem novel : ¬ GeneralNominalFeedbackSteps.Committed (start displayRoot).current packet
```

```lean
theorem source : GeneralNominalSourceFormation.InitialSource registry (context true) displayRoot where
  roles_agree
```

```lean
theorem before_scheduled : GeneralDictionaryEarlyMergeChoices.Scheduled registry displayRoot before
```

```lean
theorem before_model : Models before.current model
```

```lean
theorem site_present (n : Nat) (which : n = 10 ∨ n = 11) : site n ∈ before.current.sites
```

```lean
theorem inputs_same : GeneralNominalFeedbackSites.SameInputs before.current (site 10) (site 11)
```

```lean
theorem actual_early_merge : GeneralDictionaryEarlyMergeChoices.Scheduled registry displayRoot finish ∧
    Step registry displayRoot before finish ∧ finish.current.packets ≠ [] ∧ finish.current.aliases ≠ []
```

```lean
theorem finish_model : Models finish.current model
```

```lean
theorem actual_path : B4Target.Steps (Step registry displayRoot) (start displayRoot) finish
```

```lean
theorem reachable : B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry displayRoot finish
```

```lean
theorem inhabited_early_merge :
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry displayRoot finish ∧
    Models finish.current model ∧ finish.current.packets ≠ [] ∧ finish.current.aliases ≠ [] ∧
    GeneralDictionarySupportChoices.Coherent finish.current
```


## Yulang.GeneralDictionarySupportReadbackRegression

宣言: `accessible`, `generated_selected`, `extracted`, `extracted_exact`

```lean
theorem accessible : Acc (Child actualLocal) displayRoot
```

```lean
theorem generated_selected (focus : GeneralSourceDictionaries.Occurrence roles)
    (reached : Generated finish.current displayRoot focus) :
    ∃ key children, GeneralNominalSupportBoundary.Local registry finish focus (.selected key children)
```

```lean
theorem extracted : ∃ dictionary,
    B4TargetV3.Classify (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary
      registry finish displayRoot (.selected dictionary) ∧
    ∀ model, Models finish.current model →
      GeneralDictionaryRecursiveEvidence.Evidence registry finish.current.context model displayRoot dictionary
```

```lean
theorem extracted_exact : ∃ dictionary : Dictionary,
    dictionary = .node 1 [.node 3 []] ∧
    B4TargetV3.Classify (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary
      registry finish displayRoot (.selected dictionary) ∧
    ∀ model, Models finish.current model →
      GeneralDictionaryRecursiveEvidence.Evidence registry finish.current.context model displayRoot dictionary
```


## Yulang.GeneralDictionarySupportRecursiveJoint

宣言: `parent_branch_at`, `leaf_branch_at`, `parent_joint`, `leaf_joint`, `generated_selected_joint`

```lean
theorem parent_branch_at (m : GeneralNominalCommonBridge.Assignment) (valid : Models finish.current m) :
    BranchAt registry finish.current displayRoot 1 m
```

```lean
theorem leaf_branch_at (m : GeneralNominalCommonBridge.Assignment) (valid : Models finish.current m) :
    BranchAt registry finish.current displayChild 3 m
```

```lean
theorem parent_joint : Joint registry finish.current displayRoot 1
```

```lean
theorem leaf_joint : Joint registry finish.current displayChild 3
```

```lean
theorem generated_selected_joint (focus : Occurrence roles)
    (reached : Generated finish.current displayRoot focus)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalSupportBoundary.Local registry finish focus (.selected key children)) :
    Joint registry finish.current focus key
```


## Yulang.GeneralDictionarySupportRecursiveClosure

宣言: `varying_source`, `varying_model`, `refresh_large_unknown`, `context_complete`, `point_closed`, `sites_exact`, `edges_exact`, `generated_cases`, `sameInputs_no_cross`, `merges_closed`, `installs_committed`, `feedback_stable`, `stable`, `resolves`, `completed`

```lean
theorem varying_source (name : Nat) (large : 2 ≤ name) : GeneralNominalState.Models (state true) (varying name)
```

```lean
theorem varying_model (name : Nat) (large : 2 ≤ name) : Models finish.current (varying name)
```

```lean
theorem refresh_large_unknown (next : GeneralNominalCandidates.Context)
    (certificate : GeneralNominalCycleSteps.Refresh finish.current next) (source : Nat) (large : 2 ≤ source) :
    ¬ GeneralNominalState.Known next.state source
```

```lean
theorem context_complete : ContextComplete finish.current
```

```lean
theorem point_closed : GeneralNominalReobservationSteps.PointClosed current.state
```

```lean
theorem sites_exact : finish.current.sites = [rootSite,leafSite]
```

```lean
theorem edges_exact : finish.current.edges = [(displayRoot,displayChild)]
```

```lean
theorem generated_cases (focus : GeneralSourceDictionaries.Occurrence roles)
    (generated : Generated finish.current displayRoot focus) : focus = displayRoot ∨ focus = displayChild
```

```lean
theorem sameInputs_no_cross : ¬ GeneralNominalFeedbackSites.SameInputs finish.current rootSite leafSite
```

```lean
theorem merges_closed (first last : GeneralNominalDemandMerging.Site roles)
    (one : first ∈ finish.current.sites) (two : last ∈ finish.current.sites)
    (same : GeneralNominalFeedbackSites.SameInputs finish.current first last) :
    Alias finish.current first.occurrence.identity last.occurrence.identity
```

```lean
theorem installs_committed (p : Packet roles)
    (reached : Generated finish.current displayRoot p.site.occurrence)
    (enabled : GeneralNominalFeedbackSteps.Installable registry finish.current p) :
    GeneralNominalFeedbackSteps.Committed finish.current p
```

```lean
theorem feedback_stable : GeneralNominalFeedbackSteps.Stable registry finish.current displayRoot
```

```lean
theorem stable : GeneralNominalSupportSteps.Stable registry finish displayRoot
```

```lean
theorem resolves : CommonRoleOutermostResolver.Resolves
    (B4TargetV3.Local (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary registry finish)
    displayRoot (.selected 1 [.selected 3 []])
```

```lean
theorem completed :
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry displayRoot finish ∧
    GeneralNominalSupportSteps.Stable registry finish displayRoot ∧
    finish.current.packets ≠ [] ∧ Models finish.current model ∧
    B4TargetV3.Classify (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary
      registry finish displayRoot (.selected (.node 1 [.node 3 []])) ∧
    ∀ m, Models finish.current m → GeneralDictionaryRecursiveEvidence.Evidence registry current m displayRoot (.node 1 [.node 3 []])
```


## Yulang.GeneralDictionaryLocalReadbackExact

宣言: `classified_accessible`, `children_accessible`, `closure_selected`, `success_iff`

```lean
theorem classified_accessible (root : v.Demand) (dictionary : Dictionary)
    (classified : B4TargetV3.Classify b registry state root (.selected dictionary)) :
    Acc (Child (B4TargetV3.Local b registry state)) root
```

```lean
theorem children_accessible (children : List v.Demand) (dictionaries : List Dictionary)
    (classified : All₂ (fun child dictionary => B4TargetV3.Classify b registry state child (.selected dictionary))
      children dictionaries) :
    ∀ child ∈ children, Acc (Child (B4TargetV3.Local b registry state)) child
```

```lean
theorem closure_selected (root : v.Demand) (dictionary : Dictionary)
    (classified : B4TargetV3.Classify b registry state root (.selected dictionary)) :
    ∀ focus, Reach (B4TargetV3.Local b registry state) root focus →
      ∃ key children, B4TargetV3.Local b registry state focus (.selected key children)
```

```lean
theorem success_iff (root : v.Demand) :
    (∃ dictionary, B4TargetV3.Classify b registry state root (.selected dictionary)) ↔
    (∀ focus, Reach (B4TargetV3.Local b registry state) root focus →
      ∃ key children, B4TargetV3.Local b registry state focus (.selected key children)) ∧
      Acc (Child (B4TargetV3.Local b registry state)) root
```


## Yulang.GeneralDictionarySupportRecursiveClassification

宣言: `models_of_source`, `current_model`, `acyclic`, `parent_selected`, `leaf_selected`, `supported_parent_selected`, `supported_leaf_selected`, `classified`, `reachable_classified_dictionary`

```lean
theorem models_of_source (m : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models (state true) m) : Models finish.current m
```

```lean
theorem current_model : Models finish.current model
```

```lean
theorem acyclic (source : Nat) : ¬ GeneralNominalFeedbackK2.Cycle finish.current source
```

```lean
theorem parent_selected : GeneralNominalFeedbackK2.Local registry finish.current displayRoot (.selected 1 [displayChild])
```

```lean
theorem leaf_selected : GeneralNominalFeedbackK2.Local registry finish.current displayChild (.selected 3 [])
```

```lean
theorem supported_parent_selected : GeneralNominalSupportBoundary.Local registry finish displayRoot (.selected 1 [displayChild])
```

```lean
theorem supported_leaf_selected : GeneralNominalSupportBoundary.Local registry finish displayChild (.selected 3 [])
```

```lean
theorem classified : B4TargetV3.Classify (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary
    registry finish displayRoot (.selected (.node 1 [.node 3 []]))
```

```lean
theorem reachable_classified_dictionary :
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry displayRoot finish ∧
    Models finish.current model ∧
    B4TargetV3.Classify (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary
      registry finish displayRoot (.selected (.node 1 [.node 3 []])) ∧
    ∀ m, Models finish.current m → GeneralDictionaryRecursiveEvidence.Evidence registry current m displayRoot (.node 1 [.node 3 []])
```


## Yulang.GeneralDictionaryEarlyMergeBoundary

宣言: `packetFree_no_merge`, `initial_install_merge`

```lean
theorem packetFree_no_merge (registry : Registry) (root : Occurrence roles)
    (state : Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root state)
    (empty : state.current.packets = [])
    (first last : GeneralNominalDemandMerging.Site roles)
    (one : first ∈ state.current.sites) (two : last ∈ state.current.sites) :
    Alias state.current first.occurrence.identity last.occurrence.identity
```

```lean
theorem initial_install_merge (registry : Registry) (root : Occurrence roles)
    (context : GeneralNominalCandidates.Context)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (packet : Packet roles) (support : List (Occurrence roles))
    (atRoot : packet.site.occurrence = root)
    (enabled : GeneralNominalFeedbackSteps.Installable registry
      (GeneralNominalSupport.initial context root).current packet)
    (novel : ¬ GeneralNominalFeedbackSteps.Committed
      (GeneralNominalSupport.initial context root).current packet)
    (guard : PacketGuard (GeneralNominalSupport.initial context root) packet support)
    (child : Occurrence roles) (emitted : child ∈ packet.children)
    (freshId : child.identity ≠ root.identity)
    (last : GeneralNominalDemandMerging.Site roles)
    (present : last ∈ (GeneralNominalSupportSteps.install
      (GeneralNominalSupport.initial context root) packet support).current.sites)
    (different : child.identity ≠ last.occurrence.identity)
    (same : GeneralNominalFeedbackSites.SameInputs
      (GeneralNominalSupportSteps.install (GeneralNominalSupport.initial context root) packet support).current
      (GeneralNominalFeedbackSites.childSite packet child) last) :
    let before
```


## Yulang.GeneralDictionaryLocalReadback

宣言: `classified_exists`, `support_dictionary`

```lean
theorem classified_exists {v : B4Target.Vocabulary} (b : B4Target.SourceBoundary v)
    (registry : v.Registry) (state : v.State) (root : v.Demand)
    (selected : ∀ focus, Reach (B4TargetV3.Local b registry state) root focus →
      ∃ key children, B4TargetV3.Local b registry state focus (.selected key children))
    (accessible : Acc (Child (B4TargetV3.Local b registry state)) root) :
    ∃ dictionary, B4TargetV3.Classify b registry state root (.selected dictionary)
```

```lean
theorem support_dictionary {roles : Roles.RoleDecls} (registry : GeneralDeclarations.Registry)
    (state : GeneralNominalSupport.Tracked roles) (root : GeneralSourceDictionaries.Occurrence roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root state)
    (stable : GeneralNominalSupportSteps.Stable registry state root)
    (selected : ∀ focus,
      Reach (B4TargetV3.Local (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary registry state) root focus →
      ∃ key children, GeneralNominalSupportBoundary.Local registry state focus (.selected key children))
    (joint : (∃ model, GeneralNominalSaturationState.Models state.current model) →
      ∀ focus, GeneralNominalSaturationState.Generated state.current root focus → ∀ key children,
      GeneralNominalSupportBoundary.Local registry state focus (.selected key children) →
      GeneralNominalJointCandidates.Joint registry state.current focus key)
    (accessible : Acc (Child (B4TargetV3.Local
      (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary registry state)) root) :
    ∃ dictionary, B4TargetV3.Classify (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary
        registry state root (.selected dictionary) ∧
      ∀ model, GeneralNominalSaturationState.Models state.current model →
        GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context model root dictionary
```


## Yulang.GeneralDictionarySupportReadback

宣言: `classified_exists`, `uniform_dictionary`, `premises_inhabited`

```lean
theorem classified_exists (registry : Registry) (state : Tracked roles) (root : Occurrence roles)
    (reachable : B4TargetV5.Reachable (boundary roles) registry root state)
    (stable : GeneralNominalSupportSteps.Stable registry state root)
    (selected : ∀ focus, Generated state.current root focus →
      ∃ key children, Local registry state focus (.selected key children))
    (joint : ∀ focus, Generated state.current root focus → ∀ key children,
      Local registry state focus (.selected key children) →
      GeneralNominalJointCandidates.Joint registry state.current focus key)
    (accessible : Acc (Child (B4TargetV3.Local (boundary roles).toSourceBoundary registry state)) root) :
    ∃ dictionary, B4TargetV3.Classify (boundary roles).toSourceBoundary registry state root (.selected dictionary)
```

```lean
theorem uniform_dictionary (registry : Registry) (state : Tracked roles) (root : Occurrence roles)
    (reachable : B4TargetV5.Reachable (boundary roles) registry root state)
    (stable : GeneralNominalSupportSteps.Stable registry state root)
    (selected : ∀ focus, Generated state.current root focus →
      ∃ key children, Local registry state focus (.selected key children))
    (joint : ∀ focus, Generated state.current root focus → ∀ key children,
      Local registry state focus (.selected key children) →
      GeneralNominalJointCandidates.Joint registry state.current focus key)
    (accessible : Acc (Child (B4TargetV3.Local (boundary roles).toSourceBoundary registry state)) root) :
    ∃ dictionary, B4TargetV3.Classify (boundary roles).toSourceBoundary registry state root (.selected dictionary) ∧
      ∀ model, Models state.current model →
        GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context model root dictionary
```

```lean
theorem premises_inhabited (registry : Registry) (state : Tracked roles) (root : Occurrence roles)
    (selected : ∀ focus, Generated state.current root focus →
      ∃ key children, Local registry state focus (.selected key children))
    (joint : ∀ focus, Generated state.current root focus → ∀ key children,
      Local registry state focus (.selected key children) →
      GeneralNominalJointCandidates.Joint registry state.current focus key) :
    ∃ model, Models state.current model
```


## Yulang.GeneralDictionaryEarlyMergeChoices

宣言: `merge_coherent`, `scheduled_formed`, `scheduled_coherent`, `recorded_choices`

```lean
theorem merge_coherent (state : State roles)
    (first last : GeneralNominalDemandMerging.Site roles)
    (before : Coherent state) (early : Early state first last) :
    Coherent (GeneralNominalSaturationState.merge state first last)
```

```lean
theorem scheduled_formed (registry : Registry) (root : Occurrence roles)
    (state : Tracked roles) (path : Scheduled registry root state) :
    SourceFormed registry root state
```

```lean
theorem scheduled_coherent (registry : Registry) (root : Occurrence roles)
    (state : Tracked roles) (path : Scheduled registry root state) : Coherent state.current
```

```lean
theorem recorded_choices (registry : Registry) (root focus : Occurrence roles)
    (state : Tracked roles) (path : Scheduled registry root state)
    (packet : Packet roles) (recorded : packet ∈ state.current.packets)
    (atFocus : packet.site.occurrence.identity = focus.identity) :
    ∀ prior ∈ state.current.packets, Alias state.current focus.identity prior.site.occurrence.identity →
      prior.declaration.id = packet.declaration.id
```


## Yulang.GeneralDictionaryEarlyMergeRegression

宣言: `scheduled`, `coherent_not_current`

```lean
theorem scheduled : Scheduled registry root finish
```

```lean
theorem coherent_not_current :
    GeneralDictionarySupportChoices.Coherent finish.current ∧
    Models finish.current model ∧ finish.current.packets ≠ [] ∧
    ¬ GeneralDictionaryCurrentJournal.Current registry finish.current
```

