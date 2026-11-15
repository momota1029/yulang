# Cycle208 theorem inventory

各定理の変数は任意。以下の型に書いた前提を保持する。意味論の範囲・未解決条件を省略した無条件の主張ではない。

## GeneralDictionaryDefaultAncestry208

groundな点入力と既存のsource/coverage条件から、追加の停止仮定なしで据え付け深さ上限を構成する。 （主に補助・健全性側。完全性／主型性の完成は主張しない。）

```lean
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralDictionaryDefaultDepth208
open GeneralNominalCenteredHeadMatSemanticLabels
open GeneralNominalCenteredHeadMatCompilerSemantics (algebra)
open GeneralNominalInvocationAncestry (AtDepth child_identity)
open GeneralNominalCenteredTrace (clauseChild_mem)
open GeneralNominalPatersonLineage (mass)
variable {roles : Roles.RoleDecls} {root : Occurrence roles} {state : State roles}
```

### Yulang.GeneralDictionaryDefaultAncestry208.sites_bounded

```lean
theorem sites_bounded
    (production : EnabledHeadReadback registry context root)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
    (ground : GeneralNominalGroundAccessibility.GroundRoots context root rootLabels)
    (coverage : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation)
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ model, Models state model → ∀ site ∈ state.core.sites,
      ∃ depth labels, AtDepth registry context.state.seed root.identity depth site.occurrence.identity ∧
        Inputs (algebra registry.constructors context.interpretation) model site labels ∧
        depth + mass labels ≤ mass rootLabels
```

### Yulang.GeneralDictionaryDefaultAncestry208.installed_depth_bound

```lean
theorem installed_depth_bound
    (production : EnabledHeadReadback registry context root)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
    (ground : GeneralNominalGroundAccessibility.GroundRoots context root rootLabels)
    (coverage : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation) :
    InstalledDepthBound registry context root (mass rootLabels)
```

### Yulang.GeneralDictionaryDefaultAncestry208.head_readback

```lean
theorem head_readback : EnabledHeadReadback registry context root
```

### Yulang.GeneralDictionaryDefaultAncestry208.ground_depth_bound

```lean
theorem ground_depth_bound
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
    (ground : GeneralNominalGroundAccessibility.GroundRoots context root rootLabels)
    (coverage : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation) :
    InstalledDepthBound registry context root (mass rootLabels)
```

## GeneralDictionaryDefaultAvailability208

checkedかつ到達可能な任意のselected需要から現在のFrameとEffectを抽出する。据え付け可能性はchoice互換＋共通モデルと同値。 （主に補助・健全性側。完全性／主型性の完成は主張しない。）

```lean
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal
open GeneralDictionaryDefaultBoundary208 (boundary Local)
open GeneralNominalCenteredHeadAllocEncoding (registry)
variable {roles : Roles.RoleDecls} {state : State roles} {effect : Effect roles}
```

### Yulang.GeneralDictionaryDefaultAvailability208.selected_prior

```lean
theorem selected_prior
    (selected : Local value state focus (.selected key children)) :
    GeneralNominalCenteredHeadMatStepBoundary.Local (registry value) state focus (.selected key children)
```

### Yulang.GeneralDictionaryDefaultAvailability208.reachable_cache

```lean
theorem reachable_cache (reachable : B4TargetV7.Reachable (boundary roles) value root state) :
    GeneralNominalCenteredHeadMatStepCache.Valid state
```

### Yulang.GeneralDictionaryDefaultAvailability208.ready

```lean
theorem ready (checked : (boundary roles).Checked value)
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (frame : GeneralNominalCenteredHeadOutputs.Frame (registry value) state.core focus key plan) :
    GeneralNominalCenteredHeadMatEffects.Ready state.core focus plan
```

### Yulang.GeneralDictionaryDefaultAvailability208.emitted_complete

```lean
theorem emitted_complete (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (frame : GeneralNominalCenteredHeadOutputs.Frame (registry value) state.core focus key plan) :
    (GeneralNominalCenteredHeadMatPlans.emittedSchema plan).unknown = false
```

### Yulang.GeneralDictionaryDefaultAvailability208.selected_installable_iff

```lean
theorem selected_installable_iff (checked : (boundary roles).Checked value)
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (selected : Local value state effect.plan.packet.site.occurrence
      (.selected effect.plan.packet.declaration.id children))
    (registryEq : effect.registry = registry value) (snapshot : effect.snapshot = state.core) :
    GeneralDictionaryDefaultKernel208.Installable (registry value) state effect ↔
      GeneralNominalCycleSteps.ChoiceCompatible state.core.erased.current effect.plan.packet ∧
        ∃ model, Models state model ∧ GeneralNominalCenteredHeadMatStepPackets.Holds effect.plan model ∧ effect.Holds model
```

### Yulang.GeneralDictionaryDefaultAvailability208.selected_frame

```lean
theorem selected_frame
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (selected : Local value state focus (.selected key children)) :
    ∃ plan, GeneralNominalCenteredHeadOutputs.Frame (registry value) state.core focus key plan ∧ plan.packet.children = children
```

### Yulang.GeneralDictionaryDefaultAvailability208.selected_effect

```lean
theorem selected_effect (checked : (boundary roles).Checked value)
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (selected : Local value state focus (.selected key children)) :
    ∃ effect : Effect roles, effect.registry = registry value ∧ effect.snapshot = state.core ∧
      effect.plan.packet.site.occurrence = focus ∧ effect.plan.packet.declaration.id = key ∧
      effect.plan.packet.children = children
```

## GeneralDictionaryDefaultBoundary208

任意の入力・状態・需要のLocalは旧V7と同値。入力を狭めず、StepとStableだけを差し替える。 （主に補助・健全性側。完全性／主型性の完成は主張しない。）

```lean
open GeneralDeclarations GeneralSourceDictionaries CommonRoleOutermostResolver
open GeneralNominalCenteredHeadMatStepJournal (State)
open GeneralNominalCenteredHeadAllocEncoding (registry)
variable {roles : Roles.RoleDecls}
```

### Yulang.GeneralDictionaryDefaultBoundary208.ordinary_iff

```lean
theorem ordinary_iff : B4TargetV6.Local (boundary roles).toV6 r s d f ↔
    B4TargetV6.Local (GeneralNominalCenteredHeadAllocV7Boundary.boundary roles).toV6 r s d f
```

### Yulang.GeneralDictionaryDefaultBoundary208.local_iff

```lean
theorem local_iff : Local r s d f ↔ GeneralNominalCenteredHeadAllocV7Boundary.Local r s d f
```

### Yulang.GeneralDictionaryDefaultBoundary208.local_eq

```lean
theorem local_eq : Local (roles := roles) r s = GeneralNominalCenteredHeadAllocV7Boundary.Local r s
```

### Yulang.GeneralDictionaryDefaultBoundary208.local_total

```lean
theorem local_total (checked : (boundary roles).Checked r) (state : State roles) (root : Occurrence roles) :
    ∃ frontier, Local r state root frontier
```

### Yulang.GeneralDictionaryDefaultBoundary208.whereAccessible

```lean
theorem
```

### Yulang.GeneralDictionaryDefaultBoundary208.stepModels

```lean
theorem stepModels (step : Step r root before after) (valid : (boundary roles).Models after model) :
    (boundary roles).Models before model
```

### Yulang.GeneralDictionaryDefaultBoundary208.closure

```lean
theorem closure (halted : ∀ after, ¬ Step r root state after) :
    Stable r state root ∧ ∀ child, (boundary roles).Generated r state root child → Stable r state child
```

### Yulang.GeneralDictionaryDefaultBoundary208.initialReorders

```lean
theorem initialReorders (order : (boundary roles).Reorders first last)
    (initial : (boundary roles).Initial first root state) : (boundary roles).Initial last root state
```

### Yulang.GeneralDictionaryDefaultBoundary208.dictionaryRefl

```lean
theorem dictionaryRefl (dictionary : Dictionary) : (boundary roles).DictionaryEquivalent dictionary dictionary
```

### Yulang.GeneralDictionaryDefaultBoundary208.old_step

```lean
theorem old_step (step : GeneralNominalCenteredHeadAllocV7Boundary.Step r root before after) :
    Step r root before after
```

### Yulang.GeneralDictionaryDefaultBoundary208.old_steps

```lean
theorem old_steps (path : B4Target.Steps (GeneralNominalCenteredHeadAllocV7Boundary.Step r root) before after) :
    B4Target.Steps (Step r root) before after
```

### Yulang.GeneralDictionaryDefaultBoundary208.old_reachable

```lean
theorem old_reachable (reachable : B4TargetV7.Reachable (GeneralNominalCenteredHeadAllocV7Boundary.boundary roles) r root state) :
    B4TargetV7.Reachable (boundary roles) r root state
```

### Yulang.GeneralDictionaryDefaultBoundary208.stable_old

```lean
theorem stable_old (stable : Stable r state root) :
    GeneralNominalCenteredHeadAllocV7Boundary.Stable r state root
```

## GeneralDictionaryDefaultCache208

任意の新Step列は健全なcacheを保存する。 （主に補助・健全性側。完全性／主型性の完成は主張しない。）

```lean
open GeneralNominalCenteredHeadMatStepJournal (State initial)
open GeneralNominalCenteredHeadMatStepObservations
open GeneralCanonicalObservations (Observation Recorded)
variable {roles : Roles.RoleDecls} {before after : State roles}
```

### Yulang.GeneralDictionaryDefaultCache208.recorded_extend

```lean
theorem recorded_extend (recorded : Recorded (GeneralNominalState.extend snapshot reserved atoms) observation) :
    Recorded snapshot observation
```

### Yulang.GeneralDictionaryDefaultCache208.recorded_private

```lean
theorem recorded_private (packet : GeneralNominalSaturationState.Packet roles)
    (recorded : Recorded packet.privateContext.state observation) : Recorded packet.context.state observation
```

### Yulang.GeneralDictionaryDefaultCache208.administrative

```lean
theorem administrative (action : GeneralDictionaryDefaultKernel208.Administrative before focus after)
    (valid : Valid before) : Valid after
```

### Yulang.GeneralDictionaryDefaultCache208.at_cache

```lean
theorem at_cache (action : GeneralDictionaryDefaultKernel208.At registry before focus after)
    (valid : Valid before) : Valid after
```

### Yulang.GeneralDictionaryDefaultCache208.step_cache

```lean
theorem step_cache (action : GeneralDictionaryDefaultKernel208.Step registry root before after)
    (valid : Valid before) : Valid after
```

### Yulang.GeneralDictionaryDefaultCache208.steps_cache

```lean
theorem steps_cache (path : B4Target.Steps (GeneralDictionaryDefaultKernel208.Step registry root) before after)
    (valid : Valid before) : Valid after
```

### Yulang.GeneralDictionaryDefaultCache208.initial_valid

```lean
theorem initial_valid (context : GeneralNominalCandidates.Context) (root : GeneralSourceDictionaries.Occurrence roles) :
    Valid (initial context root)
```

## GeneralDictionaryDefaultCanonical208

同じchecked入力境界で、canonical exitの存在をsimulationから証明し、非計算的executorのLocal順序独立性を得る。 （主に補助・健全性側。完全性／主型性の完成は主張しない。）

```lean
open GeneralDeclarations GeneralSourceDictionaries GeneralRegistryReordering
open GeneralNominalCenteredHeadMatStepJournal (State)
open GeneralDictionaryDefaultBoundary208
open GeneralDictionaryDefaultExecutor208
open GeneralDictionaryDefaultSimulation208
open GeneralNominalCenteredHeadAllocEncoding (registry registry_reorders)
open GeneralCanonicalRegistry (canonical)
variable {roles : Roles.RoleDecls} {state : State roles}
```

### Yulang.GeneralDictionaryDefaultCanonical208.local_order

```lean
theorem local_order (order : Reorders first last) (state : State roles) (focus frontier) :
    Local first state focus frontier ↔ Local last state focus frontier
```

### Yulang.GeneralDictionaryDefaultCanonical208.local_related

```lean
theorem local_related {first last : State roles} (same : GeneralNominalCenteredHeadMatPermutationLedger.Related relation first last)
    (value : Registry) (roleEq : value.roles = roles) (focus frontier) :
    Local value first focus frontier ↔ Local value last focus frontier
```

### Yulang.GeneralDictionaryDefaultCanonical208.packet_free_reachable

```lean
theorem packet_free_reachable (order : Reorders first last)
    (reachable : B4TargetV7.Reachable (boundary roles) first root state)
    (empty : state.core.erased.current.packets = []) : B4TargetV7.Reachable (boundary roles) last root state
```

### Yulang.GeneralDictionaryDefaultCanonical208.canonical_checked

```lean
theorem canonical_checked (checked : (boundary roles).Checked value) : (boundary roles).Checked (canonical value)
```

### Yulang.GeneralDictionaryDefaultCanonical208.canonical_exit_lifting

```lean
theorem canonical_exit_lifting (checked : (boundary roles).Checked value)
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (empty : state.core.erased.current.packets = []) : ∃ final, LiftedExit value state root final
```

### Yulang.GeneralDictionaryDefaultCanonical208.final_lifted

```lean
theorem final_lifted (checked : (boundary roles).Checked value)
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (empty : state.core.erased.current.packets = []) : LiftedExit value state root (finalState value state root)
```

### Yulang.GeneralDictionaryDefaultCanonical208.registry_reachable

```lean
theorem registry_reachable (reachable : B4TargetV7.Reachable (boundary roles) value root state) :
    ∀ packet ∈ state.core.erased.current.packets, packet.registry = registry value
```

### Yulang.GeneralDictionaryDefaultCanonical208.distinct_shared_packet_free

```lean
theorem distinct_shared_packet_free (different : registry first ≠ registry last)
    (one : B4TargetV7.Reachable (boundary roles) first root state)
    (two : B4TargetV7.Reachable (boundary roles) last root state) : state.core.erased.current.packets = []
```

### Yulang.GeneralDictionaryDefaultCanonical208.choice_eq

```lean
theorem choice_eq {α : Sort u} {p q : α → Prop} (same : p = q)
    (one : ∃ x, p x) (two : ∃ x, q x) : Classical.choose one = Classical.choose two
```

### Yulang.GeneralDictionaryDefaultCanonical208.canonicalLocalOrder

```lean
theorem canonicalLocalOrder (roles : Roles.RoleDecls) : CanonicalLocalOrder roles
```

## GeneralDictionaryDefaultCodes208

planの静的同値と全class出力のmembershipを有限コードへ写し、全モデルで意味を保存する。 （主に補助・健全性側。完全性／主型性の完成は主張しない。）

```lean
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralDictionaryAssociatedProvenance
open GeneralNominalCenteredHeadMatEffects
open GeneralNominalCenteredHeadMatSemanticCodes (Config encode)
open GeneralNominalCenteredHeadMatPlanData (Same)
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls} {first last plan : Plan roles}
```

### Yulang.GeneralDictionaryDefaultCodes208.body_same

```lean
theorem body_same (same : Same first last) (target model body) :
    BodyHolds first target model body ↔ BodyHolds last target model body
```

### Yulang.GeneralDictionaryDefaultCodes208.class_same

```lean
theorem class_same (same : Same first last) (outputs model) :
    ClassMeaning outputs first model ↔ ClassMeaning outputs last model
```

### Yulang.GeneralDictionaryDefaultCodes208.class_membership

```lean
theorem class_membership (same : ∀ output, output ∈ firstOutputs ↔ output ∈ lastOutputs) :
    ClassMeaning firstOutputs plan model ↔ ClassMeaning lastOutputs plan model
```

### Yulang.GeneralDictionaryDefaultCodes208.classCode_mem

```lean
theorem classCode_mem
    (covered : GeneralNominalCenteredHeadOutputs.requests state root ⊆ pool) :
    output ∈ classCode pool state root ↔ output ∈ GeneralNominalCenteredHeadOutputs.requests state root
```

### Yulang.GeneralDictionaryDefaultCodes208.classCode_meaning

```lean
theorem classCode_meaning
    (covered : GeneralNominalCenteredHeadOutputs.requests state root ⊆ pool) :
    ClassMeaning (classCode pool state root) plan model ↔ ClassEffects state root plan model
```

### Yulang.GeneralDictionaryDefaultCodes208.classCode_sublist

```lean
theorem classCode_sublist : (classCode pool state root).Sublist pool
```

### Yulang.GeneralDictionaryDefaultCodes208.represents

```lean
theorem represents (configured : Config context plan)
    (covered : GeneralNominalCenteredHeadOutputs.requests state.core plan.packet.site.occurrence ⊆ pool) :
    GeneralDictionaryDefaultFinite208.Represents
      (signature context ⟨encode plan,classCode pool state.core plan.packet.site.occurrence⟩) state plan
```

### Yulang.GeneralDictionaryDefaultCodes208.filter_selection

```lean
theorem filter_selection (items : List α) (test : α → Bool) :
    items.filter test ∈ selections items
```

### Yulang.GeneralDictionaryDefaultCodes208.classCode_selected

```lean
theorem classCode_selected : classCode pool state root ∈ selections pool
```

## GeneralDictionaryDefaultCommitment208

Committed・Ready・モデルを前提に全classの出力証拠を得る。Installable＋Stableからnode証拠を組む補題は条件付きである。 （主に補助・健全性側。完全性／主型性の完成は主張しない。）

```lean
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal
open GeneralDictionaryDefaultKernel208
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls} {state : State roles} {plan : Plan roles}
  {model : Assignment} {root : Occurrence roles}
```

### Yulang.GeneralDictionaryDefaultCommitment208.committed_output

```lean
theorem committed_output (committed : Committed state plan)
    (ready : GeneralNominalCenteredHeadMatEffects.Ready state.core plan.packet.site.occurrence plan)
    (valid : Models state model)
    (member : output ∈ GeneralNominalCenteredHeadOutputs.requests state.core plan.packet.site.occurrence) :
    GeneralDictionaryDefaultEvidence204.OutputWitness plan model output
```

### Yulang.GeneralDictionaryDefaultCommitment208.alias_output

```lean
theorem alias_output (committed : Committed state plan)
    (ready : GeneralNominalCenteredHeadMatEffects.Ready state.core plan.packet.site.occurrence plan)
    (valid : Models state model)
    (alias : GeneralNominalSaturationState.Alias state.core.erased.current
      root.identity plan.packet.site.occurrence.identity)
    (member : output ∈ GeneralNominalCenteredHeadOutputs.requests state.core root) :
    GeneralDictionaryDefaultEvidence204.OutputWitness plan model output
```

### Yulang.GeneralDictionaryDefaultCommitment208.equal_named_outputs

```lean
theorem equal_named_outputs (committed : Committed state plan) (valid : Models state model)
    (one : first ∈ GeneralNominalCenteredHeadOutputs.requests state.core plan.packet.site.occurrence)
    (two : last ∈ GeneralNominalCenteredHeadOutputs.requests state.core plan.packet.site.occurrence)
    (named : first.name = last.name) :
    CommonNominalFullCarrier.Equivalent (model first.target).1 (model last.target).1
```

### Yulang.GeneralDictionaryDefaultCommitment208.certificate

```lean
theorem certificate (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core root key plan)
    (committed : Committed state plan)
    (ready : GeneralNominalCenteredHeadMatEffects.Ready state.core root plan)
    (valid : Models state model) :
    GeneralDictionaryTotalEvidence206.Certificate registry state.core model root key plan.packet.children plan
```

### Yulang.GeneralDictionaryDefaultCommitment208.enabled_stable_committed

```lean
theorem enabled_stable_committed (enabled : Installable registry state effect)
    (stable : Stable registry state effect.plan.packet.site.occurrence) : Committed state effect.plan
```

### Yulang.GeneralDictionaryDefaultCommitment208.enabled_stable_node

```lean
theorem enabled_stable_node (enabled : Installable registry state effect)
    (stable : Stable registry state effect.plan.packet.site.occurrence)
    (valid : Models state model)
    (given : CommonRoleOutermostResolver.All₂
      (GeneralDictionaryTotalEvidence206.Evidence registry state.core model)
      effect.plan.packet.children dictionaries) :
    GeneralDictionaryTotalEvidence206.Evidence registry state.core model
      effect.plan.packet.site.occurrence (.node effect.plan.packet.declaration.id dictionaries)
```

## GeneralDictionaryDefaultComposition208

全rolesについてTwelveLawsを証明。B4全体へのcompositionはEvidenceNodeとGeneratedChildrenを明示的に必要とする。 （主に補助・健全性側。完全性／主型性の完成は主張しない。）

```lean
open GeneralDeclarations GeneralSourceDictionaries CommonRoleOutermostResolver
open GeneralNominalCenteredHeadMatStepJournal (State)
open GeneralDictionaryDefaultBoundary208
open GeneralDictionaryDefaultExecutor208 (executor frontiers)
```

### Yulang.GeneralDictionaryDefaultComposition208.twelveLaws

```lean
theorem twelveLaws (roles : Roles.RoleDecls) : TwelveLaws roles
```

### Yulang.GeneralDictionaryDefaultComposition208.bridges

```lean
theorem bridges (laws : TwelveLaws roles) (node : EvidenceNode roles) (generated : GeneratedChildren roles) :
    B4SkeletonV7.B4Bridges (boundary roles) (executor roles) (frontiers roles)
```

### Yulang.GeneralDictionaryDefaultComposition208.composition

```lean
theorem composition (node : EvidenceNode roles) (generated : GeneratedChildren roles) :
    B4TargetV7.Statement (boundary roles) (executor roles)
```

### Yulang.GeneralDictionaryDefaultComposition208.dictionarySound

```lean
theorem dictionarySound (node : EvidenceNode roles) (generated : GeneratedChildren roles) :
    B4TargetV7.DictionarySound (boundary roles) (executor roles)
```

## GeneralDictionaryDefaultCover208

任意のchecked ground sourceについて、全class出力の部分列を含む具体的有限coverを作り、全新Stepの停止性を得る。 （主に補助・健全性側。完全性／主型性の完成は主張しない。）

```lean
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralDictionaryDefaultTrace208 GeneralDictionaryDefaultDepth208
open GeneralDictionaryDefaultEnumeration208
open GeneralNominalCenteredHeadMatSemanticCodes
open GeneralDictionaryDefaultFinite208 (FiniteCover)
open GeneralNominalOccurrenceEnumeration (basis)
open GeneralNominalActualTraceSupport (pool)
variable {roles : Roles.RoleDecls} {root : Occurrence roles} {state : State roles}
```

### Yulang.GeneralDictionaryDefaultCover208.centers_enumerated

```lean
theorem centers_enumerated (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    state.core.sites ⊆ centers checked source limit
```

### Yulang.GeneralDictionaryDefaultCover208.requests_enumerated

```lean
theorem requests_enumerated (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    GeneralNominalCenteredHeadOutputs.requests state.core focus ⊆ outputPool checked source limit
```

### Yulang.GeneralDictionaryDefaultCover208.accessible_of_depth_bound

```lean
theorem accessible_of_depth_bound (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (bound : InstalledDepthBound registry context root limit) :
    Acc (fun next current => Step registry root current next) (initial context root)
```

### Yulang.GeneralDictionaryDefaultCover208.ground_accessible

```lean
theorem ground_accessible
    (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
    (ground : GeneralNominalGroundAccessibility.GroundRoots context root rootLabels)
    (coverage : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation) :
    Acc (fun next current => Step registry root current next) (initial context root)
```

## GeneralDictionaryDefaultDepth208

初期状態からの新Step列について構成・据え付け深さの帰納的対応を保つ。 （主に補助・健全性側。完全性／主型性の完成は主張しない。）

```lean
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralNominalInvocationAncestry (AtDepth frontier bounded_enumerated allocationPool allocation_member)
variable {roles : Roles.RoleDecls} {before after state : State roles} {effect : Effect roles}
```

### Yulang.GeneralDictionaryDefaultDepth208.frame

```lean
theorem frame (enabled : Installable registry state effect) :
    GeneralNominalCenteredHeadOutputs.Frame registry state.core effect.plan.packet.site.occurrence
      effect.plan.packet.declaration.id effect.plan
```

### Yulang.GeneralDictionaryDefaultDepth208.configuration_step

```lean
theorem configuration_step (step : Step registry root before after) :
    after.core.erased.current.context.state.seed = before.core.erased.current.context.state.seed ∧
    after.core.erased.current.context.state.constructors = before.core.erased.current.context.state.constructors ∧
    after.core.erased.current.context.interpretation = before.core.erased.current.context.interpretation
```

### Yulang.GeneralDictionaryDefaultDepth208.configuration_trace

```lean
theorem configuration_trace (path : B4Target.Steps (Step registry root) before after) :
    after.core.erased.current.context.state.seed = before.core.erased.current.context.state.seed ∧
    after.core.erased.current.context.state.constructors = before.core.erased.current.context.state.constructors ∧
    after.core.erased.current.context.interpretation = before.core.erased.current.context.interpretation
```

### Yulang.GeneralDictionaryDefaultDepth208.plan_config

```lean
theorem plan_config (path : B4Target.Steps (Step registry root) (initial context root) state)
    (enabled : Installable registry state effect) :
    GeneralNominalCenteredHeadMatSemanticCodes.Config context effect.plan
```

### Yulang.GeneralDictionaryDefaultDepth208.installed_parents_finite

```lean
theorem installed_parents_finite (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (generated : GeneralNominalSaturationState.Generated state.core.erased.current root effect.plan.packet.site.occurrence)
    (enabled : Installable registry state effect) (novel : ¬ Committed state effect.plan) :
    effect.plan.packet.site.occurrence.identity ∈ frontier registry context.state.seed root.identity limit
```

### Yulang.GeneralDictionaryDefaultDepth208.reservations_finite

```lean
theorem reservations_finite (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (generated : GeneralNominalSaturationState.Generated state.core.erased.current root effect.plan.packet.site.occurrence)
    (enabled : Installable registry state effect) (novel : ¬ Committed state effect.plan) :
    GeneralNominalAllocation.reserved effect.plan.packet.context.state effect.plan.packet.registry effect.plan.packet.site.occurrence.identity ⊆
      allocationPool registry context.state.seed (frontier registry context.state.seed root.identity limit)
```

## GeneralDictionaryDefaultEnumeration208

明示した深さ上限の下で、全source、slot、occurrenceを有限集合で覆う。 （主に補助・健全性側。完全性／主型性の完成は主張しない。）

```lean
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralDictionaryDefaultTrace208 GeneralDictionaryDefaultDepth208
open GeneralNominalCenteredEnumeration (merge_sources)
open GeneralNominalActualTraceSupport (pool Supported administrative_support)
open GeneralNominalAllocationSupport
open GeneralNominalInvocationAncestry (frontier)
open GeneralNominalOccurrenceEnumeration (basis checkedFor child_enumerated)
open GeneralNominalSaturationState (Packet)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}
```

### Yulang.GeneralDictionaryDefaultEnumeration208.equate_sources

```lean
theorem equate_sources {before : GeneralNominalSaturationState.State roles}
    (one : first ∈ GeneralNominalState.sources before.context.state)
    (two : last ∈ GeneralNominalState.sources before.context.state) :
    GeneralNominalState.sources (GeneralNominalFeedbackSteps.equate before first last).context.state ⊆
      GeneralNominalState.sources before.context.state
```

### Yulang.GeneralDictionaryDefaultEnumeration208.source_pool

```lean
theorem source_pool (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    Supported state.core.erased.current (pool registry context root limit)
```

### Yulang.GeneralDictionaryDefaultEnumeration208.slot_pool

```lean
theorem slot_pool (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (slot : Fin state.core.erased.current.context.state.base.slots) :
    state.core.erased.current.context.state.base.source slot ∈ pool registry context root limit
```

### Yulang.GeneralDictionaryDefaultEnumeration208.sites_enumerated

```lean
theorem sites_enumerated (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ site ∈ state.core.erased.current.sites, site.occurrence ∈ basis checked source limit
```

## GeneralDictionaryDefaultExecutor208

任意のchecked入力と到達可能状態について、意味的executorが有限Stepで停止状態へ到達し、そのtreeを正確に構成する。 （主に補助・健全性側。完全性／主型性の完成は主張しない。）

```lean
open GeneralDeclarations GeneralSourceDictionaries CommonRoleOutermostResolver
open GeneralNominalCenteredHeadMatStepJournal (State)
open GeneralDictionaryDefaultBoundary208
open GeneralCanonicalRegistry (canonical)
variable {roles : Roles.RoleDecls}
```

### Yulang.GeneralDictionaryDefaultExecutor208.terminal_execution

```lean
theorem terminal_execution (registry : Registry) (state : State roles) (root : Occurrence roles) :
    B4Target.Steps (Step registry root) state (terminalState registry state root)
```

### Yulang.GeneralDictionaryDefaultExecutor208.terminal_exit

```lean
theorem terminal_exit (accessible : Acc (fun next current => Step registry root current next) state) :
    Exit registry state root (terminalState registry state root)
```

### Yulang.GeneralDictionaryDefaultExecutor208.final_execution

```lean
theorem final_execution (registry : Registry) (state : State roles) (root : Occurrence roles) :
    B4Target.Steps (Step registry root) state (finalState registry state root)
```

### Yulang.GeneralDictionaryDefaultExecutor208.final_exit

```lean
theorem final_exit (accessible : Acc (fun next current => Step registry root current next) state) :
    Exit registry state root (finalState registry state root)
```

### Yulang.GeneralDictionaryDefaultExecutor208.frontierLocal

```lean
theorem frontierLocal (checked : (boundary roles).Checked registry) (state : State roles) (root : Occurrence roles) (frontier) :
    (frontiers roles registry state).frontier root = frontier ↔ Local registry state root frontier
```

### Yulang.GeneralDictionaryDefaultExecutor208.localIdentity

```lean
theorem localIdentity (registry : Registry) (state : State roles) : (frontiers roles registry state).Local = Local registry state
```

### Yulang.GeneralDictionaryDefaultExecutor208.execution

```lean
theorem execution (registry : Registry) (_checked : (boundary roles).Checked registry) (state : State roles) (root : Occurrence roles)
    (_reachable : B4TargetV7.Reachable (boundary roles) registry root state) :
    B4Target.Steps (Step registry root) state ((executor roles).run registry state root).1
```

### Yulang.GeneralDictionaryDefaultExecutor208.halted_of_accessible

```lean
theorem halted_of_accessible (accessible : Acc (fun next current => Step registry root current next) state) :
    ∀ next, ¬ Step registry root ((executor roles).run registry state root).1 next
```

### Yulang.GeneralDictionaryDefaultExecutor208.treeExecution

```lean
theorem treeExecution (registry : Registry) (state : State roles) (root : Occurrence roles)
    (exact : FrontierExact (frontiers roles registry ((executor roles).run registry state root).1))
    (accessible : Acc (Child (frontiers roles registry ((executor roles).run registry state root).1).Local) root) :
    ((executor roles).run registry state root).2 =
      resolve (frontiers roles registry ((executor roles).run registry state root).1) exact root accessible
```

### Yulang.GeneralDictionaryDefaultExecutor208.progress

```lean
theorem progress (registry : Registry) (checked : (boundary roles).Checked registry) (state : State roles)
    (root : Occurrence roles) (reachable : B4TargetV7.Reachable (boundary roles) registry root state) :
    Acc (fun next current => Step registry root current next) state
```

### Yulang.GeneralDictionaryDefaultExecutor208.halted

```lean
theorem halted (registry : Registry) (checked : (boundary roles).Checked registry) (state : State roles)
    (root : Occurrence roles) (reachable : B4TargetV7.Reachable (boundary roles) registry root state) :
    ∀ next, ¬ Step registry root ((executor roles).run registry state root).1 next
```

### Yulang.GeneralDictionaryDefaultExecutor208.exact

```lean
theorem exact (registry : Registry) (checked : (boundary roles).Checked registry) (state : State roles)
    (root : Occurrence roles) (tree : Tree) :
    ((executor roles).run registry state root).2 = tree ↔
      Resolves (Local registry ((executor roles).run registry state root).1) root tree
```

## GeneralDictionaryDefaultFinite208

有限coverが与えられた場合のstrict progress。各新Stepで有限事実の未成立数が減る。cover自体はCoverで構成する。 （主に補助・健全性側。完全性／主型性の完成は主張しない。）

```lean
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralNominalSaturationState (Generated)
open GeneralNominalSharedBudget (Signature)
open GeneralNominalCenteredAccessibility (Fact facts signature_mem known_mem equal_mem point_mem alias_mem)
variable {roles : Roles.RoleDecls} {state before after : State roles}
```

### Yulang.GeneralDictionaryDefaultFinite208.monotone

```lean
theorem monotone (step : Step registry root before after) (fact : Fact roles) : Holds before fact → Holds after fact
```

### Yulang.GeneralDictionaryDefaultFinite208.novel_signature

```lean
theorem novel_signature (enabled : Installable registry state effect)
    (novel : ¬ Committed state effect.plan) (represents : Represents signature state effect.plan) :
    ¬ Holds state (.signature signature)
```

### Yulang.GeneralDictionaryDefaultFinite208.installed_signature

```lean
theorem installed_signature (snapshot : effect.snapshot = state.core)
    (represents : Represents signature state effect.plan) : Holds (install state effect) (.signature signature)
```

### Yulang.GeneralDictionaryDefaultFinite208.fresh_fact

```lean
theorem fresh_fact (cover : FiniteCover registry root (initial context root))
    (path : B4Target.Steps (Step registry root) (initial context root) before)
    (step : Step registry root before after) :
    ∃ fact ∈ facts cover.signatures cover.sources cover.occurrences, ¬ Holds before fact ∧ Holds after fact
```

### Yulang.GeneralDictionaryDefaultFinite208.accessible_of_cover

```lean
theorem accessible_of_cover (cover : FiniteCover registry root (initial context root)) :
    Acc (fun next current => Step registry root current next) (initial context root)
```

## GeneralDictionaryDefaultGrowth208

任意の新Stepでsource、site、edge等の蓄積を保つ。 （主に補助・健全性側。完全性／主型性の完成は主張しない。）

```lean
open GeneralNominalCenteredHeadMatStepJournal (State)
open GeneralNominalCenteredHeadMatStepTrustedGrowth
variable {roles : Roles.RoleDecls} {before after : State roles}
```

### Yulang.GeneralDictionaryDefaultGrowth208.administrative

```lean
theorem administrative (action : GeneralDictionaryDefaultKernel208.Administrative before focus after) : Growth before after
```

### Yulang.GeneralDictionaryDefaultGrowth208.at_growth

```lean
theorem at_growth (action : GeneralDictionaryDefaultKernel208.At registry before focus after) : Growth before after
```

### Yulang.GeneralDictionaryDefaultGrowth208.step

```lean
theorem step (action : GeneralDictionaryDefaultKernel208.Step registry root before after) : Growth before after
```

## GeneralDictionaryDefaultKernel208

任意の新Stepについてモデルが減少する。据え付け後は全schemaでCommitted。旧Stepは新Stepに含まれるが、逆向きは主張しない。 （主に補助・健全性側。完全性／主型性の完成は主張しない。）

```lean
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalSaturationState (Generated)
variable {roles : Roles.RoleDecls} {state before after : State roles} {effect : Effect roles} {model : Assignment}
```

### Yulang.GeneralDictionaryDefaultKernel208.administrative_models

```lean
theorem administrative_models (action : Administrative before focus after) (valid : Models after model) : Models before model
```

### Yulang.GeneralDictionaryDefaultKernel208.stepModels

```lean
theorem stepModels (step : Step registry root before after) (valid : Models after model) : Models before model
```

### Yulang.GeneralDictionaryDefaultKernel208.steps_models

```lean
theorem steps_models (path : B4Target.Steps (Step registry root) before after) :
    ∀ model, Models after model → Models before model
```

### Yulang.GeneralDictionaryDefaultKernel208.closure

```lean
theorem closure (halted : ∀ after, ¬ Step registry root state after) :
    Stable registry state root ∧ ∀ child, Generated state.core.erased.current root child → Stable registry state child
```

### Yulang.GeneralDictionaryDefaultKernel208.installable_selected

```lean
theorem installable_selected (enabled : Installable registry state effect) :
    GeneralNominalCenteredHeadMatStepLocal.Local registry state effect.plan.packet.site.occurrence
      (.selected effect.plan.packet.declaration.id effect.plan.packet.children)
```

### Yulang.GeneralDictionaryDefaultKernel208.installed_committed

```lean
theorem installed_committed (snapshot : effect.snapshot = state.core) : Committed (install state effect) effect.plan
```

### Yulang.GeneralDictionaryDefaultKernel208.committed_packet

```lean
theorem committed_packet (given : Committed state plan) :
    GeneralNominalCenteredHeadMatStepKernel.Committed state plan
```

### Yulang.GeneralDictionaryDefaultKernel208.committed_class

```lean
theorem committed_class (given : Committed state plan) (valid : Models state model) :
    GeneralNominalCenteredHeadMatEffects.ClassEffects state.core plan.packet.site.occurrence plan model
```

### Yulang.GeneralDictionaryDefaultKernel208.old_at

```lean
theorem old_at (action : GeneralNominalCenteredHeadMatStepKernel.At registry state focus after) :
    At registry state focus after
```

### Yulang.GeneralDictionaryDefaultKernel208.stable_old

```lean
theorem stable_old (stable : Stable registry state root) :
    GeneralNominalCenteredHeadMatStepKernel.Stable registry state root
```

## GeneralDictionaryDefaultLive208

checkedかつ新Step到達可能な状態で、据え付け共通モデル条件を現在journal・packet・選択effectの同時成立へ還元する。モデルの存在自体は導かない。 （主に補助・健全性側。完全性／主型性の完成は主張しない。）

```lean
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal
open GeneralNominalCenteredHeadMatCompletionLive (class_effects_install effect_present)
open GeneralDictionaryDefaultBoundary208 (boundary)
open GeneralNominalCenteredHeadAllocEncoding (registry)
variable {roles : Roles.RoleDecls} {state : State roles} {effect : Effect roles}
```

### Yulang.GeneralDictionaryDefaultLive208.installation_models_iff

```lean
theorem installation_models_iff (checked : (boundary roles).Checked value)
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (registryEq : effect.registry = registry value) (snapshot : effect.snapshot = state.core) (model) :
    InstallationModels state effect model ↔ Models state model ∧
      GeneralNominalCenteredHeadMatStepPackets.Holds effect.plan model ∧ effect.Holds model
```

### Yulang.GeneralDictionaryDefaultLive208.extension_iff

```lean
theorem extension_iff (checked : (boundary roles).Checked value)
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (registryEq : effect.registry = registry value) (snapshot : effect.snapshot = state.core) :
    GeneralNominalCenteredHeadMatStepAvailability.Extension state effect ↔
      GeneralNominalCycleSteps.ChoiceCompatible state.core.erased.current effect.plan.packet ∧
        ∃ model, Models state model ∧ GeneralNominalCenteredHeadMatStepPackets.Holds effect.plan model ∧ effect.Holds model
```

### Yulang.GeneralDictionaryDefaultLive208.common_successor_model

```lean
theorem common_successor_model (checked : (boundary roles).Checked value)
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (registryEq : effect.registry = registry value) (snapshot : effect.snapshot = state.core)
    (valid : Models state model) (branch : GeneralNominalCenteredHeadMatStepPackets.Holds effect.plan model)
    (chosen : effect.Holds model) : Models (install state effect) model
```

## GeneralDictionaryDefaultMonotonicity208

任意の新Stepでrawモデル制限、known、point、edgeを保つ。動的な全Committedの一般単調性は仮定しない。 （主に補助・健全性側。完全性／主型性の完成は主張しない。）

```lean
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
variable {roles : Roles.RoleDecls} {before after : State roles}
```

### Yulang.GeneralDictionaryDefaultMonotonicity208.raw_models

```lean
theorem raw_models (action : At registry before focus after)
    (valid : GeneralNominalState.Models after.core.erased.current.context.state model) :
    GeneralNominalState.Models before.core.erased.current.context.state model
```

### Yulang.GeneralDictionaryDefaultMonotonicity208.known

```lean
theorem known (action : At registry before focus after) (identity : Nat)
    (prior : GeneralNominalState.Known before.core.erased.current.context.state identity) :
    GeneralNominalState.Known after.core.erased.current.context.state identity
```

### Yulang.GeneralDictionaryDefaultMonotonicity208.point

```lean
theorem point (action : At registry before focus after)
    (prior : GeneralNominalReobservationOrder.Point before.core.erased.current identity) :
    GeneralNominalReobservationOrder.Point after.core.erased.current identity
```

### Yulang.GeneralDictionaryDefaultMonotonicity208.edges

```lean
theorem edges (action : At registry before focus after) :
    before.core.erased.current.edges ⊆ after.core.erased.current.edges
```

## GeneralDictionaryDefaultProduction208

実際の格納planから生成子を無条件に得る。残るFreshCompletionを仮定するとGeneratedChildrenを得る。B4にはさらにEvidenceNodeが必要。 （主に補助・健全性側。完全性／主型性の完成は主張しない。）

```lean
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal
open GeneralDictionaryDefaultBoundary208
open GeneralNominalCenteredHeadMatStepAvailability (Extension)
variable {roles : Roles.RoleDecls}
```

### Yulang.GeneralDictionaryDefaultProduction208.generated_of_recorded

```lean
theorem generated_of_recorded
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (reached : focus = root ∨ (boundary roles).Generated value state root focus)
    (recorded : Recorded state focus key children) (member : child ∈ children) :
    (boundary roles).Generated value state root child
```

### Yulang.GeneralDictionaryDefaultProduction208.generated_of_fresh

```lean
theorem generated_of_fresh (checked : (boundary roles).Checked value) (effect : Effect roles)
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (reached : effect.plan.packet.site.occurrence = root ∨
      (boundary roles).Generated value state root effect.plan.packet.site.occurrence)
    (stable : Stable value state effect.plan.packet.site.occurrence)
    (selected : Local value state effect.plan.packet.site.occurrence
      (.selected effect.plan.packet.declaration.id children))
    (registryEq : effect.registry = GeneralNominalCenteredHeadAllocEncoding.registry value)
    (snapshot : effect.snapshot = state.core) (extension : Extension state effect)
    (member : child ∈ effect.plan.packet.children) : (boundary roles).Generated value state root child
```

### Yulang.GeneralDictionaryDefaultProduction208.generatedChildren

```lean
theorem generatedChildren (fresh : FreshCompletion roles) :
    B4SkeletonV7.GeneratedChildren (boundary roles)
```

### Yulang.GeneralDictionaryDefaultProduction208.composition

```lean
theorem composition (node : GeneralDictionaryDefaultComposition208.EvidenceNode roles)
    (fresh : FreshCompletion roles) :
    B4TargetV7.Statement (boundary roles) (GeneralDictionaryDefaultExecutor208.executor roles)
```

## GeneralDictionaryDefaultProvenance208

任意の明示/default供給判断に対応するschema entryを作り、明示上書きが同じ出力のdefault entryを排除することを証明。 （主に補助・健全性側。完全性／主型性の完成は主張しない。）

```lean
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralDictionaryAssociatedProvenance
open GeneralDictionaryDefaultSchema208
variable {roles : Roles.RoleDecls} {state : GeneralNominalCenteredSteps.State roles}
  {root : Occurrence roles} {plan : Plan roles} {output : GeneralSourceState.Output}
```

### Yulang.GeneralDictionaryDefaultProvenance208.supplied_entry

```lean
theorem supplied_entry
    (member : output ∈ GeneralNominalCenteredHeadOutputs.requests state root)
    (supplied : Supplies roles plan.packet.declaration output.name body) :
    Entry.mk output (some body) ∈ entries state root plan
```

### Yulang.GeneralDictionaryDefaultProvenance208.explicit_entry

```lean
theorem explicit_entry
    (member : output ∈ GeneralNominalCenteredHeadOutputs.requests state root)
    (present : equation ∈ plan.packet.declaration.associated)
    (named : equation.name = output.name) :
    Entry.mk output (some (.explicit equation)) ∈ entries state root plan
```

### Yulang.GeneralDictionaryDefaultProvenance208.default_entry

```lean
theorem default_entry
    (member : output ∈ GeneralNominalCenteredHeadOutputs.requests state root)
    (absent : ∀ equation ∈ plan.packet.declaration.associated, equation.name ≠ output.name)
    (declared : (roles plan.packet.declaration.role).assoc output.name = some (some rhs)) :
    Entry.mk output (some (.default plan.packet.declaration.role output.name rhs)) ∈ entries state root plan
```

### Yulang.GeneralDictionaryDefaultProvenance208.override_excludes_default

```lean
theorem override_excludes_default
    (present : equation ∈ plan.packet.declaration.associated)
    (named : equation.name = output.name) :
    Entry.mk output (some (.default role name rhs)) ∉ entries state root plan
```

### Yulang.GeneralDictionaryDefaultProvenance208.schema_enforces_supplied

```lean
theorem schema_enforces_supplied
    (schema : SchemaHolds state root plan model)
    (member : output ∈ GeneralNominalCenteredHeadOutputs.requests state root)
    (supplied : Supplies roles plan.packet.declaration output.name body) :
    GeneralNominalCenteredHeadMatEffects.BodyHolds plan output.target model body
```

## GeneralDictionaryDefaultRank208

任意の有限coverでStep数は有限事実数以下。checked ground sourceでは一様な有限budgetを構成する。出力部分列列挙は2の出力数乗であり効率性は主張しない。 （主に補助・健全性側。完全性／主型性の完成は主張しない。）

```lean
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal
open GeneralDictionaryDefaultKernel208
open GeneralDictionaryDefaultFinite208
open GeneralNominalCenteredAccessibility (facts)
open GeneralNominalFiniteProgress (remaining)
variable {roles : Roles.RoleDecls} {start state : State roles}
```

### Yulang.GeneralDictionaryDefaultRank208.steps

```lean
theorem steps (trace : Counted registry root start n state) :
    B4Target.Steps (Step registry root) start state
```

### Yulang.GeneralDictionaryDefaultRank208.remaining_le_length

```lean
theorem remaining_le_length (holds : S → F → Prop) (basis : List F) (state : S) :
    remaining holds basis state ≤ basis.length
```

### Yulang.GeneralDictionaryDefaultRank208.budget

```lean
theorem budget (cover : FiniteCover registry root (initial context root))
    (trace : Counted registry root (initial context root) n state) :
    n + remaining Holds (facts cover.signatures cover.sources cover.occurrences) state ≤
      remaining Holds (facts cover.signatures cover.sources cover.occurrences) (initial context root)
```

### Yulang.GeneralDictionaryDefaultRank208.length_bound

```lean
theorem length_bound (cover : FiniteCover registry root (initial context root))
    (trace : Counted registry root (initial context root) n state) :
    n ≤ (facts cover.signatures cover.sources cover.occurrences).length
```

### Yulang.GeneralDictionaryDefaultRank208.selections_length

```lean
theorem selections_length (items : List α) :
    (GeneralDictionaryDefaultCodes208.selections items).length = 2 ^ items.length
```

### Yulang.GeneralDictionaryDefaultRank208.ground_budget

```lean
theorem ground_budget (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
    (ground : GeneralNominalGroundAccessibility.GroundRoots context root rootLabels)
    (coverage : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation) :
    ∃ budget : Nat, ∀ n state, Counted registry root (initial context root) n state → n ≤ budget
```

## GeneralDictionaryDefaultRecorded208

到達可能状態に実際に格納されたplanは全現在classのCommittedを満たす。証拠には同じplanの現在Frameが別途必要で、単なる既存child edgeからは導かない。 （主に補助・健全性側。完全性／主型性の完成は主張しない。）

```lean
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal
open GeneralDictionaryDefaultBoundary208 (boundary)
open GeneralNominalCenteredHeadAllocEncoding (registry)
open GeneralDictionaryDefaultSimulation208 (Recorded)
variable {roles : Roles.RoleDecls} {state : State roles}
```

### Yulang.GeneralDictionaryDefaultRecorded208.recorded

```lean
theorem recorded (reachable : B4TargetV7.Reachable (boundary roles) value root state) :
    Recorded state
```

### Yulang.GeneralDictionaryDefaultRecorded208.committed

```lean
theorem committed (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (member : plan ∈ state.core.plans) :
    GeneralDictionaryDefaultKernel208.Committed state plan
```

### Yulang.GeneralDictionaryDefaultRecorded208.current_class

```lean
theorem current_class (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (member : plan ∈ state.core.plans) (valid : Models state model) :
    GeneralNominalCenteredHeadMatEffects.ClassEffects state.core plan.packet.site.occurrence plan model
```

### Yulang.GeneralDictionaryDefaultRecorded208.certificate

```lean
theorem certificate (checked : (boundary roles).Checked value)
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (frame : GeneralNominalCenteredHeadOutputs.Frame (registry value) state.core focus key plan)
    (member : plan ∈ state.core.plans) (valid : Models state model) :
    GeneralDictionaryTotalEvidence206.Certificate (registry value) state.core model focus key plan.packet.children plan
```

### Yulang.GeneralDictionaryDefaultRecorded208.evidence_node

```lean
theorem evidence_node (checked : (boundary roles).Checked value)
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (frame : GeneralNominalCenteredHeadOutputs.Frame (registry value) state.core focus key plan)
    (member : plan ∈ state.core.plans) (valid : Models state model)
    (given : CommonRoleOutermostResolver.All₂
      (GeneralDictionaryTotalEvidence206.Evidence (registry value) state.core model)
      plan.packet.children dictionaries) :
    GeneralDictionaryTotalEvidence206.Evidence (registry value) state.core model focus (.node key dictionaries)
```

## GeneralDictionaryDefaultRegression208

固定206例で新しい据え付けが可能になり、bottomモデルを除きIntモデルを保つ。 （主に補助・健全性側。完全性／主型性の完成は主張しない。）

```lean
open GeneralDictionaryDefaultGap206Source GeneralDictionaryDefaultGap206Local
open GeneralDictionaryDefaultGap206State
open GeneralNominalCenteredHeadMatStepJournal
```

### Yulang.GeneralDictionaryDefaultRegression208.enabled

```lean
theorem enabled : GeneralDictionaryDefaultKernel208.Installable registry start effect
```

### Yulang.GeneralDictionaryDefaultRegression208.not_committed

```lean
theorem not_committed : ¬ GeneralDictionaryDefaultKernel208.Committed start plan
```

### Yulang.GeneralDictionaryDefaultRegression208.step

```lean
theorem step : GeneralDictionaryDefaultKernel208.Step registry root start after
```

### Yulang.GeneralDictionaryDefaultRegression208.no_longer_stable

```lean
theorem no_longer_stable : ¬ GeneralDictionaryDefaultKernel208.Stable registry start root
```

### Yulang.GeneralDictionaryDefaultRegression208.default_installed

```lean
theorem default_installed : GeneralDictionaryDefaultKernel208.Committed after plan
```

### Yulang.GeneralDictionaryDefaultRegression208.bottom_removed

```lean
theorem bottom_removed : ¬ Models after counter
```

### Yulang.GeneralDictionaryDefaultRegression208.int_retained

```lean
theorem int_retained : Models after model
```

### Yulang.GeneralDictionaryDefaultRegression208.genuine_change

```lean
theorem genuine_change : GeneralNominalCenteredHeadMatStepKernel.Committed start plan ∧
    ¬ GeneralDictionaryDefaultKernel208.Committed start plan ∧
    GeneralDictionaryDefaultKernel208.Step registry root start after ∧
    Models after model ∧ ¬ Models after counter
```

## GeneralDictionaryDefaultSchema208

任意の状態・需要・plan・モデルについて、出どころ付き全出力schemaと旧emitted式＋ClassEffectsの同値。Readyがあれば各本体が存在する。 （主に補助・健全性側。完全性／主型性の完成は主張しない。）

```lean
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralDictionaryAssociatedProvenance
open GeneralNominalCenteredHeadMatEffects
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls}
variable {state : GeneralNominalCenteredSteps.State roles} {root : Occurrence roles}
  {plan : Plan roles} {model : Assignment}
```

### Yulang.GeneralDictionaryDefaultSchema208.mem_entries

```lean
theorem mem_entries : entry ∈ entries state root plan ↔
    ∃ output ∈ GeneralNominalCenteredHeadOutputs.requests state root,
      entry = ⟨output,lookup roles plan.packet.declaration output.name⟩
```

### Yulang.GeneralDictionaryDefaultSchema208.entries_holds_iff

```lean
theorem entries_holds_iff :
    (∀ entry ∈ entries state root plan, entry.Holds plan model) ↔
    ∀ output ∈ GeneralNominalCenteredHeadOutputs.requests state root,
      ∀ body, lookup roles plan.packet.declaration output.name = some body →
        BodyHolds plan output.target model body
```

### Yulang.GeneralDictionaryDefaultSchema208.schema_holds_iff

```lean
theorem schema_holds_iff : SchemaHolds state root plan model ↔
    (GeneralNominalCenteredHeadMatPlans.emittedSchema plan).Holds (variables plan model) model ∧
    ClassEffects state root plan model
```

### Yulang.GeneralDictionaryDefaultSchema208.entry_provenance

```lean
theorem entry_provenance (member : entry ∈ entries state root plan)
    (found : entry.body = some body) :
    Supplies roles plan.packet.declaration entry.output.name body
```

### Yulang.GeneralDictionaryDefaultSchema208.entries_ready

```lean
theorem entries_ready (ready : Ready state root plan)
    (member : entry ∈ entries state root plan) :
    ∃ body, entry.body = some body ∧ (bodySchema plan entry.output.target body).unknown = false
```

### Yulang.GeneralDictionaryDefaultSchema208.alias_entries

```lean
theorem alias_entries (alias : GeneralNominalSaturationState.Alias state.erased.current first.identity last.identity) :
    entry ∈ entries state first plan ↔ entry ∈ entries state last plan
```

## GeneralDictionaryDefaultSemantic208

199の拒否、202のdefault証拠、204のmerged式証拠を新境界へ移す。任意の旧境界EvidenceAtは新境界EvidenceAtへ移せるが、旧全域EvidenceNodeは偽なので仮定しない。 （主に補助・健全性側。完全性／主型性の完成は主張しない。）

```lean
open CommonRoleOutermostResolver
open GeneralDictionaryDefaultBoundary208
open GeneralNominalCenteredHeadAllocV7Cycle199Source
open GeneralNominalCenteredHeadAllocV7Cycle199Fixture
open GeneralDictionaryAllocDefaultSource202
open GeneralDictionaryAllocDefaultCounterexample202
open GeneralDictionaryDefaultEvidence204JoinSource
```

### Yulang.GeneralDictionaryDefaultSemantic208.local_legacy

```lean
theorem local_legacy :
    Local (roles := roles) registry state demand frontier ↔
    B4TargetV7.Local (GeneralDictionaryTotalBoundary206.boundary roles) registry state demand frontier
```

### Yulang.GeneralDictionaryDefaultSemantic208.evidenceAt_legacy

```lean
theorem evidenceAt_legacy
    (given : B4SkeletonV7.EvidenceAt (GeneralDictionaryTotalBoundary206.boundary roles)
      registry state root) :
    B4SkeletonV7.EvidenceAt (boundary roles) registry state root
```

### Yulang.GeneralDictionaryDefaultSemantic208.Rejected199.rejected

```lean
theorem rejected : B4TargetV7.Local (boundary roles) registry start root .rejected
```

### Yulang.GeneralDictionaryDefaultSemantic208.Rejected199.no_selected

```lean
theorem no_selected (key children) :
    ¬ B4TargetV7.Local (boundary roles) registry start root (.selected key children)
```

### Yulang.GeneralDictionaryDefaultSemantic208.Rejected199.evidenceAt

```lean
theorem evidenceAt : B4SkeletonV7.EvidenceAt (boundary roles) registry start root
```

### Yulang.GeneralDictionaryDefaultSemantic208.Default202.selected

```lean
theorem selected : B4TargetV7.Local (boundary roles) registry start root (.selected 37 [])
```

### Yulang.GeneralDictionaryDefaultSemantic208.Default202.evidence_model

```lean
theorem evidence_model (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : (boundary roles).Models start assignment) :
    (boundary roles).Evidence registry start assignment root (.node 37 [])
```

### Yulang.GeneralDictionaryDefaultSemantic208.Default202.evidenceAt

```lean
theorem evidenceAt : B4SkeletonV7.EvidenceAt (boundary roles) registry start root
```

### Yulang.GeneralDictionaryDefaultSemantic208.Merged204.selected

```lean
theorem selected : B4TargetV7.Local (boundary roles) registry start root (.selected 37 [])
```

### Yulang.GeneralDictionaryDefaultSemantic208.Merged204.evidence_model

```lean
theorem evidence_model (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : (boundary roles).Models start assignment) :
    (boundary roles).Evidence registry start assignment root (.node 37 [])
```

### Yulang.GeneralDictionaryDefaultSemantic208.Merged204.evidenceAt

```lean
theorem evidenceAt : B4SkeletonV7.EvidenceAt (boundary roles) registry start root
```

## GeneralDictionaryDefaultSimulation208

registryの許された並べ替えと実際のjournal対応を前提に、全schemaのCommittedと新Stepを双方向に移す。 （主に補助・健全性側。完全性／主型性の完成は主張しない。）

```lean
open GeneralDeclarations GeneralSourceDictionaries GeneralRegistryReordering GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal
open GeneralDictionaryDefaultKernel208
open GeneralNominalCenteredHeadMatPermutationRaw
open GeneralNominalCenteredHeadMatPermutationLedger
open GeneralNominalCenteredHeadMatPermutationAdministrative
open GeneralNominalCenteredHeadMatPermutationInstall
variable {roles : Roles.RoleDecls} {before after first last next : State roles} {root focus : Occurrence roles}
```

### Yulang.GeneralDictionaryDefaultSimulation208.full_committed

```lean
theorem full_committed (recorded : Recorded state) (member : plan ∈ state.core.plans) : Committed state plan
```

### Yulang.GeneralDictionaryDefaultSimulation208.full_committed_related

```lean
theorem full_committed_related (same : Related relation first last)
    (pair : GeneralNominalCenteredHeadMatPermutationPlans.Pair plan other) :
    Committed first plan ↔ Committed last other
```

### Yulang.GeneralDictionaryDefaultSimulation208.corresponds_symm

```lean
theorem corresponds_symm (same : Corresponds first last) : Corresponds last first
```

### Yulang.GeneralDictionaryDefaultSimulation208.packet_at

```lean
theorem packet_at (action : At registry before focus after) (member : packet ∈ before.core.erased.current.packets) :
    packet ∈ after.core.erased.current.packets
```

### Yulang.GeneralDictionaryDefaultSimulation208.edge_at

```lean
theorem edge_at (action : At registry before focus after) (member : edge ∈ before.core.erased.current.edges) :
    edge ∈ after.core.erased.current.edges
```

### Yulang.GeneralDictionaryDefaultSimulation208.recorded_at

```lean
theorem recorded_at (recorded : Recorded before) (action : At registry before focus after) : Recorded after
```

### Yulang.GeneralDictionaryDefaultSimulation208.at_forward

```lean
theorem at_forward (order : Reorders registry otherRegistry) (roleEq : registry.roles = roles)
    (same : Corresponds first last) (action : At registry first focus next) :
    ∃ other, At otherRegistry last focus other ∧ Corresponds next other
```

### Yulang.GeneralDictionaryDefaultSimulation208.step_forward

```lean
theorem step_forward (order : Reorders registry otherRegistry) (roleEq : registry.roles = roles)
    (same : Corresponds first last) (step : Step registry root first next) :
    ∃ other, Step otherRegistry root last other ∧ Corresponds next other
```

### Yulang.GeneralDictionaryDefaultSimulation208.step_backward

```lean
theorem step_backward (order : Reorders registry otherRegistry) (roleEq : registry.roles = roles)
    (same : Corresponds first last) (step : Step otherRegistry root last next) :
    ∃ other, Step registry root first other ∧ Corresponds other next
```

### Yulang.GeneralDictionaryDefaultSimulation208.observations

```lean
theorem observations (same : Corresponds first last) (registry : Registry) (roleEq : registry.roles = roles) (demand frontier) :
    GeneralNominalCenteredHeadMatStepBoundary.Local registry first demand frontier ↔
      GeneralNominalCenteredHeadMatStepBoundary.Local registry last demand frontier
```

### Yulang.GeneralDictionaryDefaultSimulation208.steps_backward

```lean
theorem steps_backward (order : Reorders registry otherRegistry) (roleEq : registry.roles = roles)
    (same : Corresponds first last) (path : B4Target.Steps (Step otherRegistry root) last final) :
    ∃ result, B4Target.Steps (Step registry root) first result ∧ Corresponds result final
```

### Yulang.GeneralDictionaryDefaultSimulation208.halt_reflects

```lean
theorem halt_reflects (order : Reorders registry otherRegistry) (roleEq : registry.roles = roles)
    (same : Corresponds first last) (halted : ∀ next, ¬ Step otherRegistry root last next) :
    ∀ next, ¬ Step registry root first next
```

### Yulang.GeneralDictionaryDefaultSimulation208.packet_free_ledgers

```lean
theorem packet_free_ledgers (path : B4Target.Steps (Step registry root) (initial context root) state)
    (empty : state.core.erased.current.packets = []) : state.core.plans = [] ∧ state.effects = []
```

### Yulang.GeneralDictionaryDefaultSimulation208.packet_free_self

```lean
theorem packet_free_self (path : B4Target.Steps (Step registry root) (initial context root) state)
    (empty : state.core.erased.current.packets = []) : Corresponds state state
```

### Yulang.GeneralDictionaryDefaultSimulation208.packet_free_steps

```lean
theorem packet_free_steps (path : B4Target.Steps (Step registry root) start state)
    (empty : state.core.erased.current.packets = []) (otherRegistry) :
    B4Target.Steps (Step otherRegistry root) start state
```

## GeneralDictionaryDefaultTrace208

初期状態から任意の新Step列について、需要登録・中心対応・実際の据え付け履歴を保つ。 （主に補助・健全性側。完全性／主型性の完成は主張しない。）

```lean
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal
open GeneralDictionaryDefaultKernel208
open GeneralNominalCenteredHeadMatStepHistory (Built)
variable {roles : Roles.RoleDecls} {before after state : State roles}
```

### Yulang.GeneralDictionaryDefaultTrace208.generated_registered

```lean
theorem generated_registered (recorded : Registered state root)
    (generated : GeneralNominalSaturationState.Generated state.core.erased.current root focus) :
    ∃ site ∈ state.core.erased.current.sites, site.occurrence = focus
```

### Yulang.GeneralDictionaryDefaultTrace208.at_registered

```lean
theorem at_registered (recorded : Registered before root) (action : At registry before focus after) : Registered after root
```

### Yulang.GeneralDictionaryDefaultTrace208.registered_trace

```lean
theorem registered_trace (path : B4Target.Steps (Step registry root) (initial context root) state) : Registered state root
```

### Yulang.GeneralDictionaryDefaultTrace208.centered_registered

```lean
theorem centered_registered (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ center ∈ state.core.sites, ∃ raw ∈ state.core.erased.current.sites, raw.occurrence = center.occurrence
```

### Yulang.GeneralDictionaryDefaultTrace208.built_trace

```lean
theorem built_trace (path : B4Target.Steps (Step registry root) (initial context root) state) : Built registry context root state
```

