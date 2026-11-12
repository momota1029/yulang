import Yulang.GeneralNominalSupportBoundary
import Yulang.GeneralDictionaryReobservationEvidence

/-! Dictionary soundness for the actual provenance-aware support boundary.
Support-stability is weaker than old feedback stability: we construct the
support guard explicitly rather than assuming the old transition is enabled.
The low-level packet lemma retains Joint and recovered-merge closure. Exactness
discharges merge closure for all reachable states; packet-free reachability also
discharges Joint. No general Joint or V5 EvidenceNode claim is made. -/
namespace Yulang.GeneralDictionarySupportEvidence
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport
open GeneralDictionaryRecursiveEvidence
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
variable {roles : Roles.RoleDecls}

theorem steps_old (registry : Registry) (root : Occurrence roles)
    (before after : Tracked roles)
    (path : B4Target.Steps (GeneralNominalSupportSteps.Step registry root) before after) :
    B4Target.Steps (GeneralNominalReobservationSteps.Step registry root) before.current after.current := by
  induction path with
  | refl => exact .refl
  | tail prior update ih => exact .tail ih (GeneralNominalSupportSteps.step_old update)

theorem reachable_old (registry : Registry) (root : Occurrence roles) (state : Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root state) :
    B4TargetV5.Reachable (GeneralNominalReobservationBoundary.boundary roles) registry root state.current := by
  obtain ⟨start,⟨context,source,rfl⟩,path⟩ := reachable
  exact ⟨initial context root,⟨context,source,rfl⟩,steps_old registry root _ _ path⟩

theorem stable_site (registry : Registry) (state : Tracked roles) (root : Occurrence roles)
    (stable : GeneralNominalSupportSteps.Stable registry state root)
    (linked : GeneralNominalState.Linked state.current.context.state root.demand) :
    ∃ site ∈ state.current.sites, site.occurrence = root := by
  classical
  apply Classical.byContradiction
  intro missing
  have absent : ∀ site ∈ state.current.sites, site.occurrence ≠ root := by
    intro site member same
    exact missing ⟨site,member,same⟩
  exact stable root .root _ (.administrative root _ (.enqueue root linked absent))

theorem selected_support (registry : Registry) (state : Tracked roles) (root : Occurrence roles)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalSupportBoundary.Local registry state root (.selected key children)) :
    ∃ support, DecisionGuard state registry root support := by
  classical
  apply Classical.byContradiction
  intro missing
  cases selected with
  | selected safe unique => exact safe.2.2.2 (Or.inr missing)

/-- Explicit support construction; the remaining general obligations are Joint
and recovered merge closure, not evidence assumed as a premise. -/
theorem stable_joint_packet (registry : Registry) (state : Tracked roles)
    (root : Occurrence roles) (key : Nat) (children : List (Occurrence roles))
    (stable : GeneralNominalSupportSteps.Stable registry state root)
    (selected : GeneralNominalSupportBoundary.Local registry state root (.selected key children))
    (joint : GeneralNominalJointCandidates.Joint registry state.current root key)
    (merges : ∀ site ∈ state.current.sites, site.occurrence = root →
      GeneralNominalFeedbackSteps.MergesClosed state.current site) :
    ∃ packet : Packet roles, packet.registry = registry ∧ packet.context = state.current.context ∧
      packet.site.occurrence = root ∧ packet.declaration.id = key ∧ packet.children = children ∧
      GeneralNominalFeedbackSteps.Installable registry state.current packet ∧
      GeneralNominalFeedbackSteps.Committed state.current packet := by
  have old := GeneralNominalSupportBoundary.selected_old selected
  obtain ⟨model,valid,branch,_⟩ := joint.2
  obtain ⟨declaration,visible,checked,identity,role,prepared,bounds,located,holds⟩ := branch
  obtain ⟨site,member,same⟩ := stable_site registry state root stable prepared.2.1
  let packet : Packet roles := ⟨registry,state.current.context,site,declaration,checked,bounds⟩
  have survivor : GeneralNominalRecursiveCandidates.Survivor registry state.current.context root key packet.children := by
    refine ⟨?_,declaration,visible,checked,identity,role,bounds,located,prepared,?_⟩
    · cases old with | selected safe _ => exact safe.1
    · change GeneralNominalAllocation.children state.current.context.state registry site.occurrence declaration checked _ = _
      rw [same]
      rfl
  have kids : packet.children = children := by
    cases old with | selected _ unique => exact (unique.2 key packet.children survivor).2
  have localRule : GeneralNominalFeedbackK2.Local registry state.current site.occurrence
      (.selected declaration.id packet.children) := by
    rw [same,identity,kids]; exact old
  have closed := merges site member same
  have enabled : GeneralNominalFeedbackSteps.Installable registry state.current packet := by
    refine ⟨⟨rfl,rfl,member,visible,?_,?_,?_,?_,?_,?_,?_,?_⟩,localRule,closed⟩
    · simpa only [packet,same] using role
    · simpa only [packet,same] using located
    · simpa only [packet,same] using prepared
    · exact GeneralNominalFeedbackK2.selected_legacy localRule
    · intro prior present alias
      apply identity.trans
      apply Eq.symm
      apply joint.1 prior present
      simpa only [packet,same] using alias
    · intro other present inputs
      exact closed other present (GeneralDictionaryFeedbackEvidence.sameInputs_recovered state.current site other inputs)
    · refine ⟨model,valid,?_⟩
      simpa only [Packet.Holds,packet,same] using holds
    · simpa only [packet,same,identity] using joint
  obtain ⟨support,decision⟩ := selected_support registry state root key children selected
  have guard : GeneralNominalSupportSteps.PacketGuard state packet support := by
    change Guard state site.occurrence declaration bounds support ∧
      DecisionGuard state registry site.occurrence support
    rw [same]
    exact ⟨⟨decision.1,decision.2.1,decision.2.2 declaration visible role bounds located⟩,decision⟩
  exact ⟨packet,rfl,rfl,same,identity,kids,enabled,
    GeneralNominalSupportSteps.stable_committed stable packet (same ▸ Generated.root) enabled support guard⟩

theorem stable_joint_instance (registry : Registry) (state : Tracked roles)
    (root : Occurrence roles) (key : Nat) (children : List (Occurrence roles))
    (stable : GeneralNominalSupportSteps.Stable registry state root)
    (selected : GeneralNominalSupportBoundary.Local registry state root (.selected key children))
    (joint : GeneralNominalJointCandidates.Joint registry state.current root key)
    (merges : ∀ site ∈ state.current.sites, site.occurrence = root →
      GeneralNominalFeedbackSteps.MergesClosed state.current site) :
    (∀ model, Models state.current model → Instance registry state.current.context model root key children) ∧
      ∀ child ∈ children, Generated state.current root child := by
  obtain ⟨packet,reg,ctx,focus,id,kids,enabled,committed⟩ :=
    stable_joint_packet registry state root key children stable selected joint merges
  constructor
  · intro model valid
    have rule := GeneralDictionaryCommittedEvidence.committed_instance state.current packet
      (by simpa only [reg] using enabled.1.2.2.2.1)
      enabled.1.2.2.2.2.1 enabled.1.2.2.2.2.2.1 enabled.1.2.2.2.2.2.2.1 committed model valid
    simpa only [reg,ctx,focus,id,kids] using rule
  · intro child member
    have reached := GeneralDictionaryCommittedEvidence.committed_children state.current packet committed child
      (by simpa only [kids] using member)
    simpa only [focus] using reached

theorem stable_joint_evidence (registry : Registry) (state : Tracked roles)
    (root : Occurrence roles) (key : Nat) (children : List (Occurrence roles))
    (stable : GeneralNominalSupportSteps.Stable registry state root)
    (selected : GeneralNominalSupportBoundary.Local registry state root (.selected key children))
    (joint : GeneralNominalJointCandidates.Joint registry state.current root key)
    (merges : ∀ site ∈ state.current.sites, site.occurrence = root →
      GeneralNominalFeedbackSteps.MergesClosed state.current site)
    (model : Assignment) (valid : Models state.current model) (dictionaries : List Payload)
    (given : CommonRoleOutermostResolver.All₂
      (Evidence registry state.current.context model) children dictionaries) :
    Evidence registry state.current.context model root (.node key dictionaries) :=
  evidence_node registry state.current.context model root key children dictionaries
    ((stable_joint_instance registry state root key children stable selected joint merges).1 model valid) given

/-- Erasing provenance maps actual reachable states into the existing
reobservation semantics, but does not map support stability to old stability. -/
theorem reachable_packetFree_shape (registry : Registry) (root : Occurrence roles)
    (state : Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root state)
    (empty : state.current.packets = []) :
    state.current.sites = [GeneralNominalDemandMerging.pointSite root] ∧ state.current.edges = [] :=
  GeneralDictionaryReobservationEvidence.reachable_packetFree_shape registry root state.current
    (reachable_old registry root state reachable) empty

theorem reachable_packetFree_joint (registry : Registry) (root focus : Occurrence roles)
    (state : Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root state)
    (empty : state.current.packets = []) (reached : focus = root ∨ Generated state.current root focus)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalSupportBoundary.Local registry state focus (.selected key children)) :
    GeneralNominalJointCandidates.Joint registry state.current focus key :=
  GeneralDictionaryReobservationEvidence.reachable_packetFree_joint registry root focus state.current
    (reachable_old registry root state reachable) empty reached key children
    (GeneralNominalSupportBoundary.selected_old selected)

/-- For reachable packet-free states, neither Joint nor merge closure is an
extra premise. Support guards follow from the actual selected judgment. -/
theorem reachable_packetFree_terminal (registry : Registry) (root focus : Occurrence roles)
    (state : Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root state)
    (empty : state.current.packets = []) (reached : focus = root ∨ Generated state.current root focus)
    (key : Nat) (children : List (Occurrence roles))
    (stable : GeneralNominalSupportSteps.Stable registry state focus)
    (selected : GeneralNominalSupportBoundary.Local registry state focus (.selected key children)) :
    children = [] ∧ ∀ model, Models state.current model →
      Evidence registry state.current.context model focus (.node key []) := by
  have shape := reachable_packetFree_shape registry root state reachable empty
  have sites : ∀ site ∈ state.current.sites, site.occurrence = root := by
    intro site member
    rw [shape.1] at member
    have eq := List.mem_singleton.mp member
    subst site; rfl
  have same : focus = root := reached.elim id
    (GeneralDictionarySemanticCompletion.generated_eq_root state.current root focus shape.2 sites)
  subst focus
  have joint := reachable_packetFree_joint registry root root state reachable empty (Or.inl rfl) key children selected
  have merges : ∀ site ∈ state.current.sites, site.occurrence = root →
      GeneralNominalFeedbackSteps.MergesClosed state.current site := by
    intro site member same other present inputs
    have equal := sites other present
    rw [same,equal]
    exact .refl _
  have combined := stable_joint_instance registry state root key children stable selected joint merges
  have nil : children = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro child member
    obtain ⟨packet,_,_,site,_,kids,_,committed⟩ :=
      stable_joint_packet registry state root key children stable selected joint merges
    have edge := committed.2 child (by simpa only [kids] using member)
    rw [shape.2] at edge
    cases edge
  refine ⟨nil,?_⟩
  intro model valid
  have rule := combined.1 model valid
  rw [nil] at rule
  exact evidence_node registry state.current.context model root key [] [] rule .nil

theorem reachable_packetFree_evidence (registry : Registry) (root focus : Occurrence roles)
    (state : Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root state)
    (empty : state.current.packets = []) (reached : focus = root ∨ Generated state.current root focus)
    (key : Nat) (children : List (Occurrence roles))
    (stable : GeneralNominalSupportSteps.Stable registry state focus)
    (selected : GeneralNominalSupportBoundary.Local registry state focus (.selected key children))
    (model : Assignment) (valid : Models state.current model) (dictionaries : List Payload)
    (given : CommonRoleOutermostResolver.All₂
      (Evidence registry state.current.context model) children dictionaries) :
    Evidence registry state.current.context model focus (.node key dictionaries) := by
  have terminal := reachable_packetFree_terminal registry root focus state reachable empty reached key children stable selected
  rw [terminal.1] at given
  cases given
  exact terminal.2 model valid

theorem nonterminal_has_packet (registry : Registry) (root focus : Occurrence roles)
    (state : Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root state)
    (reached : focus = root ∨ Generated state.current root focus) (key : Nat) (children : List (Occurrence roles))
    (stable : GeneralNominalSupportSteps.Stable registry state focus)
    (selected : GeneralNominalSupportBoundary.Local registry state focus (.selected key children))
    (nonterminal : children ≠ []) : ∃ packet, packet ∈ state.current.packets := by
  cases empty : state.current.packets with
  | nil => exact False.elim (nonterminal (reachable_packetFree_terminal registry root focus state
      reachable empty reached key children stable selected).1)
  | cons packet rest => exact ⟨packet,by simp⟩


/-- Taking every dependency recovers the exact semantic ledger. No cycle
admissibility is needed for the existing MergeGuard definition. -/
theorem slice_pool (state : Tracked roles) (model : Assignment) :
    Slice state (GeneralNominalSupportChoices.dependencyPool state) model ↔ AllModels state model := by
  constructor
  · intro valid
    refine ⟨valid.1,?_⟩
    intro fact member
    exact valid.2 fact member (fun producer dependency => List.mem_flatMap.mpr ⟨fact,member,dependency⟩)
  · intro valid
    exact ⟨valid.1,fun fact member _ => valid.2 fact member⟩

theorem related_known (models : Assignment → Prop) (first last : List (Option GeneralNominalRecursiveInspection.Origin))
    (same : GeneralNominalDemandMerging.All₂ (GeneralNominalDemandMerging.Related models) first last) :
    (∀ input ∈ first, input ≠ none) ∧ (∀ input ∈ last, input ≠ none) := by
  induction same with
  | nil => simp
  | cons related rest ih =>
    obtain ⟨a,b,rfl,rfl,_⟩ := related
    constructor
    · intro input member
      rcases List.mem_cons.mp member with rfl | member
      · simp
      · exact ih.1 input member
    · intro input member
      rcases List.mem_cons.mp member with rfl | member
      · simp
      · exact ih.2 input member

theorem recovered_endpoint (state : State roles) (site : GeneralNominalDemandMerging.Site roles)
    (known : ∀ input ∈ (GeneralNominalFeedbackSites.recover state site).inputs, input ≠ none)
    (index : Fin (roles site.occurrence.demand.role).arity)
    (absent : site.inputs[index.val]? = some none) :
    GeneralNominalFeedbackSites.EndpointEqual state (site.occurrence.demand.arguments index) := by
  classical
  have bound : index.val < site.inputs.length := by rw [site.arity]; exact index.isLt
  have old : site.inputs[index.val] = none := by
    rw [List.getElem?_eq_getElem bound] at absent
    exact Option.some.inj absent
  have member : GeneralNominalFeedbackSites.recoverOrigin state site index ∈
      (GeneralNominalFeedbackSites.recover state site).inputs := List.mem_ofFn.mpr ⟨index,rfl⟩
  have present := known _ member
  by_cases yes : GeneralNominalFeedbackSites.EndpointEqual state (site.occurrence.demand.arguments index)
  · exact yes
  · exact False.elim (present (by simp [GeneralNominalFeedbackSites.recoverOrigin,old,yes]))

theorem merge_guard_of_exact (state : Tracked roles) (exact : GeneralNominalSupportSteps.Exact state)
    (first last : GeneralNominalDemandMerging.Site roles)
    (same : GeneralNominalFeedbackSites.SameInputs state.current first last) :
    GeneralNominalSupportChoices.MergeGuard state first last (GeneralNominalSupportChoices.dependencyPool state) := by
  have models : Slice state (GeneralNominalSupportChoices.dependencyPool state) = Models state.current :=
    funext (fun model => propext ((slice_pool state model).trans (exact model).symm))
  have known := related_known (Models state.current) _ _ same.2
  refine ⟨?_,?_,?_⟩
  · rw [models]; exact same
  · intro index absent model valid
    exact recovered_endpoint state.current first known.1 index absent model (models ▸ valid)
  · intro index absent model valid
    exact recovered_endpoint state.current last known.2 index absent model (models ▸ valid)

theorem stable_merges_of_exact (registry : Registry) (state : Tracked roles) (root : Occurrence roles)
    (exact : GeneralNominalSupportSteps.Exact state)
    (stable : GeneralNominalSupportSteps.Stable registry state root)
    (first last : GeneralNominalDemandMerging.Site roles)
    (one : first ∈ state.current.sites) (two : last ∈ state.current.sites)
    (reached : Generated state.current root first.occurrence)
    (same : GeneralNominalFeedbackSites.SameInputs state.current first last) :
    Alias state.current first.occurrence.identity last.occurrence.identity := by
  classical
  by_cases done : Alias state.current first.occurrence.identity last.occurrence.identity
  · exact done
  · exact False.elim (stable first.occurrence reached _
      (.merge first last _ one two same done (merge_guard_of_exact state exact first last same)))

/-- Source formation discharges the merge side condition. Joint is the only
remaining applicability premise; no old feedback stability is assumed. -/
theorem reachable_joint_instance (registry : Registry) (state : Tracked roles)
    (root focus : Occurrence roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root state)
    (key : Nat) (children : List (Occurrence roles))
    (stable : GeneralNominalSupportSteps.Stable registry state focus)
    (selected : GeneralNominalSupportBoundary.Local registry state focus (.selected key children))
    (joint : GeneralNominalJointCandidates.Joint registry state.current focus key) :
    (∀ model, Models state.current model → Instance registry state.current.context model focus key children) ∧
      ∀ child ∈ children, Generated state.current focus child := by
  have exact := GeneralNominalSupportSteps.formed_exact
    (GeneralNominalSupportBoundary.reachable_formed registry state root reachable)
  apply stable_joint_instance registry state focus key children stable selected joint
  intro site member same other present inputs
  exact stable_merges_of_exact registry state focus exact stable site other member present
    (same ▸ Generated.root) inputs

theorem reachable_joint_evidence (registry : Registry) (state : Tracked roles)
    (root focus : Occurrence roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root state)
    (key : Nat) (children : List (Occurrence roles))
    (stable : GeneralNominalSupportSteps.Stable registry state focus)
    (selected : GeneralNominalSupportBoundary.Local registry state focus (.selected key children))
    (joint : GeneralNominalJointCandidates.Joint registry state.current focus key)
    (model : Assignment) (valid : Models state.current model) (dictionaries : List Payload)
    (given : CommonRoleOutermostResolver.All₂ (Evidence registry state.current.context model) children dictionaries) :
    Evidence registry state.current.context model focus (.node key dictionaries) :=
  evidence_node registry state.current.context model focus key children dictionaries
    ((reachable_joint_instance registry state root focus reachable key children stable selected joint).1 model valid) given

end Yulang.GeneralDictionarySupportEvidence
