import Yulang.GeneralDictionarySettledProjection
import Yulang.GeneralDictionaryValueEvidence
import Yulang.GeneralDictionarySupportEvidence

/-! Current-context Evidence for the actual I26 guarded relation. Selected
support supplies both captured-value and settled explanations. Stability is
used only against genuinely guarded installs; old Value stability is never
inferred. General nonempty-journal results retain the explicit Joint premise;
packet-free reachable roots discharge Joint using the existing source theorem. -/
namespace Yulang.GeneralDictionarySettledEvidence
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport
open GeneralDictionaryRecursiveEvidence
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
variable {roles : Roles.RoleDecls}

private theorem selected_old {registry : Registry} {state : Tracked roles} {root : Occurrence roles}
    (selected : GeneralNominalSettledBoundary.Local registry state root (.selected key children)) :
    GeneralNominalFeedbackK2.Local registry state.current root (.selected key children) := by
  have projected := GeneralDictionarySettledProjection.selected_local_old
    ((GeneralNominalSettledBoundary.local_correspondence registry state root _).mpr selected)
  exact GeneralNominalValueBoundary.selected_old
    ((GeneralNominalValueBoundary.local_correspondence registry state root _).mp projected)

theorem stable_committed {registry : Registry} {state : Tracked roles} {root : Occurrence roles}
    (stable : GeneralNominalSettledSteps.Stable registry state root) (packet : Packet roles)
    (generated : Generated state.current root packet.site.occurrence)
    (enabled : GeneralNominalFeedbackSteps.Installable registry state.current packet)
    (support : List (Occurrence roles)) (guard : GeneralNominalSettledSupport.PacketGuard state packet support) :
    GeneralNominalFeedbackSteps.Committed state.current packet := by
  classical
  exact Classical.byContradiction (fun novel =>
    stable packet.site.occurrence generated _ (.install packet support enabled novel guard))

theorem stable_site (registry : Registry) (state : Tracked roles) (root : Occurrence roles)
    (stable : GeneralNominalSettledSteps.Stable registry state root)
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
    (selected : GeneralNominalSettledBoundary.Local registry state root (.selected key children)) :
    ∃ support, GeneralNominalValueSupport.DecisionGuard registry state root support := by
  classical
  apply Classical.byContradiction
  intro missing
  cases selected with
  | selected safe unique => exact safe.2.2.2 (Or.inl (Or.inr missing))

/-- Explicit support construction; the remaining general obligations are Joint
and recovered merge closure, not evidence assumed as a premise. -/
theorem stable_joint_packet (registry : Registry) (state : Tracked roles)
    (root : Occurrence roles) (key : Nat) (children : List (Occurrence roles))
    (stable : GeneralNominalSettledSteps.Stable registry state root)
    (selected : GeneralNominalSettledBoundary.Local registry state root (.selected key children))
    (joint : GeneralNominalJointCandidates.Joint registry state.current root key)
    (merges : ∀ site ∈ state.current.sites, site.occurrence = root →
      GeneralNominalFeedbackSteps.MergesClosed state.current site) :
    ∃ packet : Packet roles, packet.registry = registry ∧ packet.context = state.current.context ∧
      packet.site.occurrence = root ∧ packet.declaration.id = key ∧ packet.children = children ∧
      GeneralNominalFeedbackSteps.Installable registry state.current packet ∧
      GeneralNominalFeedbackSteps.Committed state.current packet := by
  have old := selected_old selected
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
  have guard : GeneralNominalValueSteps.PacketGuard state packet support := by
    refine ⟨?_,decision.2⟩
    change Guard state site.occurrence declaration bounds support ∧
      DecisionGuard state registry site.occurrence support
    rw [same]
    exact ⟨⟨decision.1.1,decision.1.2.1,
      decision.1.2.2 declaration visible role bounds located⟩,decision.1⟩
  refine ⟨packet,rfl,rfl,same,identity,kids,enabled,
    stable_committed stable packet (same ▸ Generated.root) enabled support ⟨guard,?_⟩⟩
  change GeneralNominalSettledSupport.DecisionGuard registry state site.occurrence
  rw [same]
  apply Classical.byContradiction
  intro blocked
  cases selected with
  | selected safe _ => exact safe.2.2.2 (Or.inr blocked)

theorem stable_joint_instance (registry : Registry) (state : Tracked roles)
    (root : Occurrence roles) (key : Nat) (children : List (Occurrence roles))
    (stable : GeneralNominalSettledSteps.Stable registry state root)
    (selected : GeneralNominalSettledBoundary.Local registry state root (.selected key children))
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
    (stable : GeneralNominalSettledSteps.Stable registry state root)
    (selected : GeneralNominalSettledBoundary.Local registry state root (.selected key children))
    (joint : GeneralNominalJointCandidates.Joint registry state.current root key)
    (merges : ∀ site ∈ state.current.sites, site.occurrence = root →
      GeneralNominalFeedbackSteps.MergesClosed state.current site)
    (model : Assignment) (valid : Models state.current model) (dictionaries : List Payload)
    (given : CommonRoleOutermostResolver.All₂
      (Evidence registry state.current.context model) children dictionaries) :
    Evidence registry state.current.context model root (.node key dictionaries) :=
  evidence_node registry state.current.context model root key children dictionaries
    ((stable_joint_instance registry state root key children stable selected joint merges).1 model valid) given

theorem stable_merges_of_exact (registry : Registry) (state : Tracked roles) (root : Occurrence roles)
    (exact : GeneralNominalSupportSteps.Exact state)
    (stable : GeneralNominalSettledSteps.Stable registry state root)
    (first last : GeneralNominalDemandMerging.Site roles)
    (one : first ∈ state.current.sites) (two : last ∈ state.current.sites)
    (reached : Generated state.current root first.occurrence)
    (same : GeneralNominalFeedbackSites.SameInputs state.current first last) :
    Alias state.current first.occurrence.identity last.occurrence.identity := by
  classical
  by_cases done : Alias state.current first.occurrence.identity last.occurrence.identity
  · exact done
  · exact False.elim (stable first.occurrence reached _
      (.merge first last _ one two same done (GeneralDictionarySupportEvidence.merge_guard_of_exact state exact first last same)))

/-- Source formation discharges the merge side condition. Joint is the only
remaining applicability premise; no old feedback stability is assumed. -/
theorem reachable_joint_instance (registry : Registry) (state : Tracked roles)
    (root focus : Occurrence roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalSettledBoundary.boundary roles) registry root state)
    (key : Nat) (children : List (Occurrence roles))
    (stable : GeneralNominalSettledSteps.Stable registry state focus)
    (selected : GeneralNominalSettledBoundary.Local registry state focus (.selected key children))
    (joint : GeneralNominalJointCandidates.Joint registry state.current focus key) :
    (∀ model, Models state.current model → Instance registry state.current.context model focus key children) ∧
      ∀ child ∈ children, Generated state.current focus child := by
  have exact := GeneralNominalSettledSteps.formed_exact
    (GeneralNominalSettledBoundary.reachable_formed reachable)
  apply stable_joint_instance registry state focus key children stable selected joint
  intro site member same other present inputs
  exact stable_merges_of_exact registry state focus exact stable site other member present
    (same ▸ Generated.root) inputs

theorem reachable_joint_evidence (registry : Registry) (state : Tracked roles)
    (root focus : Occurrence roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalSettledBoundary.boundary roles) registry root state)
    (key : Nat) (children : List (Occurrence roles))
    (stable : GeneralNominalSettledSteps.Stable registry state focus)
    (selected : GeneralNominalSettledBoundary.Local registry state focus (.selected key children))
    (joint : GeneralNominalJointCandidates.Joint registry state.current focus key)
    (model : Assignment) (valid : Models state.current model) (dictionaries : List Payload)
    (given : CommonRoleOutermostResolver.All₂ (Evidence registry state.current.context model) children dictionaries) :
    Evidence registry state.current.context model focus (.node key dictionaries) :=
  evidence_node registry state.current.context model focus key children dictionaries
    ((reachable_joint_instance registry state root focus reachable key children stable selected joint).1 model valid) given


/-- Actual settled transitions erase to actual reobservation transitions.
No reverse simulation or stability transfer is asserted. -/
theorem steps_reobservation (registry : Registry) (root : Occurrence roles)
    (before after : Tracked roles)
    (path : B4Target.Steps (GeneralNominalSettledSteps.Step registry root) before after) :
    B4Target.Steps (GeneralNominalReobservationSteps.Step registry root)
      before.current after.current := by
  induction path with
  | refl => exact .refl
  | tail prior update ih =>
    exact .tail ih (GeneralNominalSupportSteps.step_old
      (GeneralNominalDownstreamSteps.step_old (GeneralNominalValueSteps.step_old (GeneralNominalSettledSteps.step_old update))))

theorem reachable_reobservation (registry : Registry) (root : Occurrence roles)
    (state : Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalSettledBoundary.boundary roles) registry root state) :
    B4TargetV5.Reachable (GeneralNominalReobservationBoundary.boundary roles)
      registry root state.current := by
  obtain ⟨start,⟨context,source,rfl⟩,path⟩ := reachable
  exact ⟨initial context root,⟨context,source,rfl⟩,steps_reobservation registry root _ _ path⟩

/-- At reachable packet-free settled-stable states, selected roots or generated
focuses are terminal and sound in every final model, with no Joint premise.
This does not cover nonempty journals. -/
theorem reachable_packetFree_terminal (registry : Registry) (root focus : Occurrence roles)
    (state : Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalSettledBoundary.boundary roles) registry root state)
    (empty : state.current.packets = [])
    (reached : focus = root ∨ Generated state.current root focus)
    (key : Nat) (children : List (Occurrence roles))
    (stable : GeneralNominalSettledSteps.Stable registry state focus)
    (selected : GeneralNominalSettledBoundary.Local registry state focus (.selected key children)) :
    children = [] ∧ ∀ model, Models state.current model →
      Evidence registry state.current.context model focus (.node key []) := by
  have oldReachable := reachable_reobservation registry root state reachable
  have shape := GeneralDictionaryReobservationEvidence.reachable_packetFree_shape
    registry root state.current oldReachable empty
  have joint := GeneralDictionaryReobservationEvidence.reachable_packetFree_joint
    registry root focus state.current oldReachable empty reached key children
    (selected_old selected)
  have exact := GeneralNominalSettledSteps.formed_exact
    (GeneralNominalSettledBoundary.reachable_formed reachable)
  have merges : ∀ site ∈ state.current.sites, site.occurrence = focus →
      GeneralNominalFeedbackSteps.MergesClosed state.current site := by
    intro site member same other present inputs
    exact stable_merges_of_exact registry state focus exact stable site other member present
      (same ▸ Generated.root) inputs
  obtain ⟨packet,reg,ctx,site,id,kids,enabled,committed⟩ :=
    stable_joint_packet registry state focus key children stable selected joint merges
  have nil : children = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro child member
    have edge := committed.2 child (by simpa only [kids] using member)
    rw [shape.2] at edge
    cases edge
  refine ⟨nil,?_⟩
  intro model valid
  have rule := (reachable_joint_instance registry state root focus reachable key children
    stable selected joint).1 model valid
  rw [nil] at rule
  exact evidence_node registry state.current.context model focus key [] [] rule .nil

/-- The packet-free specialization matches the node evidence shape exactly,
including child payload alignment in the same final model. -/
theorem reachable_packetFree_evidence (registry : Registry) (root focus : Occurrence roles)
    (state : Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalSettledBoundary.boundary roles) registry root state)
    (empty : state.current.packets = [])
    (reached : focus = root ∨ Generated state.current root focus)
    (key : Nat) (children : List (Occurrence roles))
    (stable : GeneralNominalSettledSteps.Stable registry state focus)
    (selected : GeneralNominalSettledBoundary.Local registry state focus (.selected key children))
    (model : Assignment) (valid : Models state.current model) (dictionaries : List Payload)
    (given : CommonRoleOutermostResolver.All₂
      (Evidence registry state.current.context model) children dictionaries) :
    Evidence registry state.current.context model focus (.node key dictionaries) := by
  have terminal := reachable_packetFree_terminal registry root focus state reachable empty
    reached key children stable selected
  rw [terminal.1] at given
  cases given
  exact terminal.2 model valid

end Yulang.GeneralDictionarySettledEvidence
