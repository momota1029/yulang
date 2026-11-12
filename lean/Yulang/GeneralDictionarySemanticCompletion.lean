import Yulang.GeneralDictionaryReachableEvidenceRecorded
import Yulang.GeneralDictionaryReachableBoundary

/-! Semantic completion without a recorded-focus premise. Context completeness
is an explicit residual and is not claimed for all reachable journals. For an
empty packet journal of point sites it is proved structurally below. -/
namespace Yulang.GeneralDictionarySemanticCompletion
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalRecursiveCandidates GeneralDictionaryRecursiveEvidence
open GeneralNominalJointCandidates (Joint BranchAt Related)
variable {roles : Roles.RoleDecls}

/-- A current survivor has a branch model, regardless of packet coverage. -/
theorem survivor_branch (registry : Registry) (state : State roles)
    (focus : Occurrence roles) (key : Nat) (children : List (Occurrence roles))
    (survivor : Survivor registry state.context focus key children) :
    ∃ model, GeneralNominalState.Models state.context.state model ∧
      BranchAt registry state focus key model := by
  obtain ⟨_,declaration,visible,checked,identity,role,bounds,located,prepared,_⟩ := survivor
  obtain ⟨stored,storedLocated,finished,ready,model,branch⟩ := prepared.2.2.2
  have same : stored = bounds := Option.some.inj (storedLocated.symm.trans located)
  subst stored
  exact ⟨model,(branch_interval_sound _ _ _ _ _ _ _ branch).1,
    declaration,visible,checked,identity,role,prepared,bounds,located,branch⟩

/-- Completeness and current packet semantics replace the requirement that the
focus itself be recorded. Exact-occurrence aliases are still explicit. -/
theorem selected_joint (registry : Registry) (state : State roles)
    (focus : Occurrence roles) (key : Nat) (children : List (Occurrence roles))
    (complete : ContextComplete state)
    (current : GeneralDictionaryCurrentJournal.Current registry state)
    (packetClass : ∀ prior ∈ state.packets,
      Alias state focus.identity prior.site.occurrence.identity → prior.site.occurrence = focus)
    (siteClass : ∀ site, Related state focus site → site.occurrence = focus)
    (selected : GeneralNominalFeedbackK2.Local registry state focus (.selected key children)) :
    Joint registry state focus key := by
  have survivor : Survivor registry state.context focus key children := by
    cases selected with | selected _ unique => exact unique.1
  obtain ⟨model,raw,branch⟩ := survivor_branch registry state focus key children survivor
  have valid := complete model raw
  refine ⟨?_,model,valid,branch,?_⟩
  · intro packet member alias
    have rule := current packet member model valid
    rw [packetClass packet member alias] at rule
    exact (GeneralDictionarySelectedInstanceCoherence.instance_selected registry state focus model
      packet.declaration.id key packet.children children rule selected).1
  · intro site related
    rw [siteClass site related]
    exact branch

/-- Pure point sites impose no obligations beyond their own source intervals. -/
theorem packetFree_complete (state : State roles) (empty : state.packets = [])
    (points : ∀ site ∈ state.sites, site = GeneralNominalDemandMerging.pointSite site.occurrence) :
    ContextComplete state := by
  intro model raw
  refine ⟨raw,?_,?_⟩
  · intro packet member
    rw [empty] at member
    cases member
  · intro site member
    rw [points site member]
    exact point_holds site.occurrence model

/-- Empty packet lists supply current semantics vacuously, not Evidence. -/
theorem packetFree_current (registry : Registry) (state : State roles)
    (empty : state.packets = []) : GeneralDictionaryCurrentJournal.Current registry state := by
  intro packet member
  rw [empty] at member
  cases member

/-- Unrecorded semantic completion works in arbitrary point-site journals,
not just the initial one-site state. Aliases must still preserve occurrences. -/
theorem packetFree_selected_joint (registry : Registry) (state : State roles)
    (focus : Occurrence roles) (key : Nat) (children : List (Occurrence roles))
    (empty : state.packets = [])
    (points : ∀ site ∈ state.sites, site = GeneralNominalDemandMerging.pointSite site.occurrence)
    (siteClass : ∀ site, Related state focus site → site.occurrence = focus)
    (selected : GeneralNominalFeedbackK2.Local registry state focus (.selected key children)) :
    Joint registry state focus key := by
  apply selected_joint registry state focus key children (packetFree_complete state empty points)
    (packetFree_current registry state empty) _ siteClass selected
  intro packet member
  rw [empty] at member
  cases member

/-- Stability then forces the actual current branch in every journal model. -/
theorem packetFree_stable_instance (registry : Registry) (state : State roles)
    (focus : Occurrence roles) (key : Nat) (children : List (Occurrence roles))
    (empty : state.packets = [])
    (points : ∀ site ∈ state.sites, site = GeneralNominalDemandMerging.pointSite site.occurrence)
    (siteClass : ∀ site, Related state focus site → site.occurrence = focus)
    (stable : GeneralNominalFeedbackSteps.Stable registry state focus)
    (selected : GeneralNominalFeedbackK2.Local registry state focus (.selected key children)) :
    (∀ model, Models state model → Instance registry state.context model focus key children) ∧
      ∀ child ∈ children, Generated state focus child :=
  GeneralDictionaryFeedbackEvidence.stable_joint_instance registry state focus key children stable selected
    (packetFree_selected_joint registry state focus key children empty points siteClass selected)

/-- With no edges and a singleton occurrence class, generation cannot leave the root. -/
theorem generated_eq_root (state : State roles) (root focus : Occurrence roles)
    (edges : state.edges = [])
    (sites : ∀ site ∈ state.sites, site.occurrence = root)
    (generated : Generated state root focus) : focus = root := by
  induction generated with
  | root => rfl
  | child _ member _ => rw [edges] at member; cases member
  | alias _ _ member _ _ => exact sites _ member

/-- A source-formed state with no installed packets still has precisely its
initial point site and no child edge. This quantifies over the full feedback
relation, including arbitrary certified view-changing refreshes. -/
theorem packetFree_shape (registry : Registry) (root : Occurrence roles)
    (state : State roles) (formed : GeneralNominalFeedbackSteps.SourceFormed registry root state)
    (empty : state.packets = []) :
    state.sites = [GeneralNominalDemandMerging.pointSite root] ∧ state.edges = [] := by
  induction formed with
  | initial context source => exact ⟨rfl,rfl⟩
  | @update before after formed step ih =>
    obtain ⟨focus,generated,action⟩ := step
    cases action with
    | enqueue focus linked absent =>
      have old := ih empty
      have same := generated_eq_root before root focus old.2 (by
        intro site member
        rw [old.1] at member
        have eq := List.mem_singleton.mp member
        subst site
        rfl) generated
      exact False.elim (absent (GeneralNominalDemandMerging.pointSite root)
        (by rw [old.1]; exact List.mem_singleton_self _) same.symm)
    | install packet enabled novel =>
      change packet :: before.packets = [] at empty
      cases empty
    | merge => exact ih empty
    | refresh => exact ih empty
    | equate => exact ih empty

/-- Complete semantic applicability for any stable selected packet-free reachable
root. No context-completeness, record-coverage, alias, or fixed-view premise. -/
theorem sourceFormed_packetFree_joint (registry : Registry) (root : Occurrence roles)
    (state : State roles) (formed : GeneralNominalFeedbackSteps.SourceFormed registry root state)
    (empty : state.packets = []) (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalFeedbackK2.Local registry state root (.selected key children)) :
    Joint registry state root key := by
  have shape := packetFree_shape registry root state formed empty
  apply packetFree_selected_joint registry state root key children empty
  · intro site member
    rw [shape.1] at member
    have same := List.mem_singleton.mp member
    subst site
    rfl
  · intro site related
    change site ∈ state.sites ∧ _ at related
    rw [shape.1] at related
    have same := List.mem_singleton.mp related.1
    subst site
    rfl
  · exact selected

/-- In the empty-packet reachable case, stable selected roots are terminal and
have the same dictionary in every final model. The no-packet restriction remains. -/
theorem sourceFormed_packetFree_terminal (registry : Registry) (root : Occurrence roles)
    (state : State roles) (formed : GeneralNominalFeedbackSteps.SourceFormed registry root state)
    (empty : state.packets = []) (key : Nat) (children : List (Occurrence roles))
    (stable : GeneralNominalFeedbackSteps.Stable registry state root)
    (selected : GeneralNominalFeedbackK2.Local registry state root (.selected key children)) :
    children = [] ∧ ∀ model, Models state model →
      Evidence registry state.context model root (.node key []) := by
  have joint := sourceFormed_packetFree_joint registry root state formed empty key children selected
  obtain ⟨packet,reg,ctx,site,id,kids,enabled,committed⟩ :=
    GeneralDictionaryFeedbackEvidence.stable_joint_packet registry state root key children stable selected joint
  have edgeEmpty := (packetFree_shape registry root state formed empty).2
  have nil : children = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro child member
    have edge := committed.2 child (by simpa only [kids] using member)
    rw [edgeEmpty] at edge
    cases edge
  rw [nil] at selected
  exact ⟨nil,fun model valid => GeneralDictionaryFeedbackEvidence.stable_joint_evidence
    registry state root key [] stable selected joint model valid [] .nil⟩

/-- The packet-free case covers every reachable generated focus, not only the
root: such a focus must equal the root because no installation emitted an edge. -/
theorem reachable_packetFree_terminal (registry : Registry) (root focus : Occurrence roles)
    (state : State roles)
    (reachable : B4TargetV5.Reachable (GeneralDictionaryReachableBoundary.boundary roles)
      registry root state)
    (empty : state.packets = []) (reached : focus = root ∨ Generated state root focus)
    (key : Nat) (children : List (Occurrence roles))
    (stable : GeneralNominalFeedbackSteps.Stable registry state focus)
    (selected : GeneralNominalFeedbackK2.Local registry state focus (.selected key children)) :
    children = [] ∧ ∀ model, Models state model →
      Evidence registry state.context model focus (.node key []) := by
  have formed := (GeneralDictionaryReachableBoundary.reachable_iff_sourceFormed
    registry root state).mp reachable
  have shape := packetFree_shape registry root state formed empty
  have same : focus = root := by
    rcases reached with same | generated
    · exact same
    · apply generated_eq_root state root focus shape.2 _ generated
      intro site member
      rw [shape.1] at member
      have eq := List.mem_singleton.mp member
      subst site
      rfl
  subst focus
  exact sourceFormed_packetFree_terminal registry root state formed empty key children stable selected

/-- Any nonterminal stable selected reachable focus has at least one packet
somewhere in its journal. This does not assert that the focus itself is recorded. -/
theorem nonterminal_has_packet (registry : Registry) (root focus : Occurrence roles)
    (state : State roles)
    (reachable : B4TargetV5.Reachable (GeneralDictionaryReachableBoundary.boundary roles)
      registry root state)
    (reached : focus = root ∨ Generated state root focus)
    (key : Nat) (children : List (Occurrence roles))
    (stable : GeneralNominalFeedbackSteps.Stable registry state focus)
    (selected : GeneralNominalFeedbackK2.Local registry state focus (.selected key children))
    (nonterminal : children ≠ []) : ∃ packet, packet ∈ state.packets := by
  cases empty : state.packets with
  | nil => exact False.elim (nonterminal (reachable_packetFree_terminal registry root focus
      state reachable empty reached key children stable selected).1)
  | cons packet rest => exact ⟨packet,by simp⟩

/-- Exact parent evidence for the packet-free reachable part of the V5 bridge;
child dictionaries use the same final model. General nonempty journals remain open. -/
theorem reachable_packetFree_evidence (registry : Registry) (root focus : Occurrence roles)
    (state : State roles)
    (reachable : B4TargetV5.Reachable (GeneralDictionaryReachableBoundary.boundary roles)
      registry root state)
    (empty : state.packets = []) (reached : focus = root ∨ Generated state root focus)
    (key : Nat) (children : List (Occurrence roles))
    (stable : GeneralNominalFeedbackSteps.Stable registry state focus)
    (selected : GeneralNominalFeedbackK2.Local registry state focus (.selected key children))
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model)
    (dictionaries : List GeneralDictionaryReadback.Payload)
    (given : CommonRoleOutermostResolver.All₂
      (Evidence registry state.context model) children dictionaries) :
    Evidence registry state.context model focus (.node key dictionaries) := by
  have terminal := reachable_packetFree_terminal registry root focus state reachable empty
    reached key children stable selected
  rw [terminal.1] at given
  cases given
  exact terminal.2 model valid

end Yulang.GeneralDictionarySemanticCompletion
