import Yulang.GeneralDictionarySemanticCompletion
import Yulang.GeneralNominalReobservationBoundary

/-! Dictionary soundness for packet-free reachable states of the additive
point-reobservation boundary. This is not the general nonempty-journal bridge. -/
namespace Yulang.GeneralDictionaryReobservationEvidence
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralDictionaryRecursiveEvidence
open GeneralDictionarySemanticCompletion
variable {roles : Roles.RoleDecls}

/-- Empty final packet lists exclude every prior installation. Reobservation
preserves journal shape, even when its nominal descriptors genuinely change. -/
theorem trace_packetFree_shape (registry : Registry) (root : Occurrence roles)
    (context : GeneralNominalCandidates.Context) (state : State roles)
    (path : B4Target.Steps (GeneralNominalReobservationSteps.Step registry root)
      (initial context root) state) (empty : state.packets = []) :
    state.sites = [GeneralNominalDemandMerging.pointSite root] ∧ state.edges = [] := by
  induction path with
  | refl => exact ⟨rfl,rfl⟩
  | @tail before after path step ih =>
    obtain ⟨focus,generated,action⟩ := step
    cases action with
    | reobserve => exact ih empty
    | ordinary action =>
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

theorem reachable_packetFree_shape (registry : Registry) (root : Occurrence roles)
    (state : State roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalReobservationBoundary.boundary roles)
      registry root state) (empty : state.packets = []) :
    state.sites = [GeneralNominalDemandMerging.pointSite root] ∧ state.edges = [] := by
  obtain ⟨start,⟨context,source,rfl⟩,path⟩ := reachable
  exact trace_packetFree_shape registry root context state path empty

/-- No old-boundary reachability or fixed-view premise is required. -/
theorem reachable_packetFree_joint (registry : Registry) (root focus : Occurrence roles)
    (state : State roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalReobservationBoundary.boundary roles)
      registry root state) (empty : state.packets = [])
    (reached : focus = root ∨ Generated state root focus)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalFeedbackK2.Local registry state focus (.selected key children)) :
    GeneralNominalJointCandidates.Joint registry state focus key := by
  have shape := reachable_packetFree_shape registry root state reachable empty
  have sites : ∀ site ∈ state.sites, site.occurrence = root := by
    intro site member
    rw [shape.1] at member
    have eq := List.mem_singleton.mp member
    subst site
    rfl
  have same : focus = root := reached.elim id (generated_eq_root state root focus shape.2 sites)
  subst focus
  apply packetFree_selected_joint registry state root key children empty
  · intro site member
    rw [shape.1] at member
    have eq := List.mem_singleton.mp member
    subst site
    rfl
  · intro site related
    exact sites site related.1
  · exact selected

theorem reachable_packetFree_terminal (registry : Registry) (root focus : Occurrence roles)
    (state : State roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalReobservationBoundary.boundary roles)
      registry root state) (empty : state.packets = [])
    (reached : focus = root ∨ Generated state root focus)
    (key : Nat) (children : List (Occurrence roles))
    (stable : GeneralNominalReobservationSteps.Stable registry state focus)
    (selected : GeneralNominalFeedbackK2.Local registry state focus (.selected key children)) :
    children = [] ∧ ∀ model, Models state model →
      Evidence registry state.context model focus (.node key []) := by
  have joint := reachable_packetFree_joint registry root focus state reachable empty reached key children selected
  have oldStable := ((GeneralNominalReobservationSteps.stable_iff registry state focus).mp stable).1
  obtain ⟨packet,reg,ctx,site,id,kids,enabled,committed⟩ :=
    GeneralDictionaryFeedbackEvidence.stable_joint_packet registry state focus key children oldStable selected joint
  have edges := (reachable_packetFree_shape registry root state reachable empty).2
  have nil : children = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro child member
    have edge := committed.2 child (by simpa only [kids] using member)
    rw [edges] at edge
    cases edge
  rw [nil] at selected
  exact ⟨nil,fun model valid => GeneralDictionaryFeedbackEvidence.stable_joint_evidence
    registry state focus key [] oldStable selected joint model valid [] .nil⟩

/-- The exact payload node uses one common final model for all children. -/
theorem reachable_packetFree_evidence (registry : Registry) (root focus : Occurrence roles)
    (state : State roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalReobservationBoundary.boundary roles)
      registry root state) (empty : state.packets = [])
    (reached : focus = root ∨ Generated state root focus)
    (key : Nat) (children : List (Occurrence roles))
    (stable : GeneralNominalReobservationSteps.Stable registry state focus)
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

/-- This finds a packet somewhere, not necessarily one recording this focus. -/
theorem nonterminal_has_packet (registry : Registry) (root focus : Occurrence roles)
    (state : State roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalReobservationBoundary.boundary roles)
      registry root state) (reached : focus = root ∨ Generated state root focus)
    (key : Nat) (children : List (Occurrence roles))
    (stable : GeneralNominalReobservationSteps.Stable registry state focus)
    (selected : GeneralNominalFeedbackK2.Local registry state focus (.selected key children))
    (nonterminal : children ≠ []) : ∃ packet, packet ∈ state.packets := by
  cases empty : state.packets with
  | nil => exact False.elim (nonterminal (reachable_packetFree_terminal registry root focus
      state reachable empty reached key children stable selected).1)
  | cons packet rest => exact ⟨packet,by simp⟩

end Yulang.GeneralDictionaryReobservationEvidence
