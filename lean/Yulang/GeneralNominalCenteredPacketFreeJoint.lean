import Yulang.GeneralNominalCenteredRegistryJournal
import Yulang.GeneralNominalCenteredCompletionParts

/-! Before the first installation, arbitrary reachable observation revisions
leave a singleton demand journal. Every selected frame then has Joint. -/
namespace Yulang.GeneralNominalCenteredPacketFreeJoint
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralNominalCenteredAdministrativeLocal GeneralNominalCenteredSelectedCompletion
open GeneralNominalCenteredCompletionParts

variable {roles : Roles.RoleDecls}

def Shape (state : State roles) (root : Occurrence roles) (seed : Nat) : Prop :=
  state.sites = [rootSite seed root] ∧ state.plans = [] ∧
    state.erased.current.sites = [GeneralNominalDemandMerging.pointSite root] ∧
    state.erased.current.edges = [] ∧ state.erased.current.aliases = []

theorem packet_free_trace
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (empty : state.erased.current.packets = []) : Shape state root context.state.seed := by
  induction path with
  | refl => exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  | @tail before after path step ih =>
    obtain ⟨focus,generated,action⟩ := step
    have prior : before.erased.current.packets = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro packet member
      have recorded := GeneralNominalCenteredRegistryJournal.packet_at action member
      rw [empty] at recorded
      cases recorded
    have shape := ih prior
    cases action with
    | administrative focus after action =>
      cases action with
      | enqueue linked absent =>
        obtain ⟨site,member,same⟩ := GeneralNominalCenteredTrace.generated_registered path generated
        exact False.elim (absent site member same)
      | refresh | equate | reobserve => exact shape
    | refresh => exact shape
    | install => cases empty
    | merge first last support one two same novel guard =>
      rw [shape.1] at one two
      have firstEq := List.mem_singleton.mp one
      have lastEq := List.mem_singleton.mp two
      subst first; subst last
      exact False.elim (novel (.refl _))

theorem raw_initial (shape : Shape state root seed)
    (empty : state.erased.current.packets = []) :
    state.erased.current = GeneralNominalSaturationState.initial state.erased.current.context root := by
  have sites := shape.2.2.1
  have edges := shape.2.2.2.1
  have aliases := shape.2.2.2.2
  cases same : state.erased.current with
  | mk context packets rawSites rawEdges rawAliases =>
    rw [same] at empty sites edges aliases
    cases empty; cases sites; cases edges; cases aliases
    rfl

theorem packet_free_reachable
    (reachable : B4TargetV5.Reachable (boundary roles) registry root state)
    (empty : state.erased.current.packets = []) :
    state.erased.current = GeneralNominalSaturationState.initial state.erased.current.context root := by
  obtain ⟨start,⟨context,labels,source,point,ground,rfl⟩,path⟩ := reachable
  exact raw_initial (packet_free_trace path empty) empty

theorem packet_free_generated
    (reachable : B4TargetV5.Reachable (boundary roles) registry root state)
    (empty : state.erased.current.packets = [])
    (generated : GeneralNominalSaturationState.Generated state.erased.current root focus) : focus = root := by
  obtain ⟨start,⟨context,labels,source,point,ground,rfl⟩,path⟩ := reachable
  obtain ⟨site,member,same⟩ := GeneralNominalCenteredTrace.generated_registered path generated
  rw [(packet_free_trace path empty).2.2.1] at member
  have equal := List.mem_singleton.mp member
  exact same.symm.trans (congrArg GeneralNominalDemandMerging.Site.occurrence equal)

theorem frame_joint_of_packet_free
    (reachable : B4TargetV5.Reachable (boundary roles) registry root state)
    (empty : state.erased.current.packets = [])
    (frame : Frame registry state focus key children plan) :
    GeneralNominalJointCandidates.Joint registry state.erased.current focus key := by
  have raw := packet_free_reachable reachable empty
  have member := frame.raw_recorded
  rw [raw] at member
  have siteEq := List.mem_singleton.mp member
  have focusEq : focus = root :=
    frame.occurrence_eq.symm.trans (congrArg GeneralNominalDemandMerging.Site.occurrence siteEq)
  subst focus
  rcases plan with ⟨⟨preg,pctx,site,declaration,checked,bounds⟩,input,inputEq⟩
  have reg : preg = registry := frame.registry_eq
  have ctx : pctx = state.erased.current.context := frame.context_eq
  subst preg; subst pctx
  obtain ⟨model,holds⟩ := frame_branch frame
  have branch : GeneralNominalRecursiveCandidates.BranchModels registry state.erased.current.context root
      declaration checked bounds model := by
    have same : site.occurrence = root := frame.occurrence_eq
    exact same ▸ holds
  have joint := GeneralNominalJointCandidates.initial_joint registry state.erased.current.context root
    declaration frame.visible checked frame.role_eq bounds frame.located frame.prepared model branch
  have keyed := frame.key_eq ▸ joint
  rw [raw]
  exact keyed

theorem selected_joint_of_packet_free
    (reachable : B4TargetV5.Reachable (boundary roles) registry root state)
    (empty : state.erased.current.packets = [])
    (generated : GeneralNominalSaturationState.Generated state.erased.current root focus)
    (selected : Local registry state focus (.selected key children)) :
    GeneralNominalJointCandidates.Joint registry state.erased.current focus key := by
  obtain ⟨plan,frame⟩ := selected_frame reachable generated selected
  exact frame_joint_of_packet_free reachable empty frame

end Yulang.GeneralNominalCenteredPacketFreeJoint
