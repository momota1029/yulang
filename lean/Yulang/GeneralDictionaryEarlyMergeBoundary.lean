import Yulang.GeneralDictionaryEarlyMergeChoices
import Yulang.GeneralDictionarySupportEvidence

/-! Reachable packet-free states cannot merge. A first source-supported install
can, however, be followed by an actual early merge when it emits a distinct,
same-input child. The construction derives provenance guards and coherence;
it does not assume a post-state invariant or assert an instantiated example. -/
namespace Yulang.GeneralDictionaryEarlyMergeBoundary
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalSupportSteps
open GeneralDictionaryEarlyMergeChoices
variable {roles : Roles.RoleDecls}

/-- A raw two-site empty journal is not a reachable merge example. -/
theorem packetFree_no_merge (registry : Registry) (root : Occurrence roles)
    (state : Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root state)
    (empty : state.current.packets = [])
    (first last : GeneralNominalDemandMerging.Site roles)
    (one : first ∈ state.current.sites) (two : last ∈ state.current.sites) :
    Alias state.current first.occurrence.identity last.occurrence.identity := by
  have shape := (GeneralDictionarySupportEvidence.reachable_packetFree_shape registry root state reachable empty).1
  rw [shape] at one two
  have a := List.mem_singleton.mp one
  have b := List.mem_singleton.mp two
  subst first; subst last
  exact .refl _

private theorem empty_alias {state : State roles} (empty : state.aliases = [])
    {first last : Nat} (related : Alias state first last) : first = last := by
  induction related with
  | refl => rfl
  | edge member => rw [empty] at member; cases member
  | symm _ ih => exact ih.symm
  | trans _ _ one two => exact one.trans two

/-- Parametric actual construction. The input premises describe one legal
initial installation and two present, same-input sites; the new child's class
is proved uncommitted. No merge support certificate is assumed. -/
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
    let before := GeneralNominalSupportSteps.install (GeneralNominalSupport.initial context root) packet support
    let first := GeneralNominalFeedbackSites.childSite packet child
    let after := GeneralNominalSupportSteps.merge before first last
      (GeneralNominalSupportChoices.dependencyPool before)
    Scheduled registry root after ∧
    Step registry root before after ∧
    after.current.packets ≠ [] ∧ after.current.aliases ≠ [] := by
  dsimp only
  let before := GeneralNominalSupportSteps.install (GeneralNominalSupport.initial context root) packet support
  let first := GeneralNominalFeedbackSites.childSite packet child
  have path : Scheduled registry root before :=
    .install (.initial context source) packet support (atRoot ▸ Generated.root) enabled novel guard
  have generated : Generated before.current root child := by
    apply Generated.child .root
    change (root,child) ∈ [] ++ packet.children.map (fun c => (packet.site.occurrence,c))
    simp only [List.nil_append]
    exact List.mem_map.mpr ⟨child,emitted,by rw [atRoot]⟩
  have firstMem : first ∈ before.current.sites := by
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨child,emitted,rfl⟩
  have early : Early before.current first last := by
    apply Or.inl
    intro prior member related
    have eq : prior = packet := List.mem_singleton.mp member
    subst prior
    have equal := empty_alias (state := before.current) rfl related
    exact freshId (equal.trans (congrArg Occurrence.identity atRoot))
  have distinct : ¬ Alias before.current first.occurrence.identity last.occurrence.identity :=
    fun related => different (empty_alias rfl related)
  have mergeGuard := GeneralDictionarySupportEvidence.merge_guard_of_exact before
    (formed_exact (scheduled_formed registry root before path)) first last same
  refine ⟨Scheduled.merge path first last _ generated firstMem present same distinct mergeGuard early,
    ⟨child,generated,.merge first last _ firstMem present same distinct mergeGuard⟩,?_,?_⟩
  · simp [GeneralNominalSupportSteps.merge,GeneralNominalSaturationState.merge,
      GeneralNominalSupportSteps.install,GeneralNominalFeedbackSites.install]
  · simp [GeneralNominalSupportSteps.merge,GeneralNominalSaturationState.merge]

end Yulang.GeneralDictionaryEarlyMergeBoundary
