import Yulang.GeneralLocalPredicateCongruence
import Yulang.GeneralNominalCenteredGroundComposition

/-! Registration and required merging precede selection. The raw and centered
merge obligations are both explicit; this layer changes no transition. -/
namespace Yulang.GeneralNominalCenteredAdministrativeLocal
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open CommonRoleOutermostResolver
open GeneralNominalCenteredBoundary (vocabulary)

variable {roles : Roles.RoleDecls}

def Registered (state : State roles) (root : Occurrence roles) : Prop :=
  ∃ site ∈ state.sites, site.occurrence = root

def RawMergesClosed (state : State roles) (root : Occurrence roles) : Prop :=
  ∀ site ∈ state.erased.current.sites, site.occurrence = root →
    GeneralNominalFeedbackSteps.MergesClosed state.erased.current site

def CenterMergesClosed (state : State roles) (root : Occurrence roles) : Prop :=
  ∀ first ∈ state.sites, first.occurrence = root → ∀ last ∈ state.sites,
    SameInputs (Models state) first last →
    GeneralNominalSaturationState.Alias state.erased.current first.occurrence.identity last.occurrence.identity

def AdministrativeReady (state : State roles) (root : Occurrence roles) : Prop :=
  Registered state root ∧ RawMergesClosed state root ∧ CenterMergesClosed state root

def fields (roles : Roles.RoleDecls) : GeneralNominalLocalBoundary.Fields (vocabulary roles) :=
  { GeneralNominalCenteredBoundary.fields roles with
    InspectionPending := fun registry state root =>
      (GeneralNominalCenteredBoundary.fields roles).InspectionPending registry state root ∨
        ¬ AdministrativeReady state root }

abbrev Local (registry : Registry) (state : State roles) :=
  GeneralNominalLocalBoundary.Local (fields roles) registry state

theorem local_functional (one : Local registry state root first) (two : Local registry state root last) : first = last :=
  GeneralNominalLocalBoundary.local_functional one two

theorem local_total (registry : Registry) (checked : Checked registry) (state : State roles) (root : Occurrence roles) :
    ∃ frontier, Local registry state root frontier :=
  GeneralNominalLocalBoundary.local_total (fun key first last one two =>
    GeneralNominalRecursiveCandidates.survivor_children_functional registry checked
      state.erased.current.context root key first last one two)

theorem selected_old (selected : Local registry state root (.selected key children)) :
    GeneralNominalCenteredBoundary.Local registry state root (.selected key children) := by
  cases selected with
  | selected safe unique =>
      exact .selected ⟨safe.1,safe.2.1,safe.2.2.1,fun pending => safe.2.2.2 (Or.inl pending)⟩ unique

theorem selected_ready (selected : Local registry state root (.selected key children)) : AdministrativeReady state root := by
  apply Classical.byContradiction
  intro missing
  cases selected with
  | selected safe _ => exact safe.2.2.2 (Or.inr missing)

theorem ready_local_iff (ready : AdministrativeReady state root) (frontier : Frontier (Occurrence roles)) :
    Local registry state root frontier ↔ GeneralNominalCenteredBoundary.Local registry state root frontier := by
  apply GeneralLocalPredicateCongruence.local_iff (first := fields roles)
    (last := GeneralNominalCenteredBoundary.fields roles) Iff.rfl Iff.rfl Iff.rfl ?_ (fun _ _ => Iff.rfl) frontier
  change (_ ∨ ¬ AdministrativeReady state root) ↔ _
  simp only [ready,not_true_eq_false,or_false]

theorem selected_iff : Local registry state root (.selected key children) ↔
    GeneralNominalCenteredBoundary.Local registry state root (.selected key children) ∧ AdministrativeReady state root :=
  ⟨fun selected => ⟨selected_old selected,selected_ready selected⟩,
    fun ⟨old,ready⟩ => (ready_local_iff ready _).mpr old⟩

theorem administrative_pending
    (known : ¬ (fields roles).RootPending registry state root)
    (noRoot : ¬ (fields roles).RootK2 registry state root)
    (noCandidate : ¬ (fields roles).CandidateK2 registry state root)
    (missing : ¬ AdministrativeReady state root) : Local registry state root .pending :=
  .inspectionPending known (Or.inr missing) noRoot noCandidate

theorem root_cycle_rejected (known : ¬ (fields roles).RootPending registry state root)
    (cycle : RootCycle state root) : Local registry state root .rejected :=
  .rejected ⟨known,Or.inl (Or.inr cycle)⟩

theorem inspected_cycle_rejected (known : ¬ (fields roles).RootPending registry state root)
    (cycle : CandidateCycle registry state root) : Local registry state root .rejected :=
  .rejected ⟨known,Or.inr (Or.inl (Or.inr cycle))⟩

theorem required_merge_not_ready (first last : Site roles)
    (one : first ∈ state.sites) (two : last ∈ state.sites)
    (same : SameInputs (Models state) first last)
    (novel : ¬ GeneralNominalSaturationState.Alias state.erased.current first.occurrence.identity last.occurrence.identity) :
    ¬ AdministrativeReady state first.occurrence :=
  fun ready => novel (ready.2.2 first one rfl last two same)

theorem initial_ready (context : GeneralNominalCandidates.Context) (root : Occurrence roles) :
    AdministrativeReady (initial context root) root := by
  refine ⟨⟨rootSite context.state.seed root,List.mem_singleton_self _,rfl⟩,?_,?_⟩
  · intro site member same other present inputs
    have first : site = GeneralNominalDemandMerging.pointSite root := List.mem_singleton.mp member
    have last : other = GeneralNominalDemandMerging.pointSite root := List.mem_singleton.mp present
    rw [first,last]
    exact .refl _
  · intro first member same last present inputs
    have one : first = rootSite context.state.seed root := List.mem_singleton.mp member
    have two : last = rootSite context.state.seed root := List.mem_singleton.mp present
    rw [one,two]
    exact .refl _

theorem initial_local_iff (registry : Registry) (context : GeneralNominalCandidates.Context)
    (root : Occurrence roles) (frontier) :
    Local registry (initial context root) root frontier ↔
      GeneralNominalCenteredBoundary.Local registry (initial context root) root frontier :=
  ready_local_iff (initial_ready context root) frontier

/-- The frozen merge rule still asks for a raw support certificate. This law
names that operational obligation separately from required merge closure. -/
def CenterMergeSupported (state : State roles) (root : Occurrence roles) : Prop :=
  ∀ first ∈ state.sites, first.occurrence = root → ∀ last ∈ state.sites,
    SameInputs (Models state) first last →
    ∃ support, GeneralNominalSupportChoices.MergeGuard state.erased first.observed last.observed support

theorem stable_center_merges_closed (stable : Stable registry state root)
    (supported : CenterMergeSupported state root) : CenterMergesClosed state root := by
  intro first one same last two inputs
  apply Classical.byContradiction
  intro novel
  obtain ⟨support,guard⟩ := supported first one same last two inputs
  exact stable first.occurrence (same ▸ GeneralNominalSaturationState.Generated.root) _
    (.merge first last support one two inputs novel guard)

def boundary (roles : Roles.RoleDecls) : B4TargetV5.SourceBoundary (vocabulary roles) where
  toSourceBoundary := GeneralNominalLocalBoundary.complete (fields roles) (GeneralNominalCenteredBoundary.remaining roles)
  Initial := (GeneralNominalCenteredGroundBoundary.groundBoundary roles).Initial

theorem reachable_iff : B4TargetV5.Reachable (boundary roles) registry root state ↔
    B4TargetV5.Reachable (GeneralNominalCenteredGroundBoundary.groundBoundary roles) registry root state := Iff.rfl

theorem local_correspondence (registry : Registry) (state : State roles) (root : Occurrence roles) (frontier) :
    B4TargetV3.Local (boundary roles).toSourceBoundary registry state root frontier ↔ Local registry state root frontier :=
  (GeneralNominalLocalBoundary.local_extension (GeneralNominalCenteredBoundary.remaining roles) frontier).symm

noncomputable def frontiers (roles : Roles.RoleDecls) : B4SkeletonV5.Frontiers (vocabulary roles) := by
  classical
  exact fun registry state =>
    { frontier := fun root => if checked : Checked registry then Classical.choose (local_total registry checked state root) else .pending
      Local := B4TargetV3.Local (boundary roles).toSourceBoundary registry state }

theorem frontierLocal (registry : Registry) (checked : (boundary roles).Checked registry)
    (state : State roles) (root : Occurrence roles) (_reachable : B4TargetV5.Reachable (boundary roles) registry root state)
    (demand : Occurrence roles) (frontier) :
    (frontiers roles registry state).frontier demand = frontier ↔
      B4TargetV3.Local (boundary roles).toSourceBoundary registry state demand frontier := by
  classical
  have valid := Classical.choose_spec (local_total registry checked.2 state demand)
  change (if checked : Checked registry then Classical.choose (local_total registry checked state demand) else .pending) = frontier ↔ _
  rw [dite_eq_left checked.2]
  constructor
  · intro same
    exact (local_correspondence registry state demand frontier).mpr (same ▸ valid)
  · intro given
    exact local_functional valid ((local_correspondence registry state demand frontier).mp given)

theorem localIdentity (registry : Registry) (state : State roles) (root : Occurrence roles)
    (_reachable : B4TargetV5.Reachable (boundary roles) registry root state) :
    (frontiers roles registry state).Local = B4TargetV3.Local (boundary roles).toSourceBoundary registry state := rfl

end Yulang.GeneralNominalCenteredAdministrativeLocal
