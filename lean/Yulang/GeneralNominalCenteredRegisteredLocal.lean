import Yulang.GeneralNominalCenteredTerminalAgreement

/-! Reachable registration is exactly generation from the source root.
Outside that set the administrative classifier has only pending and legacy
cycle rejection; literal all-demand agreement has a separate rejection bit. -/
namespace Yulang.GeneralNominalCenteredRegisteredLocal
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralNominalCenteredAdministrativeLocal
open GeneralNominalSaturationState (Generated)
open CommonRoleOutermostResolver (Frontier)

variable {roles : Roles.RoleDecls}

theorem raw_registered_generated
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ site ∈ state.erased.current.sites, Generated state.erased.current root site.occurrence := by
  induction path with
  | refl =>
    intro site member
    cases List.mem_singleton.mp member
    exact .root
  | @tail before after path step ih =>
    obtain ⟨focus,generated,action⟩ := step
    have grow := (GeneralNominalCenteredTrace.at_extends action).journal
    have carry {child} (given : Generated before.erased.current root child) :
        Generated after.erased.current root child :=
      GeneralNominalSaturationSteps.generated_monotone grow given
    cases action with
    | administrative focus after action =>
      cases action with
      | enqueue linked absent =>
        obtain ⟨site,member,same⟩ := GeneralNominalCenteredTrace.generated_registered path generated
        exact False.elim (absent site member same)
      | refresh | equate | reobserve => exact fun site member => carry (ih site member)
    | refresh | merge => exact fun site member => carry (ih site member)
    | install plan support enabled novel guard =>
      intro site member
      rcases List.mem_append.mp member with old | added
      · exact carry (ih site old)
      · obtain ⟨child,present,rfl⟩ := List.mem_map.mp added
        exact .child (carry generated)
          (List.mem_append_right _ (List.mem_map.mpr ⟨child,present,rfl⟩))

theorem registered_iff_generated
    (reachable : B4TargetV5.Reachable (boundary roles) registry root state) :
    Registered state demand ↔ Generated state.erased.current root demand := by
  obtain ⟨start,⟨context,labels,source,point,ground,rfl⟩,path⟩ := reachable
  constructor
  · rintro ⟨site,member,same⟩
    obtain ⟨raw,present,rawSame⟩ := GeneralNominalCenteredTrace.centered_site_registered path site member
    exact (rawSame.trans same) ▸ raw_registered_generated path raw present
  · exact GeneralNominalCenteredTrace.generated_centered path

def LegacyReject (registry : Registry) (state : State roles) (demand : Occurrence roles) : Prop :=
  GeneralNominalFeedbackK2.RootK2 state.erased.current demand ∨
    GeneralNominalFeedbackK2.CandidateK2 registry state.erased.current demand

theorem unregistered_no_root_cycle (absent : ¬ Registered state demand) : ¬ RootCycle state demand :=
  fun ⟨site,member,same,_⟩ => absent ⟨site,member,same⟩

theorem unregistered_no_candidate_cycle (absent : ¬ Registered state demand) :
    ¬ CandidateCycle registry state demand :=
  fun ⟨plan,member,same,_⟩ => absent ⟨plan.input,member,same⟩

theorem unregistered_rejected_iff (absent : ¬ Registered state demand) :
    Local registry state demand .rejected ↔ LegacyReject registry state demand := by
  constructor
  · intro given
    cases given with
    | rejected reason =>
      rcases reason.2 with (old | centered) | (old | centered) | empty
      · exact Or.inl old
      · exact False.elim (unregistered_no_root_cycle absent centered)
      · exact Or.inr old
      · exact False.elim (unregistered_no_candidate_cycle absent centered)
      · exact False.elim (empty.1 (Or.inr (fun ready => absent ready.1)))
  · rintro (root | candidate)
    · exact .rejected ⟨GeneralNominalFeedbackK2.root_ready root,Or.inl (Or.inl root)⟩
    · exact .rejected ⟨GeneralNominalFeedbackK2.candidate_ready candidate,Or.inr (Or.inl (Or.inl candidate))⟩

theorem unregistered_pending_iff (absent : ¬ Registered state demand) :
    Local registry state demand .pending ↔ ¬ LegacyReject registry state demand := by
  constructor
  · intro pending rejected
    have equal := local_functional pending ((unregistered_rejected_iff absent).mpr rejected)
    cases equal
  · intro safe
    classical
    by_cases unknown : GeneralNominalState.RootPending state.erased.current.context.state demand.demand
    · exact .pending unknown
    · refine .inspectionPending unknown (Or.inr (fun ready => absent ready.1)) ?_ ?_
      · rintro (old | centered)
        · exact safe (Or.inl old)
        · exact unregistered_no_root_cycle absent centered
      · rintro (old | centered)
        · exact safe (Or.inr old)
        · exact unregistered_no_candidate_cycle absent centered

theorem unregistered_never_selected (absent : ¬ Registered state demand) :
    ¬ Local registry state demand (.selected key children) :=
  fun selected => absent (selected_ready selected).1

theorem unregistered_never_ambiguous (absent : ¬ Registered state demand) :
    ¬ Local registry state demand .ambiguous := by
  intro given
  cases given with
  | ambiguous safe _ _ _ => exact safe.2.2.2 (Or.inr (fun ready => absent ready.1))

theorem unregistered_local_iff (one : ¬ Registered first demand) (two : ¬ Registered last demand)
    (same : LegacyReject registry first demand ↔ LegacyReject registry last demand) (frontier) :
    Local registry first demand frontier ↔ Local registry last demand frontier := by
  cases frontier with
  | pending => exact (unregistered_pending_iff one).trans ((not_congr same).trans (unregistered_pending_iff two).symm)
  | rejected => exact (unregistered_rejected_iff one).trans (same.trans (unregistered_rejected_iff two).symm)
  | ambiguous => exact iff_of_false (unregistered_never_ambiguous one) (unregistered_never_ambiguous two)
  | selected key children => exact iff_of_false (unregistered_never_selected one) (unregistered_never_selected two)

theorem local_agreement_iff
    (left : B4TargetV5.Reachable (boundary roles) firstRegistry root first)
    (right : B4TargetV5.Reachable (boundary roles) lastRegistry root last) :
    (∀ demand frontier, Local registry first demand frontier ↔ Local registry last demand frontier) ↔
      (∀ demand, Generated first.erased.current root demand ∨ Generated last.erased.current root demand →
        ∀ frontier, Local registry first demand frontier ↔ Local registry last demand frontier) ∧
      (∀ demand, ¬ Generated first.erased.current root demand → ¬ Generated last.erased.current root demand →
        (LegacyReject registry first demand ↔ LegacyReject registry last demand)) := by
  constructor
  · intro agreement
    refine ⟨fun demand _ frontier => agreement demand frontier,?_⟩
    intro demand absentFirst absentLast
    have one := mt (registered_iff_generated left).mp absentFirst
    have two := mt (registered_iff_generated right).mp absentLast
    exact (unregistered_rejected_iff one).symm.trans ((agreement demand .rejected).trans (unregistered_rejected_iff two))
  · rintro ⟨inside,outside⟩ demand frontier
    classical
    by_cases present : Generated first.erased.current root demand ∨ Generated last.erased.current root demand
    · exact inside demand present frontier
    · have one : ¬ Generated first.erased.current root demand := fun h => present (Or.inl h)
      have two : ¬ Generated last.erased.current root demand := fun h => present (Or.inr h)
      exact unregistered_local_iff (mt (registered_iff_generated left).mp one)
        (mt (registered_iff_generated right).mp two) (outside demand one two) frontier


def TerminalGeneratedLocalConfluence (roles : Roles.RoleDecls) : Prop :=
  ∀ first last, (boundary roles).Checked first → (boundary roles).Checked last → (boundary roles).Reorders first last →
    ∀ context (root : Occurrence roles) labels, GeneralNominalSourceFormation.InitialSource first context root →
    (∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2) →
    GeneralNominalGroundAccessibility.GroundRoots context root labels → ∀ left right,
    B4Target.Steps (Step first root) (initial context root) left →
    B4Target.Steps (Step last root) (initial context root) right →
    (∀ next, ¬ Step first root left next) → (∀ next, ¬ Step last root right next) → ∀ demand,
    (Generated left.erased.current root demand ∨ Generated right.erased.current root demand) → ∀ frontier,
    Local last left demand frontier ↔ Local last right demand frontier

end Yulang.GeneralNominalCenteredRegisteredLocal
