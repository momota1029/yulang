import Yulang.GeneralNominalFeedbackAdministrative
import Yulang.GeneralNominalReobservationSteps

/-! Administrative accessibility including certified descriptor replacement.
Point facts are indexed by source identity: refresh may change the finite slot
table, but cannot reset these facts. No installation bound is assumed here. -/
namespace Yulang.GeneralNominalReobservationOrder

open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalReobservationSteps
open GeneralNominalAdministrativeProgress (support)

variable {roles : Roles.RoleDecls} {registry : Registry}
variable {before after state : State roles} {focus : Occurrence roles}
noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

def Point (state : State roles) (source : Nat) : Prop :=
  ∃ slot, state.context.state.base.source slot = source ∧ PointAt state.context.state slot

theorem point_sources (point : Point state source) :
    source ∈ GeneralNominalState.sources state.context.state := by
  obtain ⟨slot,same,_⟩ := point
  exact List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_ofFn.mpr ⟨slot,same⟩)))

theorem point_refines (refines : GeneralNominalRefinements.Refines before.context.state after.context.state)
    (point : Point before source) : Point after source := by
  obtain ⟨slot,same,descriptor,recorded,point⟩ := point
  refine ⟨refines.base.embed slot,(refines.base.source slot).trans same,
    GeneralNominalRefinements.renameDescriptor refines.base.embed descriptor,
    refines.nominals slot descriptor recorded,?_⟩
  intro parameter member
  change parameter ∈ descriptor.arguments.map _ at member
  obtain ⟨old,present,equal⟩ := List.mem_map.mp member
  subst parameter
  have equal := point old present
  cases old <;> exact congrArg refines.base.embed equal

theorem point_at (update : At registry before focus after) (point : Point before source) : Point after source := by
  cases update with
  | reobserve revision _ improved =>
    obtain ⟨slot,same,point⟩ := point
    exact ⟨slot,same,improved.1 slot point⟩
  | ordinary action =>
    cases action with
    | enqueue => exact point
    | merge => exact point
    | equate => exact point
    | refresh _ _ certificate _ _ _ _ => exact point_refines certificate.refines point
    | install packet enabled _ =>
      have refinement := GeneralNominalRefinements.installed packet.registry packet.context
        packet.site.occurrence packet.declaration packet.bounds
      conv at refinement => lhs; rw [enabled.1.2.1]
      exact point_refines refinement point

inductive Update (registry : Registry) (before : State roles) : State roles → Prop
  | ordinary {after : State roles} : GeneralNominalFeedbackAdministrative.Update registry before after → Update registry before after
  | reobserve (revision : Revision before) : Certified revision → Improves revision → Update registry before revision.result

theorem as_update (update : Update registry before after) : ∃ focus, At registry before focus after := by
  cases update with
  | ordinary action =>
    obtain ⟨focus,action⟩ := GeneralNominalFeedbackAdministrative.as_update action
    exact ⟨focus,.ordinary focus action⟩
  | reobserve revision certificate improved =>
    -- An administrative update does not inspect its focus.
    let focus : Occurrence roles := ⟨0,⟨0,fun _ => (0,0),[],by intro output member; cases member⟩⟩
    exact ⟨focus,.reobserve focus revision certificate improved⟩

abbrev Fact (roles : Roles.RoleDecls) := GeneralNominalFeedbackProgress.Fact roles ⊕ Nat

def Holds (state : State roles) : Fact roles → Prop
  | .inl fact => GeneralNominalFeedbackProgress.Holds state fact
  | .inr source => Point state source

def facts (state : State roles) : List (Fact roles) :=
  (GeneralNominalFeedbackAdministrative.facts state).map Sum.inl ++ (support state).map Sum.inr

theorem monotone (update : At registry before focus after) (fact : Fact roles) : Holds before fact → Holds after fact := by
  cases fact with
  | inl fact => exact GeneralNominalFeedbackProgress.monotone (at_extends update) fact
  | inr source => exact point_at update

theorem supported_update (start before after : State roles)
    (sites : before.sites = start.sites)
    (sources : GeneralNominalState.sources before.context.state ⊆ support start)
    (update : Update registry before after) :
    after.sites = start.sites ∧ GeneralNominalState.sources after.context.state ⊆ support start ∧
      ∃ fact ∈ facts start, ¬ Holds before fact ∧ Holds after fact := by
  cases update with
  | ordinary action =>
    obtain ⟨newSites,newSources,fact,member,old,now⟩ :=
      GeneralNominalFeedbackAdministrative.supported_update start before after sites sources action
    exact ⟨newSites,newSources,.inl fact,
      List.mem_append_left _ (List.mem_map.mpr ⟨fact,member,rfl⟩),old,now⟩
  | reobserve revision certificate improved =>
    obtain ⟨slot,old,now⟩ := improved.2
    refine ⟨sites,sources,.inr (before.context.state.base.source slot),?_,?_,slot,rfl,now⟩
    · apply List.mem_append_right
      apply List.mem_map.mpr
      refine ⟨_,sources ?_,rfl⟩
      exact List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_ofFn.mpr ⟨slot,rfl⟩)))
    · rintro ⟨other,same,point⟩
      have equal := before.context.state.base.source_injective same
      exact old (equal ▸ point)

noncomputable def remaining (basis : List (Fact roles)) (state : State roles) : Nat := by
  classical
  exact basis.foldr (fun fact count => if Holds state fact then count else count+1) 0

private theorem remaining_cons (fact : Fact roles) (rest : List (Fact roles)) (state : State roles) :
    remaining (fact :: rest) state = if Holds state fact then remaining rest state else remaining rest state+1 := by
  classical
  rfl

theorem remaining_monotone (basis : List (Fact roles)) (update : At registry before focus after) :
    remaining basis after ≤ remaining basis before := by
  classical
  induction basis with
  | nil => exact Nat.le_refl _
  | cons fact rest ih =>
    rw [remaining_cons,remaining_cons]
    by_cases old : Holds before fact
    · have now := monotone update fact old
      simp only [ite_eq_left old,ite_eq_left now]; exact ih
    · by_cases now : Holds after fact <;> simp [now,old] <;> omega

theorem remaining_decreases (basis : List (Fact roles)) (update : At registry before focus after)
    (fact : Fact roles) (member : fact ∈ basis) (old : ¬ Holds before fact) (now : Holds after fact) :
    remaining basis after < remaining basis before := by
  classical
  induction basis with
  | nil => cases member
  | cons head rest ih =>
    rcases List.mem_cons.mp member with rfl | member
    · have tail := remaining_monotone rest update
      rw [remaining_cons,remaining_cons]
      simp only [ite_eq_right old,ite_eq_left now]; omega
    · have tail := ih member
      rw [remaining_cons,remaining_cons]
      by_cases was : Holds before head
      · have current := monotone update head was
        simp only [ite_eq_left was,ite_eq_left current]; exact tail
      · by_cases current : Holds after head <;> simp [current,was] <;> omega

theorem accessible (registry : Registry) (start : State roles) :
    Acc (fun next current => Update registry current next) start := by
  have all : ∀ current : State roles, current.sites = start.sites →
      GeneralNominalState.sources current.context.state ⊆ support start →
      Acc (fun next current => Update registry current next) current := by
    intro current
    induction current using (measure (remaining (facts start))).wf.induction with
    | h current ih =>
      intro sites sources
      refine Acc.intro current ?_
      intro next update
      obtain ⟨newSites,newSources,fact,member,old,now⟩ := supported_update start current next sites sources update
      obtain ⟨focus,action⟩ := as_update update
      exact ih next (remaining_decreases (facts start) action fact member old now) newSites newSources
  exact all start rfl (fun _ member => List.mem_append_left _ member)

end Yulang.GeneralNominalReobservationOrder
