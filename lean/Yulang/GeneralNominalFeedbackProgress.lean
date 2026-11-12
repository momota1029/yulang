import Yulang.GeneralNominalFeedbackSteps
import Yulang.GeneralNominalAdministrativeProgress

/-! Persistent progress facts include ordinary equality feedback. A finite
basis yields full accessibility for the new relation. Its construction from
source formation and interval descent is deliberately left separate. -/
namespace Yulang.GeneralNominalFeedbackProgress

noncomputable section

open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalFeedbackSteps

variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}
variable {before after start : State roles}
local instance (p : Prop) : Decidable p := Classical.propDecidable p

structure Extends (before after : State roles) : Prop where
  journal : GeneralNominalSaturationSteps.Extends before after
  ordinary : ∀ model, GeneralNominalState.Models after.context.state model →
    GeneralNominalState.Models before.context.state model

theorem at_extends (update : At registry before focus after) : Extends before after := by
  cases update with
  | enqueue focus _ _ =>
      exact ⟨⟨fun model valid => (enqueue_models before focus model).mp valid,
        fun _ member => List.mem_append_left _ member,fun _ member => member,
        fun _ member => member,fun _ known => known⟩,fun _ valid => valid⟩
  | install packet enabled _ =>
      have refinement := GeneralNominalRefinements.installed packet.registry packet.context packet.site.occurrence
        packet.declaration packet.bounds
      have raw : ∀ model, GeneralNominalState.Models packet.privateContext.state model →
          GeneralNominalState.Models before.context.state model := by
        intro model valid
        rw [← enabled.1.2.1]
        exact GeneralNominalRefinements.models refinement model valid
      refine ⟨⟨fun model valid => ((GeneralNominalFeedbackSites.install_models before packet _ enabled.1.2.1 model).mp valid).1,
        fun _ member => List.mem_append_left _ member,fun _ member => List.mem_append_left _ member,
        fun _ member => member,?_,⟩,raw⟩
      intro source known
      apply refinement.known source
      simpa only [enabled.1.2.1] using known
  | merge first last _ _ _ _ =>
      exact ⟨⟨fun model valid => ((merge_models before first last model).mp valid).1,
        fun _ member => member,fun _ member => member,fun _ member => List.mem_cons_of_mem _ member,
        fun _ known => known⟩,
        fun model valid => ((GeneralNominalState.extend_models ..).mp valid).1⟩
  | refresh focus context certificate source member unknown known =>
      exact ⟨⟨fun model valid => (GeneralNominalCycleSteps.refresh_models certificate model).mp valid,
        fun _ member => member,fun _ member => member,fun _ member => member,certificate.refines.known⟩,
        GeneralNominalRefinements.models certificate.refines⟩
  | equate focus first last _ _ equal _ =>
      exact ⟨⟨fun model valid => (equate_models before first last equal model).mp valid,
        fun _ member => member,fun _ member => member,fun _ member => member,fun _ known => known⟩,
        fun model valid => ((GeneralNominalState.extend_models ..).mp valid).1⟩

abbrev Fact (roles : Roles.RoleDecls) := GeneralNominalSaturationProgress.Fact roles ⊕ (Nat × Nat)

def Holds (state : State roles) : Fact roles → Prop
  | .inl fact => GeneralNominalSaturationProgress.Holds state fact
  | .inr pair => RawEqual state pair.1 pair.2

theorem monotone (growth : Extends before after) (fact : Fact roles) : Holds before fact → Holds after fact := by
  cases fact with
  | inl fact => exact GeneralNominalSaturationProgress.monotone growth.journal fact
  | inr pair => exact fun prior model valid => prior model (growth.ordinary model valid)

theorem fresh_fact (update : Step registry root before after) : ∃ fact : Fact roles, ¬ Holds before fact ∧ Holds after fact := by
  classical
  obtain ⟨focus,_,action⟩ := update
  cases action with
  | enqueue focus _ absent =>
      exact ⟨.inl (.site (GeneralNominalDemandMerging.pointSite focus)),fun member => absent _ member rfl,
        List.mem_append_right _ (by simp)⟩
  | install packet enabled novel =>
      by_cases entailed : ∀ model, Models before model → packet.Holds model
      · have missing : ∃ child ∈ packet.children, (packet.site.occurrence,child) ∉ before.edges := by
          apply Classical.byContradiction
          intro none
          apply novel
          refine ⟨entailed,?_⟩
          intro child member
          by_cases found : (packet.site.occurrence,child) ∈ before.edges
          · exact found
          · exact False.elim (none ⟨child,member,found⟩)
        obtain ⟨child,member,absent⟩ := missing
        exact ⟨.inl (.edge packet.site.occurrence child),absent,(installed_committed before packet).2 child member⟩
      · exact ⟨.inl (.constraints packet),entailed,(installed_committed before packet).1⟩
  | merge first last _ _ _ novel =>
      exact ⟨.inl (.alias first.occurrence.identity last.occurrence.identity),novel,
        GeneralNominalCycleSteps.merged_inputs before first last⟩
  | refresh _ _ _ source _ unknown known => exact ⟨.inl (.known source),unknown,known⟩
  | equate _ first last _ _ _ novel => exact ⟨.inr (first,last),novel,equate_feedback before first last⟩

noncomputable def remaining (facts : List (Fact roles)) (state : State roles) : Nat := by
  classical
  exact facts.foldr (fun fact count => if Holds state fact then count else count+1) 0

private theorem remaining_cons (fact : Fact roles) (rest : List (Fact roles)) (state : State roles) :
    remaining (fact :: rest) state = if Holds state fact then remaining rest state else remaining rest state+1 := by
  classical
  rfl

private theorem remaining_monotone (facts : List (Fact roles)) (growth : Extends before after) :
    remaining facts after ≤ remaining facts before := by
  classical
  induction facts with
  | nil => exact Nat.le_refl _
  | cons fact rest ih =>
      rw [remaining_cons,remaining_cons]
      by_cases old : Holds before fact
      · have current := monotone growth fact old
        simp only [ite_eq_left old,ite_eq_left current]; exact ih
      · by_cases current : Holds after fact <;> simp [current,old] <;> omega

theorem remaining_decreases (facts : List (Fact roles)) (growth : Extends before after)
    (fact : Fact roles) (member : fact ∈ facts) (old : ¬ Holds before fact) (current : Holds after fact) :
    remaining facts after < remaining facts before := by
  classical
  induction facts with
  | nil => cases member
  | cons head rest ih =>
      rcases List.mem_cons.mp member with rfl | member
      · have tail := remaining_monotone rest growth
        rw [remaining_cons,remaining_cons]
        simp only [ite_eq_right old,ite_eq_left current]
        omega
      · have tail := ih member
        rw [remaining_cons,remaining_cons]
        by_cases was : Holds before head
        · have now := monotone growth head was
          simp only [ite_eq_left was,ite_eq_left now]; exact tail
        · by_cases now : Holds after head <;> simp [now,was] <;> omega

structure FiniteBasis (registry : Registry) (root : Occurrence roles) (initial : State roles) where
  facts : List (Fact roles)
  covers : ∀ before after, B4Target.Steps (Step registry root) initial before → Step registry root before after →
    ∃ fact ∈ facts, ¬ Holds before fact ∧ Holds after fact

theorem accessible_of_finite_basis (basis : FiniteBasis registry root start) :
    Acc (fun next current => Step registry root current next) start := by
  have accessible : ∀ state, B4Target.Steps (Step registry root) start state →
      Acc (fun next current => Step registry root current next) state := by
    intro state
    induction state using (measure (remaining basis.facts)).wf.induction with
    | h state ih =>
      intro path
      refine Acc.intro state ?_
      intro next update
      obtain ⟨fact,member,old,current⟩ := basis.covers state next path update
      exact ih next (remaining_decreases basis.facts (at_extends update.choose_spec.2) fact member old current) (.tail path update)
  exact accessible start .refl

end

end Yulang.GeneralNominalFeedbackProgress
