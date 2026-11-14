import Yulang.GeneralNominalRefiningJournal198
import Yulang.GeneralNominalSlotGrowth198

set_option backward.isDefEq.respectTransparency false
/-! An inhabited actual WF refresh grows and reindexes slots, and turns a
previously unresolved source into a scalar observation. No packet is installed. -/
namespace Yulang.GeneralNominalGrowingRefresh198
open GeneralNominalSlotGrowth198 (before after)
open GeneralDictionaryRefinementExamples (grown)
open GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadStepKernel
open GeneralDeclarations GeneralSourceDictionaries
open GeneralDeclarationExamples (roles constructors)

def observedView : GeneralNormalizedObservation.Snapshot grown where
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro i; exact Fin.elim0 i
  canonical := by intro i; exact Fin.elim0 i
  heads := fun slot => if slot = 1 then .scalar .int else .deferred .unresolved
  checked := by
    intro slot term recorded
    by_cases one : slot = 1
    · subst slot
      have equal : (Core.PresenceGeneration.TyTerm.base .int : Core.PresenceGeneration.TyTerm (Fin 2)) = term := by
        simpa [GeneralNormalizedObservation.Head.term] using recorded
      subst term
      exact .ordinary (by simp [grown,GeneralSourceState.equationAtoms])
        (by simp [grown,GeneralSourceState.equationAtoms])
    · simp [one,GeneralNormalizedObservation.Head.term,GeneralNormalizedObservation.Deferred.term] at recorded

abbrev observed : GeneralNominalState.State :=
  {after with view := observedView, bodies_opaque := by intro _ _ impossible; cases impossible}

def refinement : GeneralNominalRefinements.Refines before observed where
  base := GeneralNominalSlotGrowth198.refinement.base
  heads := by intro _ _ impossible; cases impossible
  nominals := by intro _ _ impossible; cases impossible
  ordinary := by intro _ impossible; cases impossible
  known := by
    rintro source ⟨slot,same,seen | ⟨descriptor,recorded⟩⟩
    · exact False.elim (seen rfl)
    · cases recorded
  reserved := fun _ member => member
  allocated := fun _ member => member
  seed := rfl
  constructors := rfl

theorem forward (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models before model) : GeneralNominalState.Models observed model := by
  refine ⟨⟨?_,?_,?_⟩,?_,?_⟩
  · intro atom member
    simp only [observed,after,grown,GeneralSourceState.equationAtoms,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact valid.1.1 _ (List.mem_cons_self)
    · exact valid.1.1 _ (List.mem_cons_of_mem _ (List.mem_cons_self))
  · intro slot term impossible
    cases impossible
  · intro pair member
    have same : pair = (1,1) := List.mem_singleton.mp member
    subst pair
    exact CommonNominalFullCarrier.subtype_refl _
  · intro slot descriptor impossible
    cases impossible
  · intro atom member
    cases member

abbrev oldContext : GeneralNominalCandidates.Context := ⟨before,GeneralNominalExamples.interpretation⟩
abbrev nextContext : GeneralNominalCandidates.Context := ⟨observed,GeneralNominalExamples.interpretation⟩
abbrev root : Occurrence roles := ⟨198,⟨0,fun _ => (10,10),[],by intro _ impossible; cases impossible⟩⟩
abbrev declaration : Declaration := ⟨1980,0,[.var 0],[],[],[]⟩
abbrev registry : Registry := ⟨constructors,roles,[declaration]⟩
abbrev start := initial oldContext root
abbrev finish := refresh start nextContext

def certificate : GeneralNominalCenteredSteps.Refresh start.core nextContext where
  refines := refinement
  interpretation := rfl
  exact := fun model valid => forward model valid.1.1
  support := GeneralNominalSlotGrowth198.supported

theorem actual_step : GeneralNominalRefiningJournal198.MixedStep registry root start finish := by
  apply GeneralNominalRefiningJournal198.refresh_step certificate
  · intro d member query within
    have same := List.mem_singleton.mp member
    subst d
    have sameQuery : query = .variables [0] := by
      simpa [GeneralNominalInspection.queries,Declaration.normalHead,
        GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
        GeneralNominalInspection.translate] using within
    subst query
    exact .variables
  · change 10 ∈ GeneralNominalState.sources before
    simp [GeneralNominalState.sources,List.ofFn_succ]
  · rintro ⟨slot,same,seen | ⟨descriptor,recorded⟩⟩
    · exact seen rfl
    · cases recorded
  · refine ⟨1,rfl,Or.inl ?_⟩
    decide

theorem growth_and_reindex :
    start.core.erased.current.context.state.base.slots < finish.core.erased.current.context.state.base.slots ∧
    certificate.refines.base.embed ⟨0,by change 0 < 1; decide⟩ = ⟨1,by change 1 < 2; decide⟩ := ⟨by decide,rfl⟩

theorem inhabited : ∃ model, Models start model ∧ Models finish model := by
  obtain ⟨model,valid,_⟩ := GeneralNominalSlotGrowth198.inhabited
  have initialModel : Models start model := by
    apply initial_models.mpr
    exact (GeneralNominalCenteredSteps.point_initial_models oldContext root (fun _ => rfl) model).mpr valid
  exact ⟨model,initialModel,(refresh_models certificate model).mpr initialModel⟩
end Yulang.GeneralNominalGrowingRefresh198
