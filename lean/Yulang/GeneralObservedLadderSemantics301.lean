import Yulang.GeneralObservedLadderPlan301

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 7500000
namespace Yulang.GeneralObservedLadderSemantics301
open GeneralObservedLadderSource301 (snapshot nominal_at)
open GeneralObservedLadderInitial301 (context)
open GeneralObservedLadderReport301 (point pos display_query display_report)
open GeneralObservedLadderPlan301
open GeneralDeclarationExamples (roles display displayChild)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
open GeneralNominalCenters
open GeneralNominalVersionedPlans231
open GeneralNominalVersionedFrame231 (binder capture)
open GeneralNominalRecursiveInspection
open GeneralNominalUnaryCaptureFacts (private_models)

variable (n i id : Nat) (hi : i ≤ n)

theorem update_support (m : Assignment) (valid : GeneralNominalState.Models (snapshot n) m) :
    Ordinary (packet n i id hi) m ∧
      ProjectionModels (snapshot n) (GeneralNominalPacketSupport.report (packet n i id hi)) m := by
  have fact := private_models (context n) compiled (occurrence i id) display (pos n i (by omega))
    (GeneralNominalOutputGrowthModels.descriptor n (pos n i (by omega)) hi) (nominal_at n i hi)
    0 rfl (point n (i+1) (by omega)) rfl (display_query n) m valid
  have raw := (GeneralNominalPacketSupport.private_exact (packet n i id hi) m).mp fact.1
  refine ⟨⟨raw.2.1,?_,raw.2.2.2⟩,fact.2⟩
  unfold GeneralNominalVersionedAllocation231.merges
  rw [bindings n i id hi]
  intro atom present
  cases present

theorem projected (inner : i ≤ n) (m : Assignment) (valid : GeneralNominalState.Models (snapshot n) m) :
    GeneralNominalOriginTerms.Same m (origin i) (.source (i+1)) := by
  have seen := nominal_argument_bounds (snapshot n) m valid (pos n i (by omega))
    (GeneralNominalOutputGrowthModels.descriptor n (pos n i (by omega)) inner) (nominal_at n i inner)
    0 (point n (i+1) (by omega)) rfl
  refine ⟨seen.1,⟨_,.source (i+1)⟩,?_⟩
  intro a b yes other
  cases other
  exact ⟨(seen.2 a yes).2,(seen.2 a yes).1⟩

theorem holds (m : Assignment) (valid : GeneralNominalState.Models (snapshot n) m) :
    Holds (plan n i id hi) m := by
  have supported := update_support n i id hi m valid
  refine ⟨valid,⟨supported.1,supported.2,point_root_holds _ (occurrence i id) (fun _ => rfl) m,?_,?_,?_,?_⟩,?_⟩
  · intro name used
    have zero : name = 0 := by
      rcases used with head | ⟨clause,member,used⟩
      · simpa [GeneralDeclarations.Declaration.inputNames,GeneralDeclarationPatterns.variablesArgs,
          GeneralDeclarationPatterns.Pattern.variables,GeneralDeclarationPatterns.normalizeArgs,
          GeneralDeclarationPatterns.normalize,display] using head
      · cases List.mem_singleton.mp member
        simpa [GeneralDeclarationPatterns.variablesArgs,GeneralDeclarationPatterns.Pattern.variables,
          GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,displayChild] using used
    subst name
    change GeneralNominalCaptureMerges.Fits m ((capture (packet n i id hi)).inputs 0)
      (m (binder (plan n i id hi) 0)).1
    rw [captured n i id hi,center n i id hi]
    exact ⟨subtype_refl _,subtype_refl _⟩
  · rw [head_schema n i id hi]
    constructor
    · intro entry member
      cases List.mem_singleton.mp member
      obtain ⟨args,fit,equals⟩ := valid.2.1 _ _ (nominal_at n i hi)
      refine ⟨⟨_,.source i⟩,?_⟩
      intro actual obs
      cases obs
      have length : args.length = 1 := by
        change GeneralNominalState.FitsAll (snapshot n).base m
          [.type (point n (i+1) (by omega))] args at fit
        cases fit with | cons _ tail => cases tail; rfl
      exact ⟨args,length,equals⟩
    · intro entry member
      cases List.mem_singleton.mp member
      simpa only [ite_true,center n i id hi] using projected n i hi m valid
  · rw [emitted_schema n i id hi]
    intro entry member _
    rcases List.mem_cons.mp member with rfl|rest
    · change Equivalent (m (i+1)).1 (variables (plan n i id hi) m .lower 0)
      rw [(var_bounds n i id hi m).1]
      exact ⟨subtype_refl _,subtype_refl _⟩
    · cases List.mem_singleton.mp rest
      change Equivalent (m (i+1)).1 (variables (plan n i id hi) m .upper 0)
      rw [(var_bounds n i id hi m).2]
      exact ⟨subtype_refl _,subtype_refl _⟩
  · intro clause member signature
    cases List.mem_singleton.mp member
    rw [child_schema n i id hi]
    refine ⟨?_,?_⟩
    · change (child n i id hi).Holds m
      intro k
      rw [child_args n i id hi,child_center n i id hi]
      exact ⟨subtype_refl _,subtype_refl _⟩
    · intro entry member
      cases List.mem_singleton.mp member
      change Equivalent (m (i+1)).1 (variables (plan n i id hi) m .actual 0)
      rw [var_actual n i id hi]
      exact ⟨subtype_refl _,subtype_refl _⟩
  · unfold Outputs
    rw [emitted_schema n i id hi]
    intro entry member
    rcases List.mem_cons.mp member with rfl|rest
    · change Equivalent (m (i+1)).1 (variables (plan n i id hi) m .lower 0)
      rw [(var_bounds n i id hi m).1]
      exact ⟨subtype_refl _,subtype_refl _⟩
    · cases List.mem_singleton.mp rest
      change Equivalent (m (i+1)).1 (variables (plan n i id hi) m .upper 0)
      rw [(var_bounds n i id hi m).2]
      exact ⟨subtype_refl _,subtype_refl _⟩

end Yulang.GeneralObservedLadderSemantics301
