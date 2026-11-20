import Yulang.GeneralRebasePackedSource298
import Yulang.GeneralRebaseDisplayFrame285
import Yulang.GeneralRebaseSilentFactor298

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 23000
set_option maxHeartbeats 10000000
namespace Yulang.GeneralRebasePackedNonleaf298
open GeneralNominalExamples (registry model displayRoot displayChild)
open GeneralDeclarationExamples (roles)
open GeneralRebaseDisplayFrame276 (before)
open GeneralRebaseCompiledDisplay277 (after compiled effect)
open GeneralRebaseSourceSurvivor267 (Boundary)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedEvidence231 (Evidence)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
open GeneralRebaseQuestionFootprint298 (Footprint agrees prior)
open GeneralRebasePackedAnswers298 (Vector pack fill retain)
open GeneralRebaseDisplayFrame285 (TypeCheck parent_exact child_exact)
open Core.PresenceGeneration (CompTerm)

def footprint : Footprint := ⟨[0,1],[]⟩

def joint (m : Assignment) (p d : Payload) : Prop :=
  Models after m ∧ Evidence compiled after.core m displayRoot p ∧ Evidence compiled after.core m displayChild d

theorem joint_exact (m : Assignment) (p d : Payload) :
    joint m p d ↔ TypeCheck m ∧ p = .node 1 [.node 3 []] ∧ d = .node 3 [] := by
  unfold joint
  constructor
  · rintro ⟨held,pa,ch⟩
    obtain ⟨tys,par⟩ := (parent_exact m p).mp ⟨held,pa⟩
    exact ⟨tys,par,((child_exact m d).mp ⟨held,ch⟩).2⟩
  · rintro ⟨tys,pa,ch⟩
    obtain ⟨held,parent⟩ := (parent_exact m p).mpr ⟨tys,pa⟩
    exact ⟨held,parent,((child_exact m d).mpr ⟨tys,ch⟩).2⟩

theorem stable (a b : Assignment) (p d : Payload) (same : agrees footprint a b) :
    joint a p d ↔ joint b p d := by
  rw [joint_exact,joint_exact]
  simp only [TypeCheck,same.1 0 (by decide),same.1 1 (by decide)]

theorem model_and_tree_packed (a fallback : Assignment) (p d : Payload) :
    joint (fill footprint (pack footprint a) fallback) p d ↔ joint a p d :=
  stable _ _ p d (retain _ _ _)

theorem witness_reified (fallback : Assignment) :
    ∃ data : Vector footprint,
      joint (fill footprint data fallback) (.node 1 [.node 3 []]) (.node 3 []) := by
  have raw := GeneralRebaseCompiledSelection277.after_model
  refine ⟨pack footprint model,(model_and_tree_packed model fallback _ _).mpr ?_⟩
  exact (joint_exact model _ _).mpr
    ⟨(GeneralRebaseDisplayFrame285.final_check _).mp raw,rfl,rfl⟩

theorem actual_generated :
    (Boundary roles).Step registry displayRoot before after ∧
      GeneralNominalSaturationState.Generated after.core.erased.current displayRoot displayChild :=
  ⟨GeneralRebaseCompiledInstall277.actual_step,.child .root (GeneralNominalVersionedInstall232.installed_child (effect := effect) (GeneralRebaseCompiledDisplay277.children.symm ▸ List.mem_cons_self ..))⟩

theorem hidden_by_no_output_projection :
    GeneralRebaseWeakProgress268.Stutter compiled displayRoot [] [] before after :=
  ⟨actual_generated.1,GeneralRebaseStep258.state_ext _ _ rfl⟩

end Yulang.GeneralRebasePackedNonleaf298
