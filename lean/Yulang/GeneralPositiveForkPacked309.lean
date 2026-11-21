import Yulang.GeneralPositiveForkSettlement309
import Yulang.GeneralRebasePackedAnswers298
import Yulang.GeneralRebaseDisplayFrame285

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 26000
set_option maxHeartbeats 16000000
namespace Yulang.GeneralPositiveForkPacked309
open GeneralPositiveForkSource309 (initial registry root)
open GeneralPositiveForkInstall309 (after models inhabited)
open GeneralPositiveForkNodes309 (focus)
open GeneralPositiveForkEvidence309 (parentPlan payload)
open GeneralPositiveForkPayload309 (iff_expected)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedJournal232 (Models initial_models)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
open GeneralDeclarationExamples (roles)
open GeneralRebaseDisplayFrame285 (TypeCheck source_check)
open GeneralRebaseQuestionFootprint298 (Footprint agrees)
open GeneralRebasePackedAnswers298 (Vector pack fill retain)
open GeneralNominalExamples (model)

abbrev footprint : Footprint := ⟨[0,1],[]⟩

def Joint (m : Assignment) (p l r : Payload) : Prop :=
  Models after m ∧
  GeneralDictionaryDefaultEvidence204.OutputWitness parentPlan m ⟨0,1⟩ ∧
  (boundary roles).Evidence registry after m root p ∧
  (boundary roles).Evidence registry after m (focus .low) l ∧
  (boundary roles).Evidence registry after m (focus .high) r

theorem model_exact (m : Assignment) : Models after m ↔ TypeCheck m := by
  rw [models,initial_models]
  exact ⟨fun h => (source_check m).mp h.1,fun h =>
    ⟨(source_check m).mpr h,GeneralNominalCenters.point_root_holds _ _ (fun _ => rfl) _⟩⟩

theorem exact_joint (m : Assignment) (p l r : Payload) :
    Joint m p l r ↔ TypeCheck m ∧ p = payload ∧ l = .node 2 [] ∧ r = .node 3 [] := by
  unfold Joint
  constructor
  · rintro ⟨valid,_,parent,one,two⟩
    exact ⟨(model_exact m).mp valid,(iff_expected .parent m valid p).mp parent,
      (iff_expected .low m valid l).mp one,(iff_expected .high m valid r).mp two⟩
  · rintro ⟨ty,rfl,rfl,rfl⟩
    have valid := (model_exact m).mpr ty
    obtain ⟨out,one,two,par⟩ := GeneralPositiveForkEvidence309.both_same_model m valid
    exact ⟨valid,out,par,one,two⟩

theorem framing (a b : Assignment) (p l r : Payload) (same : agrees footprint a b) :
    Joint a p l r ↔ Joint b p l r := by
  rw [exact_joint,exact_joint]
  simp only [TypeCheck,same.1 0 (by decide),same.1 1 (by decide)]

theorem exact_packed (m fallback : Assignment) (p l r : Payload) :
    Joint (fill footprint (pack footprint m) fallback) p l r ↔ Joint m p l r :=
  framing _ _ _ _ _ (retain _ _ _)

theorem arbitrary_fallback (fallback : Assignment) :
    ∃ packed : Vector footprint,
      Joint (fill footprint packed fallback) payload (.node 2 []) (.node 3 []) :=
  ⟨pack footprint model,(exact_packed model fallback _ _ _).mpr
    ((exact_joint model _ _ _).mpr ⟨(model_exact _).mp inhabited,rfl,rfl,rfl⟩)⟩

end Yulang.GeneralPositiveForkPacked309
