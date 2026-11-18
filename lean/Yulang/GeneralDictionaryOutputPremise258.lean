import Yulang.GeneralDictionaryPendingOutput258
namespace Yulang.GeneralDictionaryOutputPremise258
open GeneralDictionaryOutputDepth252
open GeneralDictionaryPendingOutput258 (replace)
open CommonNominalFullCarrier

theorem bottom_not_expected : ¬ Equivalent (.bottom : Ty) P := by
 intro same
 exact GeneralNominalCenteredHeadMatHeadShape.bottom_no_head (.nominal 0 1)
   ⟨[.inl (nominal 0 [.inl F])],rfl,same⟩

theorem initial_not_outputs :
 GeneralNominalVersionedJournal232.Models initial (replace .bottom) ∧
 ¬ GeneralNominalVersionedPlans231.Outputs plan (replace .bottom) := by
 refine ⟨GeneralDictionaryPendingOutput258.initial_models .bottom,?_⟩
 intro outputs
 exact bottom_not_expected ((GeneralDictionaryPendingOutput258.outputs_exact .bottom).mp outputs)

theorem initial_not_packet :
 GeneralNominalVersionedJournal232.Models initial (replace .bottom) ∧
 ¬ GeneralNominalVersionedPlans231.Holds plan (replace .bottom) :=
 ⟨initial_not_outputs.1,fun packet => initial_not_outputs.2 packet.2.2⟩

/-- Prepared current Frame and initial Models alone do not establish this
packet's output equations. This is not a source-depth or rejection theorem. -/
theorem frame_not_packet :
 GeneralNominalVersionedEvidence231.Frame registry initial.core root 0 plan ∧
 GeneralNominalVersionedJournal232.Models initial (replace .bottom) ∧
 ¬ GeneralNominalVersionedPlans231.Holds plan (replace .bottom) :=
 ⟨frame,initial_not_packet⟩

theorem expected_outputs : GeneralNominalVersionedPlans231.Outputs plan (replace P) :=
 (GeneralDictionaryPendingOutput258.outputs_exact P).mpr ⟨subtype_refl _,subtype_refl _⟩
end Yulang.GeneralDictionaryOutputPremise258
