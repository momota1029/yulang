import Yulang.GeneralVersionRowsHead259
import Yulang.GeneralDictionaryVersionLoopFamilyFull238
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralVersionRowsPacket259
open GeneralDictionaryVersionLoopFamilyBase238
open GeneralDictionaryVersionLoopFamilySnapshot238 (snapshot context)
open GeneralDictionaryVersionLoopFamilyPacket238
open GeneralDictionaryVersionLoopFamilyFull238 (head_schema binder_exact emitted_empty)
open GeneralDictionaryVersionLoopSource237 (roles registry declaration root F)
open GeneralDictionaryVersionLoopNames238 (lower upper)
open GeneralDictionaryVersionLoopPacket237 (origin0 origin1 actual)
open GeneralNominalCenters GeneralDeclarations CommonNominalFullCarrier
open GeneralVersionRowsRaw259 GeneralVersionRowsHead259
variable (rows : Nat → Common.Row)
theorem actual_value : ((withRows rows) actual).1 = F := GeneralDictionaryVersionLoopPacket237.actual_value
variable (n : Nat) (allocated : List GeneralNominalIdentities.Origin)
 (reserved : List Nat) (ordinary : List (PresenceNormalForm.Atom Nat))
theorem head_holds : GeneralNominalVersionedPlans231.SchemaHolds (plan n allocated reserved ordinary) (plan n allocated reserved ordinary).headSchema (withRows rows) := by
  rw [head_schema]
  constructor
  · intro test member
    cases List.mem_singleton.mp member
    refine ⟨⟨_,.source 3⟩,?_⟩
    intro value seen
    cases seen
    exact ⟨[.inl F,.inl F],rfl,subtype_refl _,subtype_refl _⟩
  · intro entry member
    rcases List.mem_cons.mp member with rfl | member
    all_goals first | cases List.mem_singleton.mp member | skip
    all_goals
      simp only [ite_true]
      refine ⟨?_,⟨_,.source _⟩,?_⟩
      · first | exact ⟨_,seen0 rows⟩ | exact ⟨_,seen1 rows⟩
      · intro x y seenX seenY
        cases seenY
        rw [GeneralNominalVersionedFrame231.binder_eq,binder_exact,actual_value rows]
        first | exact observed_value rows 0 (by decide) seenX | exact observed_value rows 1 (by decide) seenX


theorem packet_holds (atoms : PresenceNormalForm.All CommonNominalFullCarrier.model (withRows rows) ordinary) : GeneralNominalVersionedPlans231.Holds (plan n allocated reserved ordinary) (withRows rows) := by
 have head : GeneralNominalVersionedPlans231.HeadModels (packet n allocated reserved ordinary) (withRows rows) := head_model rows n allocated reserved ordinary atoms
 have rawOrdinary := ((GeneralNominalVersionedPlans231.private_models_iff (packet n allocated reserved ordinary) (withRows rows)).mp head.1).2
 refine ⟨raw_models rows n allocated reserved ordinary atoms,⟨rawOrdinary,head.2,?_,?_,head_holds rows n allocated reserved ordinary,?_,?_⟩,?_⟩
 · intro index; exact ⟨subtype_refl _,subtype_refl _⟩
 · intro name needed
   have same : name=0 := by
     rcases needed with named | ⟨clause,member,_⟩
     · simpa [Declaration.inputNames,GeneralDeclarationPatterns.variablesArgs,
         GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
         GeneralDeclarationPatterns.Pattern.variables] using named
     · cases member
   subst name
   rw [GeneralNominalVersionedFrame231.binder_eq,binder_exact,actual_value rows]
   change GeneralNominalCaptureMerges.Fits (withRows rows) ((GeneralNominalVersionedAllocation231.capture _ _ _ _ (packet n allocated reserved ordinary).bindings).inputs 0) F
   rw [bindings_exact]
   change Subtype ((withRows rows) (lower (n+1))).1 F ∧ Subtype F ((withRows rows) (upper n)).1
   rw [model_lower rows,model_upper rows]
   exact ⟨subtype_refl _,subtype_refl _⟩
 · intro equation member _; rw [emitted_empty] at member; cases member
 · intro clause member; cases member
 · intro equation member; rw [emitted_empty] at member; cases member

end Yulang.GeneralVersionRowsPacket259
