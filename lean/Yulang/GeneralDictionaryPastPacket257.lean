import Yulang.GeneralDictionaryPastObservations257
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryPastPacket257
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryLooseIterationBook240 (context packet plan)
open GeneralDictionaryLooseLoopSource240 (F P declaration)
open GeneralDictionaryLooseLoopPacket240 (actual)
open GeneralNominalRecursiveInspection
open CommonNominalFullCarrier

theorem actual_value (n : Nat) (assignment : Assignment)
 (valid : GeneralNominalState.Models (context n).state assignment)
 (binder : GeneralDictionaryBinderFact257.Holds assignment) : Equivalent (assignment actual).1 F := by
 have source := GeneralDictionaryHistoricalValues257.raw_initial n assignment valid
 have value := GeneralDictionaryLooseLoopInitial240.foo_fixed assignment source
 exact ⟨subtype_trans binder.1 value.1,subtype_trans value.2 binder.2⟩

theorem head_schema (n index : Nat) (assignment : Assignment)
 (valid : GeneralNominalState.Models (context n).state assignment)
 (binder : GeneralDictionaryBinderFact257.Holds assignment) :
 GeneralNominalVersionedPlans231.SchemaHolds (plan index) (plan index).headSchema assignment := by
 have source := GeneralDictionaryHistoricalValues257.raw_initial n assignment valid
 have center := actual_value n assignment valid binder
 rw [GeneralDictionaryLooseFamilyFull240.head_schema]
 constructor
 · intro test member
   cases List.mem_singleton.mp member
   refine ⟨⟨_,.source 3⟩,?_⟩
   intro value seen
   cases seen
   exact ⟨[.inl F,.inl F],rfl,GeneralDictionaryLooseLoopInitial240.root_fixed assignment source⟩
 · intro entry member
   rcases List.mem_cons.mp member with rfl | member
   all_goals first | cases List.mem_singleton.mp member | skip
   all_goals
     simp only [ite_true]
     refine ⟨?_,⟨_,.source _⟩,?_⟩
     · first | exact ⟨F,GeneralDictionaryPastObservations257.observed assignment source 0 (by decide)⟩
             | exact ⟨F,GeneralDictionaryPastObservations257.observed assignment source 1 (by decide)⟩
     · intro x y seenX seenY
       cases seenY
       rw [GeneralNominalVersionedFrame231.binder_eq,GeneralDictionaryLooseFamilyFull240.binder_exact]
       have same : Equivalent x F := by
         first | exact GeneralDictionaryPastObservations257.observed_value assignment source 0 (by decide) x seenX
               | exact GeneralDictionaryPastObservations257.observed_value assignment source 1 (by decide) x seenX
       exact ⟨subtype_trans same.1 center.2,subtype_trans center.1 same.2⟩

theorem holds (n index : Nat) (before : index < n) (assignment : Assignment)
 (valid : GeneralNominalState.Models (context n).state assignment)
 (binder : GeneralDictionaryBinderFact257.Holds assignment) :
 GeneralNominalVersionedPlans231.Holds (plan index) assignment := by
 refine ⟨GeneralDictionaryPastRaw257.raw_past n index (by omega) assignment valid,
   ⟨GeneralDictionaryPastRaw257.ordinary_past n index before assignment valid,
     GeneralDictionaryPastObservations257.projection n index (by omega) assignment valid,
     ?_,?_,head_schema n index assignment valid binder,?_,?_⟩,?_⟩
 · intro i; exact ⟨subtype_refl _,subtype_refl _⟩
 · intro name needed
   have same : name=0 := by
     rcases needed with named | ⟨clause,member,_⟩
     · simpa [GeneralDeclarations.Declaration.inputNames,GeneralDeclarationPatterns.variablesArgs,
         GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
         GeneralDeclarationPatterns.Pattern.variables] using named
     · cases member
   subst name
   rw [GeneralNominalVersionedFrame231.binder_eq,GeneralDictionaryLooseFamilyFull240.binder_exact]
   change GeneralNominalCaptureMerges.Fits assignment
     ((GeneralNominalVersionedAllocation231.capture _ _ _ _ (packet index).bindings).inputs 0)
     (assignment actual).1
   rw [GeneralDictionaryLooseFamilyPacket240.bindings_exact]
   exact (GeneralDictionaryBinderFact257.fits_exact n index before assignment valid).mpr binder
 · intro equation member _
   rw [GeneralDictionaryLooseFamilyFull240.emitted_empty] at member
   cases member
 · intro clause member; cases member
 · intro equation member
   rw [GeneralDictionaryLooseFamilyFull240.emitted_empty] at member
   cases member
end Yulang.GeneralDictionaryPastPacket257
