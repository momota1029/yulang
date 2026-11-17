import Yulang.GeneralDictionaryLooseFamilyBase240
set_option backward.isDefEq.respectTransparency false
/-! Arbitrary finite point-observation stage. The bookkeeping lists are
explicit parameters. Raw model validity requires the actual ordinary atoms to
hold; no reachable journal or uniform operational iteration is assumed. -/
namespace Yulang.GeneralDictionaryLooseFamilySnapshot240
open GeneralDictionaryLooseFamilyBase240
open GeneralDictionaryLooseLoopSource240 (model S F P)
open CommonNominalFullCarrier

abbrev snapshot (n : Nat) (allocated : List GeneralNominalIdentities.Origin)
 (reserved : List Nat) (ordinary : List (PresenceNormalForm.Atom Nat)) : GeneralNominalState.State where
 base := base n
 view := view n
 constructors := GeneralDeclarationExamples.constructors
 nominals := fun slot => if slot.val = 3 then some (pair n) else
   if slot.val = 2 ∨ 4 ≤ slot.val then some (foo n) else none
 catalogue := by
   intro slot d found
   split at found
   · cases Option.some.inj found; rfl
   · split at found
     · cases Option.some.inj found; rfl
     · cases found
 bodies_opaque := by intro _ _ _; rfl
 allocated := allocated
 reserved := reserved
 ordinary := ordinary
 seed := 4
abbrev context (n : Nat) (allocated : List GeneralNominalIdentities.Origin)
 (reserved : List Nat) (ordinary : List (PresenceNormalForm.Atom Nat)) : GeneralNominalCandidates.Context :=
 ⟨snapshot n allocated reserved ordinary,GeneralDictionaryLooseLoopSource240.interpretation⟩

theorem base_models (n : Nat) : GeneralNominalCommonBridge.Models (base n) model := by
 refine And.intro ?_ (And.intro (by intro _ _ h; cases h) (by intro _ h; cases h))
 intro atom member
 simp only [base,GeneralDictionaryLooseLoopSource240.base,List.mem_map] at member
 obtain ⟨old,present,rfl⟩ := member
 simp only [GeneralDictionaryLooseLoopSource240.atoms,GeneralDictionaryLooseLoopSource240.equations,
   List.flatMap_cons,List.flatMap_nil,List.cons_append,List.nil_append,
   GeneralSourceState.equationAtoms,List.mem_cons,List.not_mem_nil,or_false] at present
 rcases present with rfl | rfl | rfl | rfl
 all_goals exact subtype_refl _

theorem raw_models (n : Nat) (allocated reserved ordinary)
 (atoms : PresenceNormalForm.All CommonNominalFullCarrier.model model ordinary) :
 GeneralNominalState.Models (snapshot n allocated reserved ordinary) model := by
 refine ⟨base_models n,?_,atoms⟩
 intro slot d found
 change (if slot.val=3 then some (pair n) else if slot.val=2 ∨ 4 ≤ slot.val then some (foo n) else none) = some d at found
 split at found
 · rename_i same
   cases Option.some.inj found
   have source3 : source n slot = 3 := by rw [source_small slot (by omega),same]
   refine ⟨[.inl F,.inl F],?_,?_⟩
   · change GeneralNominalState.FitsAll (base n) model [.type (anchor n,original n 4),.type (anchor n,original n 4)] [.inl F,.inl F]
     have fits : GeneralNominalState.Fits (base n) model (.type (anchor n,original n 4)) (.inl F) := by
       change Subtype (model (source n (anchor n))).1 F ∧ Subtype F (model (source n (original n 4))).1
       rw [model_anchor,source_original]; exact ⟨subtype_refl _,subtype_refl _⟩
     exact .cons fits (.cons fits .nil)
   · change Equivalent (model (source n slot)).1 P
     rw [source3]; exact ⟨subtype_refl _,subtype_refl _⟩
 · split at found
   · rename_i relevant
     cases Option.some.inj found
     have value : (model (source n slot)).1 = F := by
       rcases relevant with two | added
       · rw [source_small slot (by omega),two]; rfl
       · by_cases four : slot.val = 4
         · rw [source_small slot (by omega),four]; rfl
         · exact model_added slot (by omega)
     refine ⟨[.inl S],.cons ?_ .nil,?_⟩
     · change Subtype (model (source n (original n 0))).1 S ∧ Subtype S (model (source n (original n 0))).1
       rw [source_original]; exact ⟨subtype_refl _,subtype_refl _⟩
     · change Equivalent (model (source n slot)).1 F
       rw [value]; exact ⟨subtype_refl _,subtype_refl _⟩
   · cases found
end Yulang.GeneralDictionaryLooseFamilySnapshot240
