import Yulang.GeneralDictionaryRebaseCurrent259
import Yulang.GeneralDictionaryVersionLoopFamilySnapshot238
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralVersionRowsRaw259
open GeneralDictionaryVersionLoopFamilyBase238
open GeneralDictionaryVersionLoopFamilySnapshot238 (snapshot)
open GeneralDictionaryVersionLoopSource237 (S F P)
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)

def withRows (rows : Nat → Common.Row) : Assignment :=
 fun name => ((GeneralDictionaryVersionLoopSource237.model name).1,rows name)
variable (rows : Nat → Common.Row)

theorem base_models (n : Nat) : GeneralNominalCommonBridge.Models (base n) (withRows rows) := by
 refine And.intro ?_ (And.intro (by intro _ _ h; cases h) (by intro _ h; cases h))
 intro atom member
 simp only [base,GeneralDictionaryVersionLoopSource237.base,List.mem_map] at member
 obtain ⟨old,present,rfl⟩ := member
 simp only [GeneralDictionaryVersionLoopSource237.atoms,GeneralDictionaryVersionLoopSource237.equations,
   List.flatMap_cons,List.flatMap_nil,List.cons_append,List.nil_append,
   GeneralSourceState.equationAtoms,List.mem_cons,List.not_mem_nil,or_false] at present
 rcases present with rfl | rfl | rfl | rfl
 all_goals exact subtype_refl _

theorem raw_models (n : Nat) (allocated reserved ordinary)
 (atoms : PresenceNormalForm.All CommonNominalFullCarrier.model (withRows rows) ordinary) :
 GeneralNominalState.Models (snapshot n allocated reserved ordinary) (withRows rows) := by
 refine ⟨base_models rows n,?_,atoms⟩
 intro slot d found
 change (if slot.val=3 then some (pair n) else if slot.val=2 ∨ 4 ≤ slot.val then some (foo n) else none) = some d at found
 split at found
 · rename_i same
   cases Option.some.inj found
   have source3 : source n slot = 3 := by rw [source_small slot (by omega),same]
   refine ⟨[.inl F,.inl F],?_,?_⟩
   · change GeneralNominalState.FitsAll (base n) (withRows rows) [.type (anchor n,anchor n),.type (anchor n,anchor n)] [.inl F,.inl F]
     have fits : GeneralNominalState.Fits (base n) (withRows rows) (.type (anchor n,anchor n)) (.inl F) := by
       change Subtype ((withRows rows) (source n (anchor n))).1 F ∧ Subtype F ((withRows rows) (source n (anchor n))).1
       dsimp only [withRows]
       rw [model_anchor]; exact ⟨subtype_refl _,subtype_refl _⟩
     exact .cons fits (.cons fits .nil)
   · change Equivalent ((withRows rows) (source n slot)).1 P
     rw [source3]; exact ⟨subtype_refl _,subtype_refl _⟩
 · split at found
   · rename_i relevant
     cases Option.some.inj found
     have value : ((withRows rows) (source n slot)).1 = F := by
       rcases relevant with two | added
       · rw [source_small slot (by omega),two]; rfl
       · exact model_added slot added
     refine ⟨[.inl S],.cons ?_ .nil,?_⟩
     · change Subtype ((withRows rows) (source n (original n 0))).1 S ∧ Subtype S ((withRows rows) (source n (original n 0))).1
       rw [source_original]; exact ⟨subtype_refl _,subtype_refl _⟩
     · change Equivalent ((withRows rows) (source n slot)).1 F
       rw [value]; exact ⟨subtype_refl _,subtype_refl _⟩
   · cases found
end Yulang.GeneralVersionRowsRaw259
