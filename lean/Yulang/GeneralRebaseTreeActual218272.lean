import Yulang.GeneralRebaseTreeCoverage272
import Yulang.GeneralRebaseTreeConstructors272
import Yulang.GeneralDictionaryMixedGround218Install234

set_option maxRecDepth 24000
set_option maxHeartbeats 2500000
namespace Yulang.GeneralRebaseTreeActual218272
open CommonNominalFullCarrier
open GeneralNominalRecursiveInspection (Origin)
open GeneralNominalVersionedCycles232 (Cyclic RootCycle)
open GeneralRebaseFiniteTree272 (Tree Canonical scalar value)
open GeneralRebaseTreeConstructors272 (nominalTree variantTree scalar_canonical variant_checked nominal_tree_canonical)
open GeneralRebaseTreeInterpreter272 (Certified run inspect inspectRoot inspectK2_sound)
open GeneralDictionaryGroundCopy218Source (root sourceRegistry)
open GeneralDictionaryGroundCopy218Install (model model_small)
open GeneralDictionaryMixedGround218Install234 (installed installed_model)

def left : Tree := variantTree 0 (scalar .int)
def right : Tree := variantTree 0 (scalar .bool)
def middle : Tree := nominalTree 5 [left,right]

theorem left_checked : Canonical left := variant_checked 0 _ (scalar_canonical _)
theorem right_checked : Canonical right := variant_checked 0 _ (scalar_canonical _)
theorem middle_checked : Canonical middle := by
 apply nominal_tree_canonical
 intro child listed
 simp only [List.mem_cons,List.not_mem_nil,or_false] at listed
 rcases listed with rfl | rfl
 · exact left_checked
 · exact right_checked

def source : Nat → Option Tree
 | 4 => some left
 | 5 => some right
 | 6 | 7 => some middle
 | _ => none

theorem certified : Certified model source := by
 intro n t h
 have cover : n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 := by
   unfold source at h
   split at h
   · rename_i a; exact Or.inl rfl
   · exact Or.inr (Or.inl rfl)
   · exact Or.inr (Or.inr (Or.inl rfl))
   · exact Or.inr (Or.inr (Or.inr rfl))
   · contradiction
 rcases cover with rfl | rfl | rfl | rfl
 · cases Option.some.inj h
   rw [model_small 4 (by decide +kernel)]
   exact ⟨left_checked,subtype_refl _,subtype_refl _⟩
 · cases Option.some.inj h
   rw [model_small 5 (by decide +kernel)]
   exact ⟨right_checked,subtype_refl _,subtype_refl _⟩
 · cases Option.some.inj h
   rw [model_small 6 (by decide +kernel)]
   exact ⟨middle_checked,subtype_refl _,subtype_refl _⟩
 · cases Option.some.inj h
   rw [model_small 7 (by decide +kernel)]
   exact ⟨middle_checked,subtype_refl _,subtype_refl _⟩

def leftOrigin : Origin := .structural (.nominal (.source 6) 5 0) (.variant 0) 0
def rightOrigin : Origin := .structural (.nominal (.source 6) 5 1) (.variant 0) 0

theorem read_left : run source leftOrigin = .found (scalar .int) := rfl
theorem read_right : run source rightOrigin = .found (scalar .bool) := rfl
theorem unsupported_interval : inspect source (.source 2) = none := rfl

theorem covered_noncycle (o : Origin) (started : GeneralRebaseTreeCoverage272.rootSource o = 6) :
 ¬ Cyclic installed o := by
 have a := GeneralRebaseTreeInterpreter272.inspect_sound installed model installed_model source certified o
 have b := GeneralRebaseTreeCoverage272.returns_negative source o ⟨middle,by rw [started]; rfl⟩
 rw [b] at a
 exact a

theorem root_computed : inspectRoot source installed root = some false := by decide +kernel

theorem actual_root_negative : ¬ (GeneralRebaseSourceSurvivor267.Boundary GeneralDictionaryGroundCopy218Source.roles).RootK2
 sourceRegistry installed root := by
 have claim := inspectK2_sound sourceRegistry installed model installed_model source certified root
 rw [root_computed] at claim
 exact claim

end Yulang.GeneralRebaseTreeActual218272
