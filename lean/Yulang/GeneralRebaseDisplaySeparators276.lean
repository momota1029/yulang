import Yulang.GeneralRebaseDisplayEndpoint276

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 26000
set_option maxHeartbeats 9100000
namespace Yulang.GeneralRebaseDisplaySeparators276
open GeneralNominalExamples (state model heads base listDescriptor)
open GeneralRebaseDisplayFrame276 (after after_models)
open GeneralRebaseDisplayEndpoint276 (known_zero known_one)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalOutputGrowth (tower tower_equivalent)
open CommonNominalFullCarrier (Ty Equivalent subtype_refl)
open GeneralSourceState (equationAtoms)
open Core.PresenceGeneration (TyTerm)
open GeneralNominalRecursiveInspection (Test)

def patch (outside : Nat → Ty) : Assignment := fun id =>
 if id ≤ 1 then model id else (outside id,Common.rowEmpty)

theorem public_value (outside : Nat → Ty) (id : Nat) (small : id ≤ 1) : patch outside id = model id :=
 ite_eq_left small

theorem private_value (outside : Nat → Ty) (id : Nat) (large : 1 < id) :
 (patch outside id).1 = outside id := by
 unfold patch
 rw [ite_eq_right (Nat.not_le_of_gt large)]

theorem base_patched (outside : Nat → Ty) : GeneralNominalState.Models (state true) (patch outside) := by
 refine ⟨⟨?_,?_,?_⟩,?_,by simp [PresenceNormalForm.All]⟩
 · intro atom member
   change atom ∈ equationAtoms (1 : Fin 2) (.base .int) at member
   simp only [equationAtoms,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl|rfl
   · change CommonNominalFullCarrier.Subtype (patch outside 1).1 (.base .int)
     rw [public_value outside 1 (by decide)]
     exact subtype_refl _
   · change CommonNominalFullCarrier.Subtype (.base .int) (patch outside 1).1
     rw [public_value outside 1 (by decide)]
     exact subtype_refl _
 · intro slot term recorded
   change ((heads true slot).equation = some term) at recorded
   by_cases one : slot = 1
   · subst slot
     have equal : term = .base .int := (Option.some.inj recorded).symm
     subst term
     change Equivalent (patch outside 1).1 (.base .int)
     rw [public_value outside 1 (by decide)]
     exact ⟨subtype_refl _,subtype_refl _⟩
   · simp [heads,one,GeneralSourceState.Head.equation] at recorded
 · intro pair member
   simp only [base,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl|rfl <;> exact subtype_refl _
 · intro slot descriptor recorded
   by_cases zero : slot = 0
   · subst slot
     have equal : listDescriptor = descriptor := Option.some.inj recorded
     subst descriptor
     refine ⟨[.inl (.base .int)], .cons ?_ .nil,?_⟩
     · change CommonNominalFullCarrier.Subtype (patch outside 1).1 (.base .int) ∧
         CommonNominalFullCarrier.Subtype (.base .int) (patch outside 1).1
       rw [public_value outside 1 (by decide)]
       exact ⟨subtype_refl _,subtype_refl _⟩
     · change Equivalent (patch outside 0).1 (CommonNominalFullCarrier.nominal 0 [.inl (.base .int)])
       rw [public_value outside 0 (by decide)]
       exact ⟨subtype_refl _,subtype_refl _⟩
   · simp [zero] at recorded

theorem patched (outside : Nat → Ty) : Models after (patch outside) :=
 (after_models _).mpr (base_patched outside)

theorem headless : GeneralNominalVersionedMixedTerminalStable234.HeadlessUnknown after := by
 refine ⟨patch (fun _ => .top),patched _,?_⟩
 intro id present unknown test holds
 have high : 1 < id := by
   by_cases zero : id = 0
   · subst id
     exact False.elim (unknown known_zero)
   · by_cases one : id = 1
     · subst id
       exact False.elim (unknown known_one)
     · omega
 rw [private_value _ _ high] at holds
 exact GeneralDictionaryGroundCopy218Refresh.top_no_head test holds

theorem not_top (id : Nat) : ¬ Equivalent .top (model id).1 := by
 intro equal
 by_cases zero : id = 0
 · subst id
   exact GeneralDictionaryGroundCopy218Refresh.top_no_head (.nominal 0 1)
     ⟨[.inl (.base .int)],rfl,equal⟩
 · exact GeneralDictionaryGroundCopy218Refresh.top_no_head (.scalar .int)
     (by simpa [zero,Test.Holds] using equal)

def mark (id : Nat) : Nat → Ty := fun name => if name = id then .top else (model name).1

theorem isolate_high (a b : Nat) (high : 1 < a) (apart : a ≠ b) :
 ¬ Equivalent (patch (mark a) a).1 (patch (mark a) b).1 := by
 intro equal
 rw [private_value _ _ high] at equal
 have right : (patch (mark a) b).1 = (model b).1 := by
   by_cases small : b ≤ 1
   · rw [public_value _ _ small]
   · rw [private_value _ _ (Nat.lt_of_not_ge small)]
     exact ite_eq_right (Ne.symm apart)
 rw [right] at equal
 have top : mark a a = .top := ite_eq_left rfl
 rw [top] at equal
 exact not_top b equal

theorem equality_names (a b : Nat) (same : GeneralNominalVersionedMixedKernel234.Equal after a b) : a = b := by
 by_cases apart : a = b
 · exact apart
 by_cases aHigh : 1 < a
 · exact False.elim (isolate_high a b aHigh apart (same _ (patched _)))
 by_cases bHigh : 1 < b
 · have contrary := same _ (patched (mark b))
   exact False.elim (isolate_high b a bHigh (Ne.symm apart) ⟨contrary.2,contrary.1⟩)
 have pair : (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by omega
 have actual := same _ GeneralRebaseDisplaySafety276.after_model
 rcases pair with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
 · exact False.elim (by have never : 1 = 0 := (tower_equivalent 1 0).mp actual; cases never)
 · exact False.elim (by have never : 0 = 1 := (tower_equivalent 0 1).mp actual; cases never)

theorem equality_closed : GeneralNominalVersionedMixedTerminalStable234.EqualityClosed after := by
 intro a b _ _ same
 cases equality_names a b same
 intro m valid
 exact ⟨subtype_refl _,subtype_refl _⟩

end Yulang.GeneralRebaseDisplaySeparators276
