import Yulang.GeneralRebaseCompoundOwnerBlock273

namespace Yulang.GeneralRebaseCompoundOwnerStep273
open GeneralNominalAllocation (Bindings)
open GeneralRebaseCompoundOwnerBlock273 (Slot PublicSlot Block loose point compile)
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseCompoundSourceTypes273 (PublicSource Body)
open GeneralRebaseCompoundReplacementFrame273 (Meaning)

inductive Stage where
 | initial | installed | replacement
 deriving DecidableEq, Repr

def block : Stage → Option Block
 | .initial => none
 | .installed => some loose
 | .replacement => some point

def remaining : Stage → Nat
 | .initial => 2
 | .installed => 1
 | .replacement => 0

/-- This experiment uses only the known one-owner shape of the actual
two-observation source. Other bind lists or out-of-order stages abstain. -/
def next (s : Stage) (inputs : Bindings) (center : PublicSlot) : Option Stage :=
 match compile inputs center,s with
 | some found,.initial => if found = loose then some .installed else none
 | some found,.installed => if found = point then some .replacement else none
 | _,_ => none

def Step (a b : Stage) : Prop := ∃ inputs center, next a inputs center = some b

theorem decreases {a b : Stage} (step : Step a b) : remaining b < remaining a := by
 obtain ⟨inputs,center,h⟩ := step
 unfold next at h
 split at h <;> try contradiction
 all_goals split at h <;> try contradiction
 all_goals cases Option.some.inj h; decide

theorem accessible (s : Stage) : Acc (fun next previous => Step previous next) s := by
 let h := measure remaining
 have proof := h.wf.apply s
 induction proof with
 | intro current prev ih =>
   exact .intro current (fun child step => ih child (decreases step))

theorem actual_install :
 next .initial GeneralDictionaryCompoundPacket238.packet.bindings 2 = some .installed := by
 unfold next
 rw [GeneralRebaseCompoundOwnerBlock273.actual_loose]
 rfl

theorem actual_replacement :
 next .installed GeneralDictionaryCompoundObstruction238.currentPlan.packet.bindings 2 = some .replacement := by
 unfold next
 rw [GeneralRebaseCompoundOwnerBlock273.actual_point]
 rfl

theorem no_third (after : Stage) : ¬ Step .replacement after := by
 intro given
 have less := decreases given
 exact (Nat.not_lt_zero _) less

theorem no_backwards (inputs : Bindings) (center : PublicSlot) :
 next .replacement inputs center = none := by cases h : compile inputs center <;> simp [next,h]

theorem no_loose_replay :
 next .installed GeneralDictionaryCompoundPacket238.packet.bindings 2 = none := by
 unfold next
 rw [GeneralRebaseCompoundOwnerBlock273.actual_loose]
 rfl

def PublicMeaning (s : Stage) (boundary : Assignment) : Prop :=
 PublicSource boundary ∧ (s ≠ .initial → Body boundary)

theorem install_meaning (boundary : Assignment) : PublicMeaning .installed boundary ↔
 GeneralRebaseCompoundPublic273.Fixed boundary := by
 rw [GeneralRebaseCompoundSourceTypes273.restricted_exact]
 simp [PublicMeaning]

theorem replacement_meaning (boundary : Assignment) : PublicMeaning .replacement boundary ↔
 GeneralRebaseCompoundPublic273.Fixed boundary := by
 rw [GeneralRebaseCompoundSourceTypes273.restricted_exact]
 simp [PublicMeaning]

end Yulang.GeneralRebaseCompoundOwnerStep273
