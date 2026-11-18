import Yulang.GeneralPresenceOrderedExpansion249
/-! Finite support certificates for expanded targets. Failure is only failure
of this sufficient certificate, never a new source rejection rule. -/
namespace Yulang.GeneralPresenceProtectionCheck249
open GeneralPresenceDefinitionRewrite244

def Protected (reads : List Nat) (entries : List (Entry Nat)) : Prop :=
 ∀ name ∈ reads, ∀ entry ∈ entries, entry.1 ≠ name

def check (reads : List Nat) (entries : List (Entry Nat)) : Bool :=
 reads.all fun name => entries.all fun entry => decide (entry.1 ≠ name)

theorem check_exact (reads : List Nat) (entries : List (Entry Nat)) :
 check reads entries = true ↔ Protected reads entries := by
 simp [check,Protected,List.all_eq_true]

def NewProtected (reads : List Nat) (old fresh : List (Entry Nat)) : Prop :=
 ∀ entry ∈ fresh, (∀ original ∈ old, original.1 ≠ entry.1) →
   ∀ name ∈ reads, entry.1 ≠ name

theorem protected_of_new (reads : List Nat) (old fresh : List (Entry Nat))
 (oldClosed : Protected reads old) (newProtected : NewProtected reads old fresh) :
 Protected reads fresh := by
 intro name member entry present
 by_cases found : ∃ original ∈ old, original.1 = entry.1
 · obtain ⟨original,oldMember,equal⟩ := found
   rw [← equal]
   exact oldClosed name member original oldMember
 · exact newProtected entry present
     (fun original oldMember equal => found ⟨original,oldMember,equal⟩) name member

theorem new_protected_of_protected (reads : List Nat) (old fresh : List (Entry Nat))
 (protectedReads : Protected reads fresh) : NewProtected reads old fresh :=
 fun entry present _ name member => protectedReads name member entry present

theorem new_exact (reads : List Nat) (old fresh : List (Entry Nat)) (closed : Protected reads old) :
 Protected reads fresh ↔ NewProtected reads old fresh :=
 ⟨new_protected_of_protected reads old fresh,protected_of_new reads old fresh closed⟩

theorem append_exact (left right : List Nat) (entries : List (Entry Nat)) :
 Protected (left ++ right) entries ↔ Protected left entries ∧ Protected right entries := by
 simp [Protected,List.mem_append,or_imp,forall_and]

theorem above_bound (reads : List Nat) (entries : List (Entry Nat))
 (above : ∀ entry ∈ entries, reads.foldr max 0 < entry.1) : Protected reads entries := by
 intro name member entry present equal
 have bound : name ≤ reads.foldr max 0 := by
   clear above
   induction reads with
   | nil => cases member
   | cons head tail ih =>
     rcases List.mem_cons.mp member with rfl | rest
     · exact Nat.le_max_left _ _
     · exact Nat.le_trans (ih rest) (Nat.le_max_right _ _)
 have high := above entry present
 rw [equal] at high
 exact (Nat.not_le_of_gt high) bound
end Yulang.GeneralPresenceProtectionCheck249
