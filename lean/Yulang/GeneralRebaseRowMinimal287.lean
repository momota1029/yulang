import Yulang.GeneralRebaseRowPublic287

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 14500000
namespace Yulang.GeneralRebaseRowMinimal287
open GeneralRebaseRowChildSource287 (before model R F)
open GeneralRebaseRowChildRaw287 (SourceCheck OutputCheck fullRow exact_source before_exact changeAmbient)
open GeneralRebaseRowParentFrame287 (after after_exact)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseRowParentOutput287 (replaceOutput)
open CommonNominalFullCarrier

def Agrees (types rows : List Nat) (a b : Assignment) : Prop :=
  (∀ n ∈ types, (a n).1 = (b n).1) ∧ ∀ n ∈ rows, (a n).2 = (b n).2

def Determines (types rows : List Nat) (claims : Assignment → Prop) : Prop :=
  ∀ a b, Agrees types rows a b → (claims a ↔ claims b)

theorem supports_before {types rows : List Nat} (zero : 0 ∈ types) (one : 1 ∈ types) (row : 0 ∈ rows) :
    Determines types rows (Models before) := by
  intro a b agrees
  rw [before_exact,before_exact]
  unfold SourceCheck
  rw [agrees.1 0 zero,agrees.1 1 one,agrees.2 0 row]

theorem supports_after (choice : Bool) {types rows : List Nat} (zero : 0 ∈ types) (one : 1 ∈ types)
    (two : 2 ∈ types) (row : 0 ∈ rows) : Determines types rows (Models (after choice)) := by
  intro a b agrees
  rw [after_exact,after_exact]
  unfold OutputCheck SourceCheck
  rw [agrees.1 0 zero,agrees.1 1 one,agrees.1 2 two,agrees.2 0 row]

def changeType (a : Assignment) (k : Nat) : Assignment :=
  fun n => (if n = k then .base .int else (a n).1,(a n).2)

theorem type_mismatch {name : Nat} {args : List Argument} :
    ¬ Equivalent (.base .int) (nominal name args) := by
  intro same
  have tags := GeneralDictionaryInspectionHeads215.tag_subtype
    (GeneralDictionaryInspectionHeads215.tagged_scalar .int)
    (GeneralDictionaryInspectionHeads215.tagged_nominal name args) same.1
  cases tags

theorem source_loss (k : Nat) (small : k ≤ 1) :
    ¬ Models before (changeType (model Common.rowEmpty) k) := by
  intro good
  have source := (before_exact _).mp good
  have choices : k = 0 ∨ k = 1 := by omega
  rcases choices with rfl|rfl
  · exact type_mismatch source.1
  · exact type_mismatch source.2

theorem after_loss (choice : Bool) (k : Nat) (small : k ≤ 2) :
    ¬ Models (after choice) (changeType (model Common.rowEmpty) k) := by
  intro good
  have all := (after_exact choice _).mp good
  by_cases first : k ≤ 1
  · exact source_loss k first ((before_exact _).mpr all.1)
  · have two : k = 2 := by omega
    subst k
    exact type_mismatch all.2

theorem missed_type {types rows : List Nat} (k : Nat) (missing : k ∉ types) (a : Assignment) :
    Agrees types rows a (changeType a k) := by
  refine ⟨?_,fun _ _ => rfl⟩
  intro n present
  have other : n ≠ k := fun eq => missing (eq ▸ present)
  unfold changeType
  simp [other]

theorem missed_row {types rows : List Nat} (missing : 0 ∉ rows) (a : Assignment) :
    Agrees types rows a (changeAmbient a 0 fullRow) := by
  refine ⟨fun _ _ => rfl,?_⟩
  intro n present
  have other : n ≠ 0 := fun eq => missing (eq ▸ present)
  unfold changeAmbient
  simp [other]

theorem before_minimal (types rows : List Nat) :
    Determines types rows (Models before) ↔ 0 ∈ types ∧ 1 ∈ types ∧ 0 ∈ rows := by
  constructor
  · intro claim
    have need (k : Nat) (hk : k ≤ 1) : k ∈ types := by
      apply Classical.byContradiction
      intro missing
      exact source_loss k hk ((claim _ _ (missed_type k missing _)).mp
        (GeneralRebaseRowChildSource287.before_model Common.rowEmpty))
    refine ⟨need 0 (by decide),need 1 (by decide),?_⟩
    apply Classical.byContradiction
    intro missing
    have h := GeneralRebaseRowChildRaw287.ambient_boundary
    exact h.2.2 ((claim _ _ (missed_row missing _)).mp h.2.1)
  · rintro ⟨a,b,r⟩
    exact supports_before a b r

theorem after_minimal (choice : Bool) (types rows : List Nat) :
    Determines types rows (Models (after choice)) ↔
    0 ∈ types ∧ 1 ∈ types ∧ 2 ∈ types ∧ 0 ∈ rows := by
  constructor
  · intro claim
    have need (k : Nat) (hk : k ≤ 2) : k ∈ types := by
      apply Classical.byContradiction
      intro missing
      exact after_loss choice k hk ((claim _ _ (missed_type k missing _)).mp
        (GeneralRebaseRowParentFrame287.after_model choice Common.rowEmpty))
    refine ⟨need 0 (by decide),need 1 (by decide),need 2 (by decide),?_⟩
    apply Classical.byContradiction
    intro missing
    have h := GeneralRebaseRowChildRaw287.ambient_boundary
    have claimed := (claim _ _ (missed_row missing _)).mp
      (GeneralRebaseRowParentFrame287.after_model choice Common.rowEmpty)
    exact h.2.2 ((before_exact _).mpr ((after_exact choice _).mp claimed).1)
  · rintro ⟨a,b,c,d⟩
    exact supports_after choice a b c d

theorem canonical_minimal (choice : Bool) (types rows : List Nat) :
    Determines types rows (fun m => Models (after choice) (replaceOutput m)) ↔
      0 ∈ types ∧ 1 ∈ types ∧ 0 ∈ rows := by
  have same (m : Assignment) : Models (after choice) (replaceOutput m) ↔ Models before m :=
    (after_exact choice _).trans ((GeneralRebaseRowChildRaw287.complete_check m).trans (before_exact m).symm)
  rw [← before_minimal]
  exact ⟨fun h a b obs => (same a).symm.trans ((h a b obs).trans (same b)),
     fun h a b obs => (same a).trans ((h a b obs).trans (same b).symm)⟩

end Yulang.GeneralRebaseRowMinimal287
