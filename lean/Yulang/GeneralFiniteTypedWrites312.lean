import Yulang.GeneralNominalVersionedExpressionFrame236

set_option backward.isDefEq.respectTransparency false
/-! Solve a finite typed write table after evaluating every right-hand side
in a protected assignment. Repeated targets must denote equivalent types,
not syntactically equal ones. No new row assignment is chosen. -/
namespace Yulang.GeneralFiniteTypedWrites312
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredFrame179 (Agree)

abbrev Write := Nat × Ty

def Holds (m : Assignment) (entry : Write) : Prop :=
  Equivalent (m entry.1).1 entry.2

def Coherent (rows : List Write) : Prop :=
  ∀ a ∈ rows, ∀ b ∈ rows, a.1 = b.1 → Equivalent a.2 b.2

def Protected (rows : List Write) (pool : List Nat) (m : Assignment) : Prop :=
  ∀ row ∈ rows, row.1 ∈ pool → Holds m row

def applyWrites (rows : List Write) (pool : List Nat) (base : Assignment) : Assignment :=
  fun n => if n ∈ pool then base n else
    match rows.find? (fun row => row.1 == n) with
    | none => base n
    | some row => (row.2,(base n).2)

theorem reflexive (ty : Ty) : Equivalent ty ty := ⟨subtype_refl _,subtype_refl _⟩

theorem symmetric {a b : Ty} (equal : Equivalent a b) : Equivalent b a := ⟨equal.2,equal.1⟩

theorem transitive {a b c : Ty} (one : Equivalent a b) (two : Equivalent b c) : Equivalent a c :=
  ⟨subtype_trans one.1 two.1,subtype_trans two.2 one.2⟩

theorem preserved (rows : List Write) (pool : List Nat) (base : Assignment) :
    Agree pool base (applyWrites rows pool base) := by
  intro n member
  simp [applyWrites,member]

theorem rows_unchanged (rows : List Write) (pool : List Nat) (base : Assignment) (n : Nat) :
    (applyWrites rows pool base n).2 = (base n).2 := by
  unfold applyWrites
  split <;> first | rfl | split <;> rfl

theorem solves (rows : List Write) (pool : List Nat) (base : Assignment)
    (coherent : Coherent rows) (fixed : Protected rows pool base) :
    ∀ row ∈ rows, Holds (applyWrites rows pool base) row := by
  intro row found
  by_cases within : row.1 ∈ pool
  · unfold Holds
    rw [← preserved rows pool base _ within]
    exact fixed row found within
  · have hit : (rows.find? (fun prior => prior.1 == row.1)).isSome :=
      List.find?_isSome.mpr ⟨row,found,by simp⟩
    cases lookup : rows.find? (fun prior => prior.1 == row.1) with
    | none => simp [lookup] at hit
    | some entry =>
      have member := List.mem_of_find?_eq_some lookup
      have flag : (entry.1 == row.1) = true := List.find?_some (p := fun prior : Write => prior.1 == row.1) lookup
      have same : entry.1 = row.1 := beq_iff_eq.mp flag
      simpa only [Holds,applyWrites,within,ite_false,lookup] using coherent entry member row found same

theorem exact (rows : List Write) (pool : List Nat) (base : Assignment) :
    (∃ m, Agree pool base m ∧ ∀ row ∈ rows, Holds m row) ↔
      Coherent rows ∧ Protected rows pool base := by
  constructor
  · rintro ⟨m,same,held⟩
    refine ⟨?_,?_⟩
    · intro a one b two atTarget
      have first := (held a one)
      have last := (held b two)
      unfold Holds at first last
      rw [atTarget] at first
      exact transitive (symmetric first) last
    · intro row member inside
      unfold Holds
      rw [same _ inside]
      exact held row member
  · rintro ⟨coherence,fixed⟩
    exact ⟨_,preserved rows pool base,solves rows pool base coherence fixed⟩

end Yulang.GeneralFiniteTypedWrites312
