import Std

/-!
# Inferred variant residuals

The row below is a finite support of (tag, payload-type) alternatives, not a
surface annotation grammar. Order and duplicate entries have no semantic force:
the theorems use membership. Unlike effect occurrences, value alternatives do
not carry handler barriers. Sources: spec/04-types.md §4.5 and traps.md T-variant.

These results characterize removal of resolved tags. They do not decide source
pattern exhaustiveness, guards, payload subtyping, or recursive open row solving.
-/

namespace Yulang.Variants

abbrev Row (Tag Payload : Type) := List (Tag × Payload)

/-- The alternatives delivered to a final residual arm. -/
def residual (handled : Tag → Bool) (row : Row Tag Payload) : Row Tag Payload :=
  row.filter (fun entry => !handled entry.1)

/-- The alternatives selected by the already-resolved tag arms. -/
def selected (handled : Tag → Bool) (row : Row Tag Payload) : Row Tag Payload :=
  row.filter (fun entry => handled entry.1)

/-- Extensional inclusion of finite alternative supports. -/
def Included (left right : Row Tag Payload) : Prop :=
  ∀ entry, entry ∈ left → entry ∈ right

theorem mem_residual (handled : Tag → Bool) (row : Row Tag Payload) (entry) :
    entry ∈ residual handled row ↔ entry ∈ row ∧ handled entry.1 = false := by
  simp [residual]

theorem mem_selected (handled : Tag → Bool) (row : Row Tag Payload) (entry) :
    entry ∈ selected handled row ↔ entry ∈ row ∧ handled entry.1 = true := by
  simp [selected]

theorem residual_included (handled : Tag → Bool) (row : Row Tag Payload) :
    Included (residual handled row) row := by
  intro entry h
  exact ((mem_residual handled row entry).mp h).1

theorem residual_excludes_handled (handled : Tag → Bool) (row : Row Tag Payload)
    (entry) (h : entry ∈ residual handled row) : handled entry.1 = false :=
  ((mem_residual handled row entry).mp h).2

/-- No unmatched tag or its payload is lost. -/
theorem partition (handled : Tag → Bool) (row : Row Tag Payload) (entry) :
    entry ∈ row ↔ entry ∈ selected handled row ∨ entry ∈ residual handled row := by
  rw [mem_selected, mem_residual]
  cases handled entry.1 <;> simp

theorem selected_residual_disjoint (handled : Tag → Bool) (row : Row Tag Payload)
    (entry) : ¬(entry ∈ selected handled row ∧ entry ∈ residual handled row) := by
  rw [mem_selected, mem_residual]
  cases handled entry.1 <;> simp

/-- The residual is the greatest part of the input avoiding all handled tags. -/
theorem residual_greatest (handled : Tag → Bool) (row candidate : Row Tag Payload)
    (hsub : Included candidate row)
    (hexcludes : ∀ entry, entry ∈ candidate → handled entry.1 = false) :
    Included candidate (residual handled row) := by
  intro entry h
  exact (mem_residual handled row entry).mpr ⟨hsub entry h, hexcludes entry h⟩

/-- It is also the least residual that retains every unmatched input alternative. -/
theorem residual_least (handled : Tag → Bool) (row candidate : Row Tag Payload)
    (hretains : ∀ entry, entry ∈ row → handled entry.1 = false → entry ∈ candidate) :
    Included (residual handled row) candidate := by
  intro entry h
  rcases (mem_residual handled row entry).mp h with ⟨hin, hnot⟩
  exact hretains entry hin hnot

/-- A constraint on the residual is exactly a constraint on unmatched input tags. -/
theorem residual_constraint_iff (handled : Tag → Bool) (row target : Row Tag Payload) :
    Included (residual handled row) target ↔
      ∀ entry, entry ∈ row → handled entry.1 = false → entry ∈ target := by
  constructor
  · intro h entry hin hnot
    exact h entry ((mem_residual handled row entry).mpr ⟨hin, hnot⟩)
  · exact residual_least handled row target

theorem residual_idempotent (handled : Tag → Bool) (row : Row Tag Payload) :
    residual handled (residual handled row) = residual handled row := by
  induction row with
  | nil => rfl
  | cons entry rest ih =>
    cases h : handled entry.1 <;> simp [residual, h] at ih ⊢ <;> exact ih

/-- Removing two resolved tag sets commutes; no effect stack weight is involved. -/
theorem residual_commute (first second : Tag → Bool) (row : Row Tag Payload) :
    residual first (residual second row) = residual second (residual first row) := by
  induction row with
  | nil => rfl
  | cons entry rest ih =>
    cases h₁ : first entry.1 <;> cases h₂ : second entry.1 <;>
      simp [residual, h₁, h₂] at ih ⊢ <;> exact ih

theorem residual_empty_iff (handled : Tag → Bool) (row : Row Tag Payload) :
    residual handled row = [] ↔ ∀ entry, entry ∈ row → handled entry.1 = true := by
  simp [residual]

/-- Payload substitution cannot resurrect a removed tag. -/
theorem residual_map_payload (handled : Tag → Bool) (f : Payload → Payload')
    (row : Row Tag Payload) :
    residual handled (row.map (fun entry => (entry.1, f entry.2))) =
      (residual handled row).map (fun entry => (entry.1, f entry.2)) := by
  induction row with
  | nil => rfl
  | cons entry rest ih =>
    cases h : handled entry.1 <;> simp [residual, h] at ih ⊢ <;> exact ih

example : residual (fun tag : String => tag == "str")
    [("str", "string"), ("num", "int")] = [("num", "int")] := by decide

example : residual (fun _ : String => true)
    [("str", "string"), ("num", "int")] = [] := by decide

end Yulang.Variants
