import Yulang.CommonRoleSourceIdentity

/-! Executable first-occurrence descent of coherent type valuations.
Effect components are not equated by the source identity constraints. -/
namespace Yulang.CommonRoleSourceDescent
open CommonRoleSourceIdentity
open Core.PresenceGeneration (Comp)

def representative (table : Table) (name : Nat) : Option (Slot table) :=
  (List.finRange table.length).find? (fun slot => source table slot == name)

theorem representative_source (table : Table) (name : Nat) (slot : Slot table)
    (found : representative table name = some slot) : source table slot = name := by
  have h := List.find?_some (show (List.finRange table.length).find?
    (fun candidate => source table candidate == name) = some slot from found)
  exact beq_iff_eq.mp h

theorem representative_exists (table : Table) (slot : Slot table) :
    ∃ first, representative table (source table slot) = some first := by
  have present : (representative table (source table slot)).isSome := by
    simp only [representative, List.find?_isSome]
    exact ⟨slot, List.mem_finRange slot, by simp⟩
  cases h : representative table (source table slot) with
  | none => simp [h] at present
  | some first => exact ⟨first, rfl⟩

def descend (table : Table) (values : Slot table → Comp Common.model)
    (fallback : Common.Ty) (name : Nat) : Common.Ty :=
  match representative table name with
  | none => fallback
  | some first => (values first).1

/-- Independent factorization relation, modulo Common's type equivalence. -/
def Factors (table : Table) (values : Slot table → Comp Common.model)
    (sourceValues : Nat → Common.Ty) : Prop :=
  ∀ slot, Common.Equivalent (values slot).1 (sourceValues (source table slot))

theorem descend_factors (table : Table) (values : Slot table → Comp Common.model)
    (fallback : Common.Ty) (coherent : Coherent table values) :
    Factors table values (descend table values fallback) := by
  intro slot
  obtain ⟨first, found⟩ := representative_exists table slot
  simp only [descend, found]
  exact coherent slot first (representative_source table _ first found).symm

theorem factors_coherent (table : Table) (values : Slot table → Comp Common.model)
    (sourceValues : Nat → Common.Ty) (factor : Factors table values sourceValues) :
    Coherent table values := by
  intro left right same
  have l := factor left
  have r := factor right
  rw [same] at l
  exact Common.equivalent_trans l (Common.equivalent_symm r)

theorem factorization_exact (table : Table) (values : Slot table → Comp Common.model) :
    Coherent table values ↔ ∃ sourceValues, Factors table values sourceValues := by
  constructor
  · intro coherent
    exact ⟨descend table values (.base .int), descend_factors table values _ coherent⟩
  · rintro ⟨sourceValues, factor⟩
    exact factors_coherent table values sourceValues factor

/-- Actual identity atoms are exactly the source-factorable occurrence valuations. -/
theorem atoms_factorization_exact (table : Table) (values : Slot table → Comp Common.model) :
    PresenceNormalForm.All Common.model values (atoms table) ↔
      ∃ sourceValues, Factors table values sourceValues := by
  rw [atoms_exact, factorization_exact]

/-- The fallback cannot affect any represented source identity, even without coherence. -/
theorem fallback_independent (table : Table) (values : Slot table → Comp Common.model)
    (a b : Common.Ty) (slot : Slot table) :
    descend table values a (source table slot) = descend table values b (source table slot) := by
  obtain ⟨first, found⟩ := representative_exists table slot
  simp only [descend, found]
  rfl

/-- Solver-facing statement: arbitrary old constraints coexist with a single
source valuation exactly when the real ordinary solver accepts identity extension. -/
theorem solver_factorization_exact (table : Table)
    (state : CommonRoleSettledConstraints.State table.length) :
    CommonRoleOpenPropagation.consistent (extend table state) = true ↔
      ∃ values : Slot table → Comp Common.model,
        PresenceNormalForm.All Common.model values state.atoms ∧
        ∃ sourceValues, Factors table values sourceValues := by
  rw [CommonRoleSourceIdentity.consistent_exact]
  exact exists_congr fun values => and_congr_right fun _ => factorization_exact table values

/-- Any two valid descents agree up to type equivalence on every used source;
no assertion about unused identities or effects is made. -/
theorem factor_unique_on_occurrence (table : Table)
    (values : Slot table → Comp Common.model) (left right : Nat → Common.Ty)
    (hl : Factors table values left) (hr : Factors table values right)
    (slot : Slot table) :
    Common.Equivalent (left (source table slot)) (right (source table slot)) :=
  Common.equivalent_trans (Common.equivalent_symm (hl slot)) (hr slot)

/-- A source-level type equation is equivalent to the same equation at every
occurrence of that identity. The occurrence witnessing presence is explicit. -/
theorem source_equation_exact (table : Table)
    (values : Slot table → Comp Common.model) (fallback target : Common.Ty)
    (coherent : Coherent table values) (slot : Slot table) :
    Common.Equivalent (descend table values fallback (source table slot)) target ↔
      ∀ other, source table other = source table slot →
        Common.Equivalent (values other).1 target := by
  have fact := descend_factors table values fallback coherent
  constructor
  · intro equation other same
    have h := fact other
    rw [same] at h
    exact Common.equivalent_trans h equation
  · intro all
    exact Common.equivalent_trans (Common.equivalent_symm (fact slot)) (all slot rfl)

end Yulang.CommonRoleSourceDescent
