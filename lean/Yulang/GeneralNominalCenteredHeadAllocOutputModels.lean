import Yulang.GeneralNominalCenteredHeadAllocAllocation
import Yulang.GeneralNominalCenteredModelExtension

/-! Every private child-output cell can receive its own semantic value.
The construction preserves all other allocation purposes, including shared
output binders, and every source identity below the persistent seed. -/
namespace Yulang.GeneralNominalCenteredHeadAllocOutputModels
open GeneralDeclarations GeneralNominalCenteredHeadAllocAllocation
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Ty)

structure Producer (declaration : Declaration) where
  clause : Clause
  equation : Equation
  clause_mem : clause ∈ declaration.requirements
  equation_mem : equation ∈ clause.outputs

def target (seed invocation : Nat) (producer : Producer declaration) : Nat :=
  GeneralNominalIdentities.source seed
    (outputKey invocation declaration.id producer.clause.id producer.equation.id)

private theorem unique_key (key : α → Nat) (xs : List α) (unique : (xs.map key).Nodup)
    (one : a ∈ xs) (two : b ∈ xs) (equal : key a = key b) : a = b := by
  induction xs with
  | nil => cases one
  | cons head rest ih =>
      have pair := List.nodup_cons.mp unique
      rcases List.mem_cons.mp one with rfl | member
      · rcases List.mem_cons.mp two with rfl | member
        · rfl
        · exact False.elim (pair.1 (List.mem_map.mpr ⟨b,member,equal.symm⟩))
      · rcases List.mem_cons.mp two with rfl | other
        · exact False.elim (pair.1 (List.mem_map.mpr ⟨a,member,equal⟩))
        · exact ih pair.2 member other

theorem target_injective (identified : declaration.Identified) :
    Function.Injective (target (declaration := declaration) seed invocation) := by
  intro first last equal
  have keys := (GeneralNominalIdentities.source_identity seed _ _).mp equal
  have pair := congrArg (fun key : GeneralNominalIdentities.Origin => key.2.2.2.1) keys
  have parts := GeneralNominalCenteredHeadAllocEncoding.equation_key.mp pair
  have clauses := unique_key Clause.id declaration.requirements identified.1
    first.clause_mem last.clause_mem parts.1
  have equations := unique_key Equation.id first.clause.outputs
    (identified.2.2.2.2 first.clause first.clause_mem)
    first.equation_mem (clauses.symm ▸ last.equation_mem) parts.2
  cases first
  cases last
  cases clauses
  cases equations
  rfl

noncomputable def fill (previous : Assignment) (seed invocation : Nat)
    (values : Producer declaration → Ty) : Assignment := by
  classical
  exact fun identity => if found : ∃ producer, target seed invocation producer = identity then
    (values (Classical.choose found),(previous identity).2) else previous identity

theorem fill_value (identified : declaration.Identified) (previous : Assignment)
    (values : Producer declaration → Ty) (producer : Producer declaration) :
    (fill previous seed invocation values (target seed invocation producer)).1 = values producer := by
  classical
  unfold fill
  rw [dite_eq_left ⟨producer,rfl⟩]
  rw [target_injective identified (Classical.choose_spec
    (show ∃ other, target seed invocation other = target seed invocation producer from ⟨producer,rfl⟩))]

theorem fill_outside (previous : Assignment) (values : Producer declaration → Ty)
    (absent : ∀ producer : Producer declaration, target seed invocation producer ≠ identity) :
    fill previous seed invocation values identity = previous identity := by
  classical
  unfold fill
  rw [dite_eq_right (by rintro ⟨producer,equal⟩; exact absent producer equal)]

theorem fill_below_seed (previous : Assignment) (values : Producer declaration → Ty)
    (below : identity ≤ seed) : fill previous seed invocation values identity = previous identity := by
  apply fill_outside
  intro producer equal
  have above := GeneralNominalIdentities.source_above_seed seed
    (outputKey invocation declaration.id producer.clause.id producer.equation.id)
  change seed < target seed invocation producer at above
  omega

theorem fill_other_purpose (previous : Assignment) (values : Producer declaration → Ty)
    (different : purpose ≠ 5) :
    fill previous seed invocation values
        (GeneralNominalIdentities.source seed (other,key,purpose,owner,position)) =
      previous (GeneralNominalIdentities.source seed (other,key,purpose,owner,position)) := by
  apply fill_outside
  intro producer equal
  have keys := (GeneralNominalIdentities.source_identity seed _ _).mp equal
  exact different (congrArg (fun key : GeneralNominalIdentities.Origin => key.2.2.1) keys).symm

theorem source_extension (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (previous : Assignment) (valid : GeneralNominalState.Models context.state previous)
    (values : Producer declaration → Ty) (identified : declaration.Identified) :
    ∃ extended, GeneralNominalState.Models context.state extended ∧
      (∀ identity ∈ GeneralNominalState.sources context.state, extended identity = previous identity) ∧
      (∀ producer, (extended (target context.state.seed invocation producer)).1 = values producer) ∧
      ∀ other key owner position,
        extended (GeneralNominalIdentities.source context.state.seed (other,key,2,owner,position)) =
          previous (GeneralNominalIdentities.source context.state.seed (other,key,2,owner,position)) := by
  let extended := fill previous context.state.seed invocation values
  have kept : ∀ identity ∈ GeneralNominalState.sources context.state, extended identity = previous identity :=
    fun identity member => fill_below_seed previous values (source.below_seed identity member)
  exact ⟨extended,GeneralNominalCenteredModelExtension.source_models_same context.state
    (fun identity member => (kept identity member).symm) valid,kept,
    fill_value identified previous values,
    fun _ _ _ _ => fill_other_purpose previous values (by decide)⟩

end Yulang.GeneralNominalCenteredHeadAllocOutputModels
