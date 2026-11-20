import Yulang.GeneralSourceMetadataBundleFixture291

/-! Exact domain of the old output-expression application, distinguished
from the bounded inspection translator and its pending cases. -/
namespace Yulang.GeneralSourceMetadataApplication291
open GeneralNominalCenteredHeadMatExpressions (Expr application application_complete)
open GeneralDeclarationPatterns (Constructors)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCenteredHeadWFSource (ConstructorUse)

theorem application_sound (c : Constructors) (i : Interpretation) (key : Nat)
    (args : List Expr) (result : Expr) (compiled : application c i key args = some result) :
    ConstructorUse c i key args.length := by
  unfold application at compiled
  cases info : c key with
  | none => rw [info] at compiled; cases compiled
  | some descriptor =>
    rw [info] at compiled
    change (if descriptor.parameters.length = args.length then _ else none) = some result at compiled
    by_cases proper : descriptor.parameters.length = args.length
    · rw [ite_eq_left proper] at compiled
      cases classify : i.primitives key with
      | some pk =>
        rw [classify] at compiled
        change (if descriptor.parameters = pk.parameters then some (.primitive pk args) else none) = some result at compiled
        by_cases acceptable : descriptor.parameters = pk.parameters
        · exact ⟨descriptor,info,proper,.inl ⟨pk,classify,acceptable⟩⟩
        · rw [ite_eq_right acceptable] at compiled
          cases compiled
      | none =>
        rw [classify] at compiled
        change (if i.invariantNominal key = true ∧ descriptor.parameters = List.replicate args.length .type
          then some (.nominal descriptor.name args) else none) = some result at compiled
        by_cases acceptable : i.invariantNominal key = true ∧
          descriptor.parameters = List.replicate args.length .type
        · exact ⟨descriptor,info,proper,.inr acceptable⟩
        · rw [ite_eq_right acceptable] at compiled
          cases compiled
    · rw [ite_eq_right proper] at compiled
      cases compiled

theorem application_exact (c : Constructors) (i : Interpretation) (key : Nat) (args : List Expr) :
    (∃ code, application c i key args = some code) ↔ ConstructorUse c i key args.length :=
  ⟨fun ⟨result,compiled⟩ => application_sound c i key args result compiled,application_complete⟩

end Yulang.GeneralSourceMetadataApplication291
