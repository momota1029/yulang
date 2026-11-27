import Yulang.GeneralDeclarativeI65I74PreviousOrdinaryMaterialBoundary465
import Yulang.GeneralDeclarativeNestedExample332
namespace Yulang.GeneralDeclarativeNativeMaterialBoundary465.Actual
open GeneralDeclarativeNestedExample332 (state pat interpretation supports uses actual_center)
open GeneralDeclarativeHead320 (State)
open GeneralDeclarationExamples (constructors)
open GeneralDeclarationPatterns (normalize)
open GeneralNominalCenteredHeadMatExpressions (translate)
open GeneralDeclarativeNestedMaterial332 (assemble)
open GeneralDeclarativeOpaqueNominal328 (point point_bounded)
open GeneralDeclarativeInlineMaterial331 (ordinary)
open GeneralDeclarativeOrigins321 (restriction)
open GeneralDeclarativeObserverGrowth330 (preserve)

def readOldAssembly : Option (State × List (Nat × GeneralDeclarativeWhere319.Capture)) := do
  let code ← translate constructors interpretation (normalize pat)
  assemble state (point 0) [] code (uses .actual)

theorem actual_old_allocates_two_fresh_names_in_order :
    (ordinary state (point 0) [] (uses .actual)).map (·.left) = [16,17] ∧
    (readOldAssembly.map fun pair =>
      (pair.1.equations.map (·.left), pair.2.map fun b => (b.1,b.2.center))) =
      some ([0,14,3,16,17,0],[(0,3),(3,11),(4,16),(1,17)]) := ⟨rfl,rfl⟩

theorem actual_old_allocations_are_not_available_sources (done : Nat → Prop)
    {out spans} (run : readOldAssembly = some (out,spans)) :
    ∃ grows : GeneralDeclarativeGrowth327.Extends state out,
      ∀ e ∈ ordinary state (point 0) [] (uses .actual),
        e ∈ out.equations ∧ e ∉ (restriction (preserve (supports done) grows)).equations := by
  obtain ⟨code,printed,actual⟩ := GeneralDeclarativeNestedDecode332.normalized_sound (actual_center done)
  have exact : assemble state (point 0) [] code (uses .actual) = some (out,spans) := by
    simpa [readOldAssembly,printed,Option.bind] using run
  obtain ⟨grows,_,missing⟩ := actual_old_assembly_keeps_allocations_and_available_sources_separate
      (point_bounded _ _) printed actual exact
  exact ⟨grows,missing⟩

#print axioms actual_old_allocates_two_fresh_names_in_order
#print axioms actual_old_allocations_are_not_available_sources
end Yulang.GeneralDeclarativeNativeMaterialBoundary465.Actual
