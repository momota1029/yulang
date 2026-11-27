import Yulang.GeneralDeclarativeI65I74OrdinarySourceGrounding466
import Yulang.GeneralDeclarativeNestedExample332

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeNativeMaterialBoundary465.Certified466
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
open GeneralDeclarativeInlineGround331 (sourcesOnly Native certify derived_backed origin_path)
open GeneralDeclarativeInlineTrace331 (Read)
def readOldAssembly : Option (State × List (Nat × GeneralDeclarativeWhere319.Capture)) := do
  let code ← translate constructors interpretation (normalize pat)
  assemble state (point 0) [] code (uses .actual)

theorem actual_nested_source_adds_an_old_supported_ordinary_certificate
    {out spans} (runs : readOldAssembly = some (out,spans)) :
    ∃ grows : GeneralDeclarativeGrowth327.Extends state out,
      ∃ emitted : ordinary state (point 0) [] (uses .actual) ⊆ out.equations,
        ∀ row ∈ ordinary state (point 0) [] (uses .actual),
          row ∉ (restriction (preserve (supports (fun _ => False)) grows)).equations ∧
          row ∈ (restriction (certify (supports (fun _ => False)) grows (point 0) [] (uses .actual) emitted)).equations := by
  obtain ⟨code,printed,actual⟩ := GeneralDeclarativeNestedDecode332.normalized_sound (actual_center (fun _ => False))
  have exact : assemble state (point 0) [] code (uses .actual) = some (out,spans) := by
    simpa [readOldAssembly,printed,Option.bind] using runs
  have strict : Read (restriction (sourcesOnly (supports (fun _ => False)))) .actual
      (.variable (point 0).center) code (uses .actual) := actual
  obtain ⟨grows,emitted,_models,received⟩ :=
    actual_legacy_certificate_can_add_support_but_plain_transport_cannot
      (point_bounded _ _) printed actual strict exact
  exact ⟨grows,emitted,fun row stored => ⟨(received row stored).1,(received row stored).2.1⟩⟩

theorem actual_legacy_support_growth_is_not_vacuous :
    ∃ out spans grows,
      ∃ emitted : ordinary state (point 0) [] (uses .actual) ⊆ out.equations,
      readOldAssembly = some (out,spans) ∧
      (ordinary state (point 0) [] (uses .actual)).map (·.left) = [16,17] ∧
      ∀ row ∈ ordinary state (point 0) [] (uses .actual),
        row ∈ (restriction (certify (supports (fun _ => False)) grows (point 0) [] (uses .actual) emitted)).equations := by
  have someOut : readOldAssembly.isSome = true := rfl
  cases run : readOldAssembly with
  | none => simp [run] at someOut
  | some result =>
    obtain ⟨out,spans⟩ := result
    obtain ⟨grows,emitted,good⟩ := actual_nested_source_adds_an_old_supported_ordinary_certificate run
    exact ⟨out,spans,grows,emitted,rfl,rfl,fun row mem => (good row mem).2⟩

#print axioms actual_legacy_certificate_can_add_support_but_plain_transport_cannot
#print axioms actual_nested_source_adds_an_old_supported_ordinary_certificate
#print axioms actual_legacy_support_growth_is_not_vacuous
#print axioms legacy_supported_proof_does_not_recover_discarded_native_ledger
end Yulang.GeneralDeclarativeNativeMaterialBoundary465.Certified466
