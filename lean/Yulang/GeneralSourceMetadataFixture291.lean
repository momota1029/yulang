import Yulang.GeneralSourceMetadataExport291

/-! Exact source rows for the existing row-bearing fixture. Only its
metadata description is re-expressed; the original journal is untouched. -/
namespace Yulang.GeneralSourceMetadataFixture291
open GeneralSourceMetadataRows291
open GeneralSourceMetadataValidation291 (check check_exact)
open GeneralSourceMetadataExport291 (Attached)
open GeneralObservedMetadataOverlay290 (overlay)
open GeneralRebaseRowChildSource287 (registry ctx raw interp)

abbrev source : Source :=
  ⟨.identityEmptyLayout,
    [⟨0,some ⟨[.type],0⟩,.invariant⟩,
     ⟨1,some ⟨[.type],1⟩,.unclassified⟩,
     ⟨5,some ⟨[.type,.type],5⟩,.unclassified⟩,
     ⟨6,some ⟨[.row],6⟩,.invariant⟩]⟩

theorem source_constructors : constructors source = GeneralRebaseRowChildSource287.constructors := by
  funext k
  by_cases a : k = 0 <;> by_cases b : k = 1 <;> by_cases c : k = 5 <;> by_cases d : k = 6 <;>
    simp_all [constructors,constructorRows,DefaultCode.decode,overlay,
      GeneralRebaseRowChildSource287.constructors,GeneralDeclarationExamples.constructors]

theorem source_interpretation : interpretation source = interp := by
  apply interpretation_ext
  · funext k
    simp [interpretation,primitives,source,primitiveRows,overlay,Class.primitiveValue]
  · funext k
    by_cases a : k = 0 <;> by_cases b : k = 1 <;> by_cases c : k = 5 <;> by_cases d : k = 6 <;>
      simp_all [interpretation,invariants,source,invariantRows,overlay,Class.invariantFlag]

theorem actual_attachment (choice : Bool) : Attached source source (registry choice) ctx :=
  ⟨rfl,source_constructors.symm,source_constructors.symm,source_interpretation.symm⟩

theorem actual_valid : check source = true := by decide +kernel

theorem actual_metadata (choice : Bool) : GeneralNominalCandidates.Metadata (registry choice) ctx :=
  GeneralSourceMetadataExport291.identical_checked_metadata (actual_attachment choice)
    ((check_exact source).mp actual_valid)

abbrev duplicate : Source := { source with rows := ⟨0,none,.unclassified⟩ :: source.rows }
abbrev incompatible : Source := { source with rows := ⟨9,some ⟨[.row],9⟩,.primitive .pair⟩ :: source.rows }
abbrev supportedPrimitive : Source := { source with rows := ⟨9,some ⟨[],9⟩,.primitive (.scalar .int)⟩ :: source.rows }

theorem validator_controls :
    check duplicate = false ∧ check incompatible = false ∧ check supportedPrimitive = true := by decide +kernel

end Yulang.GeneralSourceMetadataFixture291
