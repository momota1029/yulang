import Yulang.GeneralObservedMetadataOverlay290

/-! Closed representation witnesses for the finite-complete exception.
These independent witnesses are not obtained from a successful receipt. -/
namespace Yulang.GeneralObservedMetadataOverlayFixture290
open GeneralDeclarationPatterns (Constructors Constructor)
open GeneralRebaseRowChildSource287 (ctx raw interp constructors registry)
open GeneralRebaseReceiptCollision289 (removed)
open GeneralObservedMetadataControls290 (primitiveOutside)
open GeneralObservedMetadataOverlay290 (Data Represented overlay closed_world_iff)
open GeneralObservedMetadataScope290 (certify)
open GeneralNominalCandidates (Context Metadata)

abbrev sourceOverrides : List (Nat × Option Constructor) := [(6,some ⟨[.row],6⟩)]

abbrev sourceData : Data :=
  ⟨GeneralDeclarationExamples.constructors,sourceOverrides,sourceOverrides,[]⟩

theorem source_constructors :
    constructors = overlay sourceData.fallback sourceOverrides := by
  funext key
  simp [constructors,overlay]

theorem represents_source (choice : Bool) : Represented (registry choice) ctx sourceData :=
  ⟨source_constructors,source_constructors,rfl⟩

theorem actual_enlarged_check (choice : Bool) :
    certify (sourceData.extended [6,0]) (registry choice).constructors interp raw.constructors interp = .good := by
  cases choice <;> decide +kernel

theorem full_actual_metadata (choice : Bool) : Metadata (registry choice) ctx :=
  (closed_world_iff _ _ _ [6,0] (represents_source choice)).mpr (actual_enlarged_check choice)

abbrev removedData : Data := { sourceData with declared := (8,none) :: sourceOverrides }

theorem represents_removed : Represented (removed 8) ctx removedData := by
  refine ⟨?_,source_constructors,rfl⟩
  funext k
  unfold removed
  simp only [overlay]

theorem enlarged_detects_removed :
    certify (removedData.extended [6,0]) (removed 8).constructors interp raw.constructors interp =
      .disagreement := by decide +kernel

theorem removed_really_not_metadata : ¬ Metadata (removed 8) ctx := by
  intro metadata
  have accepted := (closed_world_iff _ _ _ [6,0] represents_removed).mp metadata
  rw [enlarged_detects_removed] at accepted
  cases accepted

abbrev primitiveData : Data := { sourceData with primitives := [(8,some .pair)] }
abbrev primitiveContext : Context := ⟨raw,primitiveOutside⟩

theorem represents_primitive : Represented (registry true) primitiveContext primitiveData :=
  ⟨source_constructors,source_constructors,rfl⟩

theorem enlarged_detects_primitive :
    certify (primitiveData.extended [6,0]) (registry true).constructors primitiveOutside raw.constructors primitiveOutside =
      .incompatiblePrimitive := by decide +kernel

theorem primitive_really_not_metadata : ¬ Metadata (registry true) primitiveContext := by
  intro metadata
  have accepted := (closed_world_iff _ _ _ [6,0] represents_primitive).mp metadata
  rw [enlarged_detects_primitive] at accepted
  cases accepted

end Yulang.GeneralObservedMetadataOverlayFixture290
