import Yulang.GeneralDeclarativeI65I74PreviousOrdinaryMaterialBoundary465
import Yulang.GeneralDeclarativeInlineGround331
import Yulang.GeneralDeclarativeI65I74NativeProducerNoField465

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeNativeMaterialBoundary465.Certified466
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeNestedMaterial332 (assemble)
open GeneralDeclarativeOrigins321 (restriction)
open GeneralDeclarativeObserverGrowth330 (preserve)
open GeneralDeclarativeInlineMaterial331 (ordinary)
open GeneralNominalCenteredHeadMatExpressions (translate)
open GeneralDeclarationPatterns (normalize)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativeInlineGround331 (sourcesOnly Native certify derived_backed origin_path)
open GeneralDeclarativeInlineTrace331 (Read)
open GeneralDeclarativeInlineLineage331 (Trail)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeHead320 (Equation Models)
open GeneralDeclarativeInlineMaterial331 (named)

theorem actual_legacy_certificate_can_add_support_but_plain_transport_cannot
    {s : State} {old : Supported s done}
    (box : Bounds s a) (printed : translate c i (normalize pattern) = some code)
    (ordinaryRead : Read (restriction old) .actual (.variable a.center) code checked)
    (sourceRead : Read (restriction (sourcesOnly old)) .actual (.variable a.center) code checked)
    (runs : assemble s a fixed code checked = some (out,spans)) :
    ∃ grows : GeneralDeclarativeGrowth327.Extends s out,
      ∃ emitted : ordinary s a fixed checked ⊆ out.equations,
        (∀ m, Models out m ↔ Models (named s a fixed checked) m) ∧
        ∀ row ∈ ordinary s a fixed checked,
          row ∉ (restriction (preserve old grows)).equations ∧
          row ∈ (restriction (certify old grows a fixed checked emitted)).equations ∧
          ∃ loc ∈ checked, row.right = loc.term ∧ (∀ n, loc.term ≠ .variable n) ∧
            Trail (restriction (sourcesOnly old)) (.variable a.center) loc.term := by
  obtain ⟨holds,_,emitted,_,same⟩ :=
    GeneralDeclarativeNestedMaterial332.computed_frame box printed ordinaryRead runs
  refine ⟨holds.1,emitted,same,fun row occurs => ?_⟩
  have native : Native old a fixed checked row := ⟨occurs,code,sourceRead⟩
  exact ⟨fun leak => a_fresh_ordinary_allocation_has_no_older_available_source_origin (p := old) occurs
      ((GeneralDeclarativeObserverGrowth330.backed_same old holds.1 row).mp leak),
    derived_backed holds.1 emitted native,origin_path sourceRead occurs⟩

open GeneralDeclarativeI65.I72
open PreparedDeclarations463
open Checker408 (Problem)
open NativeProducer465.InlineBoundary

theorem legacy_supported_proof_does_not_recover_discarded_native_ledger
    {p : Problem} (checked : CheckedTable p.state.core.current) (w : HeadFieldWire p)
    (empty : p.state.core.origins = []) :
    readHeadField (p := p) checked w = none := by
  apply no_prechecked_field_receipt_on_a_sole_native360_origin_list (table := checked)
  intro _origin seen
  rw [empty] at seen
  cases seen

end Yulang.GeneralDeclarativeNativeMaterialBoundary465.Certified466
