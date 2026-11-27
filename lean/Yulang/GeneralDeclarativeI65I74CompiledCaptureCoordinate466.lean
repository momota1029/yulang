import Yulang.GeneralDeclarativeI65I74OrdinaryCaptureOrdinals466
import Yulang.GeneralDeclarativeI65I74WrittenBinderCoordinates466

set_option backward.isDefEq.respectTransparency false
namespace Yulang.C466WrittenBinderCoordinates
open GeneralDeclarativeInlineTrace331 (Read)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeI65.I72.WrittenPattern460.PhysicalOrigin (atSource)
open GeneralDeclarationPatterns (normalize)
open GeneralDeclarativeNestedMaterial332 (assemble)
open OrdinaryOccurrenceStamp466
theorem original_normalized_capture_path_and_raw_allocated_row_share_one_old_compiler_read
    {s : GeneralDeclarativeHead320.State} {done : Nat → Prop} {old : Supported s done}
    {c interpretation p code a fixed used out spans i target site}
    {original : GeneralDeclarativeTermWalk322.Occurrence}
    (printed : GeneralNominalCenteredHeadMatExpressions.translate c interpretation (normalize p) = some code)
    (read : Read (restriction old) .actual (.variable a.center) code used)
    (built : assemble s a fixed code used = some (out,spans))
    (picked : existingCaptureJob s a fixed used i = some (target,site,original)) :
    out.equations[s.equations.length+i]? = some ⟨target,original.term⟩ ∧
      ∃ path, (bindersAt (normalize p))[site]? = some (path,original.binder) ∧
        atSource (normalize p) path = some (.var original.binder) := by
  obtain ⟨auth,raw⟩ := actual_allocation_receipt_links_exact_old_capture_to_exact_new_raw_ordinal built picked
  exact ⟨raw,a_supported_old_materialization_read_pins_the_normalized_written_capture printed read auth⟩
end Yulang.C466WrittenBinderCoordinates
