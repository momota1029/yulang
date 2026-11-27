import Yulang.GeneralDeclarativeI65I74WrittenBinderCoordinates466
import Yulang.GeneralDeclarativeNestedExample332
namespace Yulang.C466WrittenBinderCoordinates
open GeneralDeclarationPatterns (normalize)
open GeneralDeclarativeNestedExample332 (pat)
theorem actual_legacy_fixture_capture_sites_not_confused_between_nested_and_outer_tail :
    (bindersAt (normalize pat))[2]? = some ([.payload,.variant,.app 1,.tail],4) ∧
    (bindersAt (normalize pat))[3]? = some ([.tail],1) ∧
    bindersAt (normalize pat) = bindersAt pat := by
  decide +kernel


#print axioms written_binder_indices_keep_the_old_order_and_multiplicity
#print axioms each_binder_address_records_a_literal_occurrence
#print axioms an_actual_ordinary_capture_index_links_to_an_exact_literal_binder_site
#print axioms actual_legacy_fixture_capture_sites_not_confused_between_nested_and_outer_tail
#print axioms a_supported_old_materialization_read_pins_the_normalized_written_capture
end Yulang.C466WrittenBinderCoordinates
