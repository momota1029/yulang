import Yulang.GeneralDeclarativeI65I74PreviousCompoundProducerBoundary465
open Yulang.GeneralDeclarativeI65
open Yulang.GeneralDeclarativeI65.NativeProducer394Boundary465
#print axioms plain_endpoint_has_exact_recursive_source_fragment
#print axioms plain_arguments_have_exact_recursive_source_fragment
#print axioms plain_argument_has_exact_recursive_source_fragment
#print axioms existing_literal_write_projection_has_exact_source_fragment
#print axioms an_actual_associated_receipt_projects_iff_its_code_is_literal

example : (projectOldNativeLiteral394 41
    (.variant 7 (.nominal 12 [.valueExpression (.variable 3 19)]))).isSome = true := by rfl
example : projectOldNativeLiteral394 41
    (.variant 7 (.nominal 12 [.valueExpression (.record 8 (.variable 3 19) (.variable 4 20))])) = none := by rfl
example : projectOldNativeLiteral394 41
    (.variant 7 (.variable 3 19)) = none := by rfl
