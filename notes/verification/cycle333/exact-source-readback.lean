import Yulang.GeneralDeclarativeAlternativeMixedModels333
import Yulang.GeneralDeclarativeAlternativeCurrentCase333
import Yulang.GeneralDeclarativeAlternativeRangeCase333

#print axioms Yulang.GeneralDeclarativeAlternativeMixedDecl333.checked
#print axioms Yulang.GeneralDeclarativeAlternativeMixedCase333.independent_endpoints
#print axioms Yulang.GeneralDeclarativeAlternativeMixedCase333.actual_modes
#print axioms Yulang.GeneralDeclarativeAlternativeMixedCase333.exact_body
#print axioms Yulang.GeneralDeclarativeAlternativeMixedCase333.mixed_exact_receipt
#print axioms Yulang.GeneralDeclarativeAlternativeMixedModels333.declared_frame
#print axioms Yulang.GeneralDeclarativeAlternativeMixedModels333.actual_mixed_child

#check @Yulang.GeneralDeclarativeAlternativeReadComplete333.normalized_finite
#check @Yulang.GeneralDeclarativeAlternativeNamedHeads333.candidate_exact
#check @Yulang.GeneralDeclarativeAlternativeMixedReplay333.consume_current
#check @Yulang.GeneralDeclarativeAlternativeCurrentCase333.real_current_dictionary
#check @Yulang.GeneralDeclarativeAlternativeRangeCase333.exact_frame
#check @Yulang.GeneralDeclarativeAlternativeMixedModels333.actual_mixed_child

example :
    Yulang.GeneralDeclarativeAlternativeMixedCase333.child.arguments = [⟨15,3,16⟩] ∧
      Yulang.GeneralDeclarativeAlternativeMixedCase333.child.outputs = [⟨1,14⟩] :=
  ⟨rfl,rfl⟩

example :
    Yulang.GeneralDeclarativeAlternativeRangeCase333.actualChild.arguments = [⟨20,3,21⟩] :=
  rfl
