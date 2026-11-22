import Yulang.GeneralStoppedLower335
import Yulang.GeneralStoppedOrdinarySite335

#print axioms Yulang.GeneralStoppedShape335.descriptor_semantics
#print axioms Yulang.GeneralStoppedShape335.head_semantics
#print axioms Yulang.GeneralStoppedLower335.collect_exact
#print axioms Yulang.GeneralStoppedLower335.exact_models
#print axioms Yulang.GeneralStoppedOrdinarySite335.each_argument
#print axioms Yulang.GeneralStoppedOrdinarySite335.output_targets
#print axioms Yulang.GeneralStoppedOrdinarySite335.retained_order

example : Yulang.GeneralStoppedShape335.point ([.type ((0 : Fin 2),(1 : Fin 2))]) = none := rfl
example : Yulang.GeneralStoppedShape335.point ([.row ((0 : Fin 2),(0 : Fin 2))]) = none := rfl
