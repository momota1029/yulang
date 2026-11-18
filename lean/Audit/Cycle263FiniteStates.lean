import Yulang.GeneralRebaseFiniteStates263
open Yulang.GeneralRebaseStep258 Yulang.GeneralRebaseFiniteStates263
#print axioms Yulang.GeneralRebaseFiniteStates263.mem_of_sublist
#print axioms Yulang.GeneralRebaseFiniteStates263.complete
#print axioms Yulang.GeneralRebaseFiniteStates263.length
#print axioms Yulang.GeneralRebaseFiniteStates263.image_exact
#print axioms Yulang.GeneralRebaseFiniteStates263.forall_image_iff
#print axioms Yulang.GeneralRebaseFiniteStates263.heads_image_iff
example : (states [.binder 0,.binder 0]).map State.remaining =
  [[],[.binder 0],[.binder 0],[.binder 0,.binder 0]] := rfl
example : (states [.binder 0,.binder 1,.installed 2]).length = 8 := rfl
example : (states []).map State.remaining = [[]] := rfl
#check Yulang.GeneralRebaseFiniteStates263.heads_image_iff
