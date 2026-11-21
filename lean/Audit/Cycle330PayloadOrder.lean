import Yulang.GeneralDeclarativeRecordConsumption330
import Yulang.GeneralDeclarativeRecordInline330

namespace Yulang.Cycle330PayloadOrder
open GeneralDeclarativeRecordInline330 (fields payload)
open GeneralDeclarativeRecordConsumption330 (read_field)
open GeneralDeclarativeRecordPayloads330 (Field)

example : Field 7 fields payload := by
  apply read_field (keys := [8,7])
    (picked := [(8,.variable 4),(7,payload)]) rfl
  exact List.mem_cons_of_mem _ List.mem_cons_self

example : Field 8 fields (.variable 4) := by
  apply read_field (keys := [8,7])
    (picked := [(8,.variable 4),(7,payload)]) rfl
  exact List.mem_cons_self

#print axioms GeneralDeclarativeRecordConsumption330.lookup_iff
#print axioms GeneralDeclarativeRecordConsumption330.read_field
#print axioms GeneralDeclarativeRecordConsumption330.from_ordered_endpoints

end Yulang.Cycle330PayloadOrder
