import Yulang.GeneralNominalPacketSupport249
import Yulang.GeneralNominalRebaseClassView243
namespace Yulang.GeneralNominalClassSupport249
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
open GeneralNominalRebaseClassView243

def support (view : View) : List Nat := GeneralNominalPacketSupport249.equationReads view.equations ++
 GeneralPresenceConsumerSupport246.listTypedReads view.equalities

theorem holds_iff (view : View) (first last : Assignment)
 (rows : ∀ n, (first n).2 = (last n).2)
 (types : ∀ n ∈ support view, (first n).1 = (last n).1) : view.Holds first ↔ view.Holds last :=
 and_congr (GeneralNominalPacketSupport249.equations_iff view.equations first last rows
   (fun n h => types n (List.mem_append_left _ h)))
   (GeneralPresenceConsumerSupport246.all_iff model first last rows view.equalities
     (fun n h => types n (List.mem_append_right _ h)))
end Yulang.GeneralNominalClassSupport249
