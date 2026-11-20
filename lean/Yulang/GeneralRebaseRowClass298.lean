import Yulang.GeneralRebaseRowPacket298
import Yulang.GeneralNominalRebaseClassView243
namespace Yulang.GeneralRebaseRowClass298
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
open GeneralNominalRebaseClassView243

def support (view : View) : List Nat := GeneralRebaseRowPacket298.equationReads view.equations ++
 GeneralRebaseRowBasis298.listRowReads view.equalities

theorem holds_iff (view : View) (first last : Assignment)
 (types : ∀ n, (first n).1 = (last n).1)
 (rows : ∀ n ∈ support view, (first n).2 = (last n).2) : view.Holds first ↔ view.Holds last :=
 and_congr (GeneralRebaseRowPacket298.equations_iff view.equations first last types
   (fun n h => rows n (List.mem_append_left _ h)))
   (GeneralRebaseRowBasis298.all_iff model first last types view.equalities
     (fun n h => rows n (List.mem_append_right _ h)))
end Yulang.GeneralRebaseRowClass298
