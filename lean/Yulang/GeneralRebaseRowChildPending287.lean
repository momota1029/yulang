import Yulang.GeneralRebaseRowChildSource287

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 24000
set_option maxHeartbeats 10000000
namespace Yulang.GeneralRebaseRowChildPending287
open GeneralRebaseRowChildSource287
open GeneralNominalRecursiveCandidates (arguments report)
open GeneralNominalVersionedCandidates231 (Prepared Failed InspectionPending)
open GeneralNominalVersionedCandidates231 (inputs)
open GeneralNominalRecursiveInspection (Finished)

theorem bounds (id : Nat) : arguments ctx (inputs (childAt id)) = some [(0,0)] := by
  change arguments ctx (inputs (childAt 0)) = some [(0,0)]
  decide +kernel

theorem blocked : (report ctx destructing [(0,0)]).blocked = [(0,0)] := by decide +kernel

theorem no_conflict : (report ctx destructing [(0,0)]).conflicts = [] := by decide +kernel

theorem no_prepared (id : Nat) : ¬ Prepared (registry false) ctx (childAt id) destructing := by
  rintro ⟨_,_,coords,found,_,done,_⟩
  cases Option.some.inj ((bounds id).symm.trans found)
  have impossible := done.1
  rw [blocked] at impossible
  cases impossible

theorem no_failed (id : Nat) : ¬ Failed (registry false) ctx (childAt id) destructing := by
  rintro ⟨_,coords,found,_,clear,_,_⟩
  cases Option.some.inj ((bounds id).symm.trans found)
  rw [blocked] at clear
  cases clear

theorem pending (id : Nat) : InspectionPending (registry false) ctx (childAt id) :=
  ⟨known_child id,destructing,List.mem_cons_of_mem _ List.mem_cons_self,rfl,no_failed id,no_prepared id⟩

theorem whole_observed : Finished (report ctx opaqueChild [(0,0)]) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

end Yulang.GeneralRebaseRowChildPending287
