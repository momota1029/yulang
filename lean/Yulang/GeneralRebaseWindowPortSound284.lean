import Yulang.GeneralRebaseWindowPorts284

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseWindowPortSound284
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable)
open GeneralRebaseHistoryOrder282 (decode compatible)
open GeneralRebaseAliasMemo283 (Aliases assignment root)
open GeneralNominalCommonBridge (Assignment)
open GeneralPresenceModelCongruence245 (Compatible)
open CommonNominalFullCarrier (model Equivalent)
open GeneralRebaseLoopBase282 (equiv_trans)

theorem equation {s : State roles} (reach : Reachable reg focus s) (m : Assignment) (valid : Models s m)
    (memo : Aliases) (interp : Compatible model (assignment m memo) (decode s m))
    (id known : Nat) (based : root memo id = known) : Equivalent (m id).1 (m known).1 := by
  have h := (interp id).1
  change Equivalent (m (root memo id)).1 (decode s m id).1 at h
  rw [based] at h
  have close := equiv_trans h (compatible reach valid id).1
  exact ⟨close.2,close.1⟩

end Yulang.GeneralRebaseWindowPortSound284
