import Yulang.GeneralDeclarativeWitnessScopedBindings359
import Yulang.GeneralDeclarativeWitnessActualOpenReceipts359

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 23000000
namespace Yulang.GeneralDeclarativeWitnessActualScopes359
open GeneralDeclarativeWitnessScopedBindings359 (FrameKey Frame slots attached)
open GeneralDeclarativeWitnessActualOpenReceipts359 (atRoot atChild)
open GeneralDeclarativeOpenFixtureSelection339 (rootSelection childSelection child)
open GeneralDeclarativeOpenFixtureBase339 (decl)
open GeneralDeclarativeExampleSource320 (leaf)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeWitnessNominalSource359 (Location)

def rootKey : FrameKey := ⟨[],decl.id,0⟩
def childKey : FrameKey := ⟨[0],leaf.id,1⟩
def rootFrame : Frame := ⟨rootKey,rootSelection.spans⟩
def childFrame : Frame := ⟨childKey,childSelection.spans⟩
def frames : List Frame := [rootFrame,childFrame]

theorem spans_from_same_current_compiler : rootFrame.locals = atRoot.spans ∧ childFrame.locals = (atChild child).spans :=
  ⟨rfl,rfl⟩

theorem actual_binder_zero_in_each :
    slots frames rootKey 0 = some ⟨13,14,15⟩ ∧
    slots frames childKey 0 = some ⟨19,14,20⟩ := by
  constructor <;> rfl

theorem exact_scope_not_same_center {p q : Capture}
    (root : slots frames rootKey 0 = some p) (child : slots frames childKey 0 = some q) :
    p.center = q.center ∧ p.lower ≠ q.lower ∧ p.upper ≠ q.upper := by
  have a := Option.some.inj (root.symm.trans actual_binder_zero_in_each.1)
  have b := Option.some.inj (child.symm.trans actual_binder_zero_in_each.2)
  cases a
  cases b
  decide

theorem distinct_frame_without_owner_gets_no_read :
    slots frames ⟨[0],decl.id,0⟩ 0 = none ∧ slots frames ⟨[],leaf.id,1⟩ 0 = none := by
  constructor <;> rfl

theorem duplicate_frame_not_first_hit :
    slots (rootFrame :: frames) rootKey 0 = none := rfl

theorem source_sites_do_not_go_by_binder_name :
    attached rootKey (.head decl.id 0 0) ∧ attached childKey (.head leaf.id 1 0) ∧
    ¬attached childKey (.head decl.id 0 0) ∧ ¬attached rootKey (.head leaf.id 1 0) := by decide

end Yulang.GeneralDeclarativeWitnessActualScopes359
