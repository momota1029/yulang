import Yulang.GeneralDeclarativeWitnessRangeRelease355
import Yulang.GeneralDeclarativeWitnessTypedReemitModel354
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 40000
set_option maxHeartbeats 37000000
namespace Yulang.GeneralDeclarativeWitnessRangeReleaseFixture355
open GeneralDeclarativeWitnessRangeRelease355 (Released read)
open GeneralDeclarativeWitnessTypedReemit354 (Wire Linked decode)
open GeneralDeclarativeWitnessTypedRelease354 (Location Authority Stamp Key)
open GeneralDeclarativeWitnessTypedReemitFixture354 (seed)
open GeneralDeclarativeWitnessTypedRangeFixture354 (emitted)
open GeneralDeclarativeWitnessCovariantFixture353 (wire)
open GeneralDeclarativeWitnessTypedForestFixture354 (head)
open GeneralDeclarativeWitnessTypedReemitModel354 (model model_fits)
open GeneralDeclarativeHead320 (State Models)
open CommonNominalFullCarrier (Equivalent)

def whereAt : Location := ⟨[4,0],8⟩
def childVersion : Stamp := ⟨[4,0],3,93,8⟩
def right : Key := ⟨childVersion,0,4,10⟩
def authority : Authority := ⟨[childVersion],[right]⟩

def test (records : Authority := authority) (loc : Location := whereAt) (slot : Nat := 0) : Bool :=
  (emitted.map (fun (s,_,top,r) =>
    ((decode seed s ⟨wire,top,head false,r⟩).map (fun a => (read a records loc slot).isSome)).getD false)).getD false

theorem independently_authorized_next_write_at_ten : test = true := by decide +kernel

theorem old_parent_authority_is_not_new_child_authority : test seed.auth = false := by decide +kernel

theorem wrong_child_path : test authority {whereAt with path := [4,1]} = false := by decide +kernel

theorem wrong_incarnation : test authority {whereAt with version := 7} = false := by decide +kernel

theorem wrong_write_occurrence : test authority whereAt 1 = false := by decide +kernel

theorem wrong_target_even_if_equivalent :
    test {authority with released := [{right with target := 9}]} = false := by decide +kernel

theorem wrong_associated_name :
    test {authority with released := [{right with name := 1}]} = false := by decide +kernel

theorem two_simultaneous_incarnations :
    test {authority with active := [childVersion,{childVersion with version := 7}]} = false := by decide +kernel

theorem exact_release_has_a_model :
    ∃ (s : State) (w : Wire) (a : Linked seed s w) (r : Released a authority whereAt 0),
      Models s model ∧ w.receiver.trace[0]? = some (.typed r.body.indexed.typed.row) ∧
      Equivalent (model r.body.indexed.typed.row.valueName).1
        (.union (model a.writer.output.source.anchor.first.valueName).1
                (model a.writer.output.source.anchor.last.valueName).1) := by
  have yes := independently_authorized_next_write_at_ten
  unfold test at yes
  cases got : emitted with
  | none => rw [got] at yes; cases yes
  | some tuple =>
    obtain ⟨s,p,top,out⟩ := tuple
    let w : Wire := ⟨wire,top,head false,out⟩
    have actual : ((decode seed s w).map
        (fun a => (read a authority whereAt 0).isSome)).getD false = true := by
      simpa only [got,Option.map_some,Option.getD_some,w] using yes
    cases parsed : decode seed s w with
    | none => simp [parsed] at actual
    | some a =>
      cases rel : read a authority whereAt 0 with
      | none => simp [parsed,rel] at actual
      | some r =>
        have fit := model_fits got
        have all := GeneralDeclarativeWitnessRangeRelease355.exact_payload r model fit
        exact ⟨s,w,a,r,fit,all.2.1,all.2.2.2⟩

end Yulang.GeneralDeclarativeWitnessRangeReleaseFixture355
