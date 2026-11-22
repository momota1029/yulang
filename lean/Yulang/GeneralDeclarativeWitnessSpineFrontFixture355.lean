import Yulang.GeneralDeclarativeWitnessSpineFront355
import Yulang.GeneralDeclarativeWitnessSpineDeepFixture355
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65000
set_option maxHeartbeats 75000000
namespace Yulang.GeneralDeclarativeWitnessSpineFrontFixture355
open GeneralDeclarativeWitnessSpineDeepSeed355 (root input second third fourth)
open GeneralDeclarativeWitnessSpineDeepFixture355 (data receipt)
open GeneralDeclarativeWitnessSpineFront355 (Source Site Wire read)
open GeneralDeclarativeWitnessCovariantWrittenState353 (Line)
open GeneralDeclarativeWitnessCovariantFixture353 (wire)
open GeneralDeclarativeWitnessSpineNode355 (Author)
open GeneralDeclarativeWitnessNominalSpine355 (Code)
open GeneralDeclarativeHead320 (State)

def row (n v : Nat) : Line := ⟨n,.variant 13 (.app 0 [.var v])⟩
def fromSite (a : Author) (l r : Nat) : Site :=
  ⟨a.authority,a.write,a.nextVersion,[row 30 7,row 31 8,row l l,row r r],a.keep,a.fallback⟩

def first : Site :=
  ⟨root.auth,1,8,[row 30 7,row 31 8,row 32 32,row 33 33],root.childKeep,root.childFallback⟩

def source : Source :=
  ⟨{input with rows := []},root.location,[row 30 7,row 31 8,row 20 10],
    [first,fromSite second.source 50 51,fromSite third.source 90 91,fromSite fourth.source 130 131]⟩

def code : Option (State × Wire) :=
  data.map (fun (s,top,rest) => (s,⟨⟨wire,2,2,.refl 10,.refl 10⟩,top.writer,
    .send ⟨[4,0],top.receiverHead,top.receiver⟩ rest,receipt⟩))

def test (p : Source := source) (edit : Wire → Wire := id) : Bool :=
  (code.map (fun (s,w) => (read p s (edit w)).isSome)).getD false

theorem independently_parsed_entire_five_node_tree : test = true := by decide +kernel

theorem root_cannot_fake_output_order :
    test source (fun w => {w with rootReceipt := {w.rootReceipt with trace := w.rootReceipt.trace.reverse}}) =
       false := by decide +kernel

theorem produced_row_not_an_independent_author_row :
    test {source with routes := {first with rows := first.rows ++ [row 10 10]}::source.routes.drop 1} =
      false := by decide +kernel

theorem ordinary_fallback_is_not_typed_authorship :
    test {source with written := [row 30 7,row 31 8,⟨20,.variant 13 (.app 1 [.var 10])⟩]} =
      false := by decide +kernel

theorem old_root_must_really_be_the_certified_author :
    test {source with location := {source.location with version := 6}} = false := by decide +kernel

end Yulang.GeneralDeclarativeWitnessSpineFrontFixture355
