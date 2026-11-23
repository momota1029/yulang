import Yulang.GeneralDeclarativeWitnessAuthorBeforeRelease361

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 67000
set_option maxHeartbeats 72000000
namespace Yulang.GeneralDeclarativeWitnessWholeFixture361
open GeneralDeclarativeWitnessAuthorBeforeRelease361 (Started Prefix Continued start beforeGrant close)
open GeneralDeclarativeWitnessMixedForwardFixture361 (PairOfNodes verify)
open GeneralDeclarativeWitnessMixedForwardChoice361 (Choice pick)
open GeneralDeclarativeWitnessNativeRelease360 (checkExactRelease)

structure Done (negative : Bool) where
  writer : Started negative
  ordinary : Prefix writer.root
  forward : Continued ordinary
  native : PairOfNodes forward.actual

def process (negative : Bool) : Option (Done negative) := do
  let s ← start negative
  let c ← beforeGrant s.root
  let parent ← pick s.root ⟨c.result.state,s.root.final.board⟩
  let n ← close c
  let leaf ← GeneralDeclarativeWitnessNestedFixture361.close n.actual
  let candidate : Choice s.root n.actual.ordinaryChild.final := by
    change Choice s.root ⟨n.actual.ordinaryChild.result.state,s.root.final.board⟩
    rw [n.sameBody]
    exact parent
  pure ⟨s,c,n,⟨candidate,leaf⟩⟩

def passes {negative} (f : Done negative) : Bool :=
  (decide (f.writer.root.prep.impl.id = 72 ∧ f.ordinary.prepared.impl.id = 73 ∧
    f.ordinary.result.fixed = [⟨105,.variable 61⟩]) && verify f.native) &&
    (checkExactRelease f.writer.root.final.board ⟨[]⟩ f.writer.root.typed.write).isNone

theorem actual_ordinary_before_authority_and_native_after (negative : Bool) :
    ((process negative).map passes).getD false = true := by
  cases negative <;> decide +kernel

end Yulang.GeneralDeclarativeWitnessWholeFixture361
