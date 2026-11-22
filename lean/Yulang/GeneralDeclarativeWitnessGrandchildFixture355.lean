import Yulang.GeneralDeclarativeWitnessGrandchildSeed355
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 50000
set_option maxHeartbeats 48000000
namespace Yulang.GeneralDeclarativeWitnessGrandchildFixture355
open GeneralDeclarativeWitnessGrandchildSeed355 (compilePair partialWire seed summarize)
open GeneralDeclarativeWitnessRangeReleaseFixture355 (authority whereAt childVersion right)
open GeneralDeclarativeWitnessGrandchild355 (Plan Wire decode)
open GeneralDeclarativeWitnessTypedOutput354 (Write)
open GeneralDeclarativeWitnessCovariantOrigin353 (Row Problem)
open GeneralDeclarativeWitnessCovariantHead352 (rawPattern)
open GeneralDeclarativeWitnessCovariantInterval353 (read)
open GeneralDeclarativeWitnessCompiler350 (execute printDemand)
open GeneralDeclarativeWitnessOrderedFixture350 (literalPlan)
open GeneralDeclarativeHead320 (State)

def authored : List Row := [⟨30,13,0,7⟩,⟨31,13,0,8⟩,⟨50,13,0,50⟩,⟨51,13,0,51⟩]

def plan : Plan := ⟨authority,whereAt,0,0,authored,[89],fun _ => ⟨10,10,10⟩⟩

def head : GeneralDeclarativeWitnessCovariantInterval353.Wire :=
  ⟨⟨0,rawPattern,0,1,4⟩,2,3,.constraint 18,.constraint 21⟩

/-- Ordinary receipt calculation for the actual emitted demand. The
executable checker does not trust the old row used to generate this
candidate: it decodes the second, independently addressed release. -/
def data (k : Nat) : Option (State × GeneralDeclarativeWitnessTypedReemit354.Wire × Wire) := do
  let p ← compilePair k
  let demand ← p.receiver.children[0]?
  let leaf : Problem := { p.context with
    stage := p.receiver.state
    rows := authored ++ [p.row]
    demand := demand
    keep := plan.keep
    fallback := plan.fallback }
  let ready ← read leaf head
  let result ← execute ready.ctx
  let wire ← partialWire p result.state
  let checked ← literalPlan result.state result.state
  pure (result.state,wire,⟨[4,0,0],head,⟨result.kids.map printDemand,result.fixed,checked⟩⟩)

def test (k : Nat := 10) (p : Plan := plan) (edit : Wire → Wire := id) : Bool :=
  ((data k).map fun (s,first,last) =>
    ((GeneralDeclarativeWitnessTypedReemit354.decode (seed k) s first).map fun a =>
      (decode a p (edit last)).isSome).getD false).getD false

def emittedAt (k n : Nat) : Bool :=
  ((compilePair k).map fun p =>
    p.receiver.children.map printDemand ==
      ([(4,[(50,n,51)],[])] : List GeneralDeclarativeWitnessCompiler350.DemandCode)).getD false

theorem literal_actual_centers : (emittedAt 9 9 && emittedAt 10 10) = true := by decide +kernel

theorem competing_real_demand_and_ordinary_leaf_at_nine : (data 9).isSome = true := by decide +kernel

theorem true_same_site_grandchild : test = true := by decide +kernel

theorem distinct_fixed_target_not_an_actual_center : test 9 = false := by decide +kernel

theorem old_token_no_implicit_reuse :
    test 10 {plan with authority := (seed 10).auth} = false := by decide +kernel

theorem exact_tree_position :
    test 10 plan (fun w => {w with path := [4,0,1]}) = false := by decide +kernel

theorem exact_emitted_index :
    test 10 {plan with childIndex := 1} = false := by decide +kernel

theorem wrong_old_row_as_authored :
    test 10 {plan with authored := authored ++ [⟨10,13,0,10⟩]} = false := by decide +kernel

theorem lower_is_not_actual_center :
    test 10 plan (fun w => {w with head := {w.head with center := {w.head.center with center := 2}}}) = false :=
  by decide +kernel

end Yulang.GeneralDeclarativeWitnessGrandchildFixture355
