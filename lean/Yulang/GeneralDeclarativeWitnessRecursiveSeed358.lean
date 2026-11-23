import Yulang.GeneralDeclarativeWitnessProjectionCheck358
import Yulang.GeneralDeclarativeWitnessJoinedFixture357

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 55000
set_option maxHeartbeats 60000000
namespace Yulang.GeneralDeclarativeWitnessRecursiveSeed358
open GeneralDeclarativeWitnessDeclaredState357 (Current centerEq point pointSpans context)
open GeneralDeclarativeWitnessAuthoredProjection358 (Source Recipe originated links)
open GeneralDeclarativeWitnessJoinedCheck357 (Layout Answer replay)
open GeneralDeclarativeWitnessProjectionCheck358 (Certificate)
open GeneralDeclarativeWitnessCompiler350 (Wire Finished execute printDemand)
open GeneralDeclarativeWitnessJoinedFixture357 (root written here head)
open GeneralDeclarativeWitnessCoverageFixture357 (catalog prepare)
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarations (Declaration)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralDeclarativeWitnessModeDeclaration357 (ready)
open GeneralDeclarativeWitnessModeCoverage357 (check)
open PresenceNormalForm (Atom)

def parent : Declaration :=
  ⟨92,5,[head],[⟨81,6,[.var 32],[⟨82,0,.var 31⟩]⟩],[⟨91,0,.var 31⟩],[]⟩

def child : Declaration :=
  ⟨93,6,[.variant 7 (.var 33)],[],[⟨94,0,.variant 7 (.var 33)⟩],[]⟩

def bundle : InputBundle :=
  ⟨⟨.absent,catalog⟩,⟨.absent,catalog⟩,⟨0,[⟨5,1,[(0,none)]⟩,⟨6,1,[(0,none)]⟩]⟩,[parent,child]⟩

def outer : Capture := ⟨63,10,64⟩
def inner : Capture := ⟨3,4,5⟩
def recipe : Recipe := ⟨7,7,8,1,2,outer,inner⟩
def author : Source := ⟨originated recipe⟩

def base : State := ⟨⟨links inner,[]⟩,author.authored⟩

def parentLayout : Layout := ⟨base,[1,2,3,4,5,7,8,10,17,18,20,41,60],point,fun _ _ => 41⟩
def childLayout (parent : Finished) : Layout :=
  ⟨parent.state,[1,2,3,4,5,7,8,10,17,18,20,41,60,63,64],point,fun _ _ => 0⟩

def plan (f : Finished) (current : State) : Wire :=
  ⟨f.kids.map printDemand,f.fixed,⟨
    f.state.normal.ordinary.map (fun atom => current.normal.ordinary.idxOf atom),
    f.state.normal.intervals.map (fun edge => .interval (current.normal.intervals.idxOf edge)),
    f.state.equations.map (fun row => .currentRow (current.equations.idxOf row))⟩⟩

structure Data where
  current : Current
  first : Finished
  second : Finished
  reached : Demand
  parentWire : Wire
  childWire : Wire

def data : Option Data := do
  let e ← prepare bundle
  let before : Current := ⟨e,base,here⟩
  let p ← execute (context before root parent parentLayout.named (pointSpans 31 32 10)
    parentLayout.keep parentLayout.fallback parentLayout.via)
  let [reached] := p.kids | none
  let l := childLayout p
  let c ← execute (context before reached child l.named [(33,inner)] l.keep l.fallback l.via)
  let final : Current := ⟨e,c.state,here⟩
  pure ⟨final,p,c,reached,plan p final.ordinary,plan c final.ordinary⟩

def test (edit : Data → Data := id) (origin : Source := author) (projection : Recipe := recipe) : Bool :=
  (data.map (fun raw =>
    let d := edit raw
    (replay d.current root written parentLayout d.parentWire).isSome &&
    (GeneralDeclarativeWitnessProjectionCheck358.replay origin d.current d.reached
      projection 33 (childLayout d.first) d.childWire).isSome &&
    check d.current.environment && ready d.current &&
    GeneralSourceMetadataRoles291.check d.current.environment.source.roles)).getD false

theorem actual_two_local_writers : test = true := by decide +kernel

def outside : Option GeneralDeclarativeWitnessCompiler350.DemandCode := data.map (fun d => printDemand d.reached)

theorem exact_nonpoint_input : outside = some (6,[(63,10,64)],[(0,41)]) := by rfl

def outputs : Option (List Nat × List Nat) := data.map fun d =>
  (d.parentWire.outputRows.map Equation.left,d.childWire.outputRows.map Equation.left)

theorem exact_fixed_targets : outputs = some ([60],[41]) := by decide +kernel

theorem not_enough_to_have_same_atoms :
    test id {authored := []} = false := by decide +kernel

theorem requires_right_arm_in_independent_source : test id {authored := (author.authored.take 1 ++ author.authored.drop 2)} = false := by decide +kernel

theorem cannot_use_outer_center_for_internal_payload :
    test id author {recipe with inner := point 10} = false := by decide +kernel

end Yulang.GeneralDeclarativeWitnessRecursiveSeed358
