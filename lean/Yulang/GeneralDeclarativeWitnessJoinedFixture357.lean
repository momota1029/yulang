import Yulang.GeneralDeclarativeWitnessJoinedCheck357
import Yulang.GeneralDeclarativeWitnessCoverageFixture357

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 45000
set_option maxHeartbeats 42000000
namespace Yulang.GeneralDeclarativeWitnessJoinedFixture357
open GeneralDeclarativeWitnessJoinedCheck357 (Recipe Layout replay Answer)
open GeneralDeclarativeWitnessDeclaredState357 (Current point observed centerEq pointSpans context)
open GeneralDeclarativeWitnessCompiler350 (Wire Finished execute printDemand)
open GeneralDeclarativeWitnessCoverageFixture357 (catalog prepare)
open GeneralDeclarativeWitnessModeDeclaration357 (ready)
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarations (Declaration)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarativeWitnessProblem349 (splitAnd)

def head : Pattern := .join (.variant 13 (.app 20 [.var 31])) (.variant 13 (.app 20 [.var 32]))

def rootDecl (hasChild : Bool) : Declaration :=
  ⟨92,5,[head],if hasChild then [⟨81,6,[.var 32],[]⟩] else [],
    [⟨91,0,.var 31⟩],[]⟩

def environment (hasChild : Bool) : Option Environment :=
  prepare ⟨⟨.absent,catalog⟩,⟨.absent,catalog⟩,⟨0,[⟨5,1,[(0,none)]⟩,⟨6,1,[]⟩]⟩,[rootDecl hasChild]⟩

def root : Demand := ⟨5,[point 20],[⟨0,60⟩]⟩

def initial : State := ⟨⟨[],[]⟩,[centerEq 10 7 8]⟩

def written : Recipe := ⟨13,20,31,32,17,18,20,7,8,10,head⟩

def layout : Layout := ⟨initial,[7,8,10,17,18,20,60],point,fun _ x => x⟩

def here : List GeneralDeclarativeWitnessDeclaredState357.AuthoredNominal :=
  [observed 17 13 20 7,observed 18 13 20 8,observed 20 13 20 10]

def exactWire (f : Finished) : Wire :=
  ⟨f.kids.map printDemand,f.fixed,⟨List.range f.state.normal.ordinary.length,
    (List.range f.state.normal.intervals.length).map .interval,
    (List.range f.state.equations.length).map .currentRow⟩⟩

structure Data where
  current : Current
  wire : Wire

def data (hasChild : Bool) : Option Data := do
  let e ← environment hasChild
  let start : Current := ⟨e,initial,here⟩
  let compiled ← execute (context start root (rootDecl hasChild) layout.named
    (pointSpans 31 32 10) layout.keep layout.fallback layout.via)
  pure ⟨⟨e,compiled.state,here⟩,exactWire compiled⟩

def test (hasChild : Bool)
    (edit : Data → Data := id) (adjust : Recipe → Recipe := id) : Bool :=
  ((data hasChild).map fun base =>
    let x := edit base
    (replay x.current root (adjust written) layout x.wire).isSome &&
    GeneralDeclarativeWitnessModeCoverage357.check x.current.environment &&
    ready x.current &&
    GeneralSourceMetadataRoles291.check x.current.environment.source.roles).getD false

theorem actual_positive_leaf : test false = true := by decide +kernel
theorem actual_positive_nonempty_children : test true = true := by decide +kernel

def receiptShape (hasChild : Bool) : Option (List GeneralDeclarativeWitnessCompiler350.DemandCode × List Nat) :=
  ((data hasChild).map fun e => (e.wire.children,e.wire.outputRows.map GeneralDeclarativeHead320.Equation.left))

theorem actual_compiler_outputs_and_child :
    receiptShape true = some ([(6,[(63,10,64)],[])],[60]) := by
  rfl

theorem refuses_split_capture : test true id (fun r => {r with value := 7}) = false := by decide +kernel

theorem missing_real_center_not_repaired_by_arm : test true
    (fun x => {x with current := {x.current with visible := x.current.visible.take 2}}) = false := by
  decide +kernel

theorem cannot_omit_child :
    test true (fun x => {x with wire := {x.wire with children := []}}) = false := by decide +kernel

theorem output_target_not_readdressed :
    test true (fun x => {x with wire := {x.wire with outputRows := (x.wire.outputRows.map (fun o => {o with left := 10}))}}) = false := by decide +kernel

end Yulang.GeneralDeclarativeWitnessJoinedFixture357
