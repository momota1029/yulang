import Yulang.GeneralDeclarativeWitnessRecursiveFixture358

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 62000
set_option maxHeartbeats 82000000
namespace Yulang.GeneralDeclarativeWitnessSiblingSeed358
open GeneralDeclarativeWitnessRecursiveSeed358 (base author recipe plan inner)
open GeneralDeclarativeWitnessJoinedFixture357 (root head written here)
open GeneralDeclarativeWitnessCoverageFixture357 (catalog prepare)
open GeneralDeclarativeWitnessDeclaredState357 (Current point pointSpans context)
open GeneralDeclarativeWitnessJoinedCheck357 (Layout)
open GeneralDeclarativeWitnessCompiler350 (Wire Finished execute printDemand DemandCode)
open GeneralDeclarativeWitnessOrderedReplay358 (Code LayoutAt)
open GeneralDeclarativeWitnessOrderedReport358 (Packet verify)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarations (Declaration)
open GeneralSourceMetadataBareBundle291 (InputBundle)

def parent : Declaration :=
  ⟨92,5,[head],
    [⟨81,6,[.var 32],[⟨82,0,.var 31⟩]⟩,⟨83,7,[.var 31],[⟨84,0,.var 32⟩]⟩],
    [⟨91,0,.var 31⟩],[]⟩

def childDecl (role : Nat) : Declaration :=
  if role = 6 then GeneralDeclarativeWitnessRecursiveSeed358.child else
    ⟨94,7,[.variant 7 (.var 34)],[],[⟨95,0,.variant 7 (.var 34)⟩],[]⟩

def bundle : InputBundle :=
  ⟨⟨.absent,catalog⟩,⟨.absent,catalog⟩,
    ⟨0,[⟨5,1,[(0,none)]⟩,⟨6,1,[(0,none)]⟩,⟨7,1,[(0,none)]⟩]⟩,
    [parent,childDecl 6,childDecl 7]⟩

def firstLayout : Layout :=
  ⟨base,[1,2,3,4,5,7,8,10,17,18,20,41,42,60],point,fun c _ => if c.id = 81 then 41 else 42⟩

def laterLayout (f : Finished) : Layout :=
  ⟨f.state,[1,2,3,4,5,7,8,10,17,18,20,41,42,60,61,62,63,64],point,fun _ _ => 0⟩

structure Data where
  current : Current
  first : Finished
  second : Finished
  third : Finished
  left : Demand
  right : Demand
  parentWire : Wire
  leftWire : Wire
  rightWire : Wire

def data : Option Data := do
  let e ← prepare bundle
  let before : Current := ⟨e,base,here⟩
  let f ← execute (context before root parent firstLayout.named (pointSpans 31 32 10)
    firstLayout.keep firstLayout.fallback firstLayout.via)
  let [left,right] := f.kids | none
  let l := laterLayout f
  let y ← execute (context before left (childDecl 6) l.named [(33,inner)] l.keep l.fallback l.via)
  let r := laterLayout y
  let z ← execute (context before right (childDecl 7) r.named [(34,inner)] r.keep r.fallback r.via)
  let s := z.state
  pure ⟨⟨e,s,here⟩,f,y,z,left,right,plan f s,plan y s,plan z s⟩

def layouts (d : Data) : LayoutAt :=
  fun p => if p = [5] then firstLayout else
    if p = [5,0] then laterLayout d.first else laterLayout d.second

def childMethod (d : Demand) (binder : Nat) :=
  GeneralDeclarativeWitnessOrderedReplay358.LocalCode.project
    {recipe with outer := d.arguments.headD recipe.outer} binder

def children (d : Data) : GeneralDeclarativeWitnessOrderedReplay358.Codes :=
  .cons (.node (childMethod d.left 33) d.leftWire .nil)
    (.cons (.node (childMethod d.right 34) d.rightWire .nil) .nil)

def code (d : Data) : Code := .node (.join written) d.parentWire (children d)

def shape : Option (List DemandCode × List (List Nat)) := data.map fun d =>
  (d.parentWire.children,[d.parentWire.outputRows.map Equation.left,
    d.leftWire.outputRows.map Equation.left,d.rightWire.outputRows.map Equation.left])

end Yulang.GeneralDeclarativeWitnessSiblingSeed358
