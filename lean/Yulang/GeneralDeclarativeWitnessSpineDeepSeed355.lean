import Yulang.GeneralDeclarativeWitnessNominalSpineWhole355
import Yulang.GeneralDeclarativeWitnessGrandchildModel355
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 50000
set_option maxHeartbeats 48000000
namespace Yulang.GeneralDeclarativeWitnessSpineDeepSeed355
open GeneralDeclarativeWitnessGrandchildSeed355 (seed producer middle leaf)
open GeneralDeclarativeWitnessCovariantHead352 (rawPattern)
open GeneralDeclarativeWitnessCovariantFixture353 (wire)
open GeneralDeclarativeWitnessTypedForestFixture354 (head)
open GeneralDeclarativeWitnessTypedPacket354 (Run Report typedAt)
open GeneralDeclarativeWitnessTypedChild354 (Input downstream)
open GeneralDeclarativeWitnessTypedRangeWriter354 (run)
open GeneralDeclarativeWitnessSpineNode355 (Send Author)
open GeneralDeclarativeWitnessCovariantOrigin353 (Problem Row)
open GeneralDeclarativeWitnessCompiler350 (printDemand)
open GeneralDeclarativeWitnessOrderedFixture350 (literalPlan)
open GeneralDeclarativeHead320 (State)
open GeneralDeclarations (Clause Declaration)

def asks (id role eq n : Nat) : Clause := ⟨id,role,[.var 31],[⟨eq,n,.var 31⟩]⟩
def returns (eq n : Nat) : GeneralDeclarations.Equation := ⟨eq,n,.variant 13 (.app 0 [.var 32])⟩

def scheme : List Declaration :=
  [GeneralDeclarativeWitnessTypedRangeFixture354.rootDecl,
   {middle with requirements := [asks 83 4 84 7]},
   {leaf with requirements := [asks 85 5 86 8],associated := [returns 110 7]},
   ⟨95,5,[rawPattern],[⟨87,6,[.var 31],[]⟩],[returns 111 8],[]⟩,
   ⟨96,6,[rawPattern],[],[],[]⟩]

def input : Problem :=
  let p := producer 10
  let old := p.metadata.sourceInput
  let new := { old with
    roles := ⟨0,[⟨1,1,[(0,none),(1,none),(2,none)]⟩,⟨3,1,[(4,none)]⟩,⟨4,1,[(7,none)]⟩,
      ⟨5,1,[(8,none)]⟩,⟨6,1,[]⟩]⟩
    declarations := scheme }
  {p with metadata := {p.metadata with sourceInput := new}}

def root : Input := {seed 10 with producer := input}

structure Scope where
  source : Author
  head : GeneralDeclarativeWitnessCovariantInterval353.Wire
  path : List Nat

def locus (readPath : List Nat) (v role decl name : Nat) (parents : Nat) (l h : Nat)
    (keep : List Nat) (lower upper : Nat) : Scope :=
  let stamp : GeneralDeclarativeWitnessTypedRelease354.Stamp := ⟨readPath,role,decl,v⟩
  let authority : GeneralDeclarativeWitnessTypedRelease354.Authority := ⟨[stamp],[⟨stamp,0,name,10⟩]⟩
  ⟨⟨authority,0,parents,[⟨30,13,0,7⟩,⟨31,13,0,8⟩,⟨l,13,0,l⟩,⟨h,13,0,h⟩],keep,fun _ => ⟨10,10,10⟩⟩,
    ⟨⟨0,rawPattern,0,1,4⟩,2,3,.constraint lower,.constraint upper⟩,readPath ++ [0]⟩

def second := locus [4,0] 8 3 93 4 9 50 51 [89] 18 21
def third := locus [4,0,0] 9 4 94 7 10 90 91 [129] 34 37
def fourth := locus [4,0,0,0] 10 5 95 8 11 130 131 [169] 50 53

structure Layer where
  input : Problem
  w : GeneralDeclarativeWitnessCovariantInterval353.Wire
  done : GeneralDeclarativeWitnessTypedRangeWriter354.Run input w

def after (before : Layer) (target : Scope) : Option Layer := do
  let d ← before.done.children[0]?
  let written ← typedAt before.done.output target.source.write
  let p : Problem := { before.input with
    stage := before.done.state
    rows := target.source.rows ++ [written.1.typed.row]
    demand := d
    keep := target.source.keep
    fallback := target.source.fallback }
  let last ← run p target.head
  pure ⟨p,target.head,last⟩

def start : Option (Run input wire × Layer) := do
  let out ← GeneralDeclarativeWitnessTypedPacket354.run input wire
  let kid ← out.children[0]?
  let named ← typedAt out.writes 1
  let child := downstream root out.state kid named.1.typed.row
  let built ← run child (head false)
  pure (out,⟨child,head false,built⟩)

def firstTwo : Option (Run input wire × Layer × Layer) := do
  let (out,b) ← start
  let child ← after b second
  pure (out,b,child)

def firstThree : Option (Run input wire × Layer × Layer × Layer) := do
  let (out,b,c) ← firstTwo
  let d ← after c third
  pure (out,b,c,d)

def full : Option (Run input wire × Layer × Layer × Layer × Layer) := do
  let (out,b,c,d) ← firstThree
  let e ← after d fourth
  pure (out,b,c,d,e)

def forLayer (a : Layer) (s : State) : Option Report := do
  let keep ← literalPlan a.done.state s
  pure ⟨a.done.readFrom.center.decl.id,a.done.children.map printDemand,a.done.output.trace,keep⟩

end Yulang.GeneralDeclarativeWitnessSpineDeepSeed355
