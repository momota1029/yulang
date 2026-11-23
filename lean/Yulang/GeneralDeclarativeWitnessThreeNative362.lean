import Yulang.GeneralDeclarativeWitnessNativeRelease360
import Yulang.GeneralDeclarativeWitnessRecordWidthFixture359
import Yulang.GeneralDeclarativeWitnessInheritedModeFixture357
import Yulang.GeneralDeclarativeWitnessFullIntervals357

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 60000
set_option maxHeartbeats 58000000
namespace Yulang.GeneralDeclarativeWitnessThreeNative362
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarativeWitnessCoverageFixture357 (bundle)
open GeneralDeclarativeWitnessRecordWidthFixture359 (current)
open GeneralDeclarativeWitnessScopedBindings359 (FrameKey)
open GeneralDeclarativeWitnessNativePreparation360 (Layout Prepared prepare)
open GeneralDeclarativeWitnessNativeValue360 (Address Write Compiled compile)
open GeneralDeclarativeWitnessNativeInstall360 (Board World install)
open GeneralDeclarativeWitnessNativeRelease360 (ReleaseAuthority checkExactRelease)
open GeneralDeclarativeWitnessAssociatedDescriptor359 (Wire)
open GeneralDeclarativeWitnessTypedRelease354 (Stamp)
open GeneralDeclarativeWitnessInheritedModeFixture357 (table)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarations (Declaration)

def ctor (contra : Bool) : Nat := if contra then 42 else 20
def first (contra : Bool) : Nat := if contra then 62 else 60
def last (contra : Bool) : Nat := if contra then 60 else 62
def point (n : Nat) : Capture := ⟨n,n,n⟩
def frame : FrameKey := ⟨[9],96,0⟩
def owner : Stamp := ⟨[9],9,96,4⟩
def board : Board := ⟨[owner],[]⟩

def declaration (contra : Bool) : Declaration :=
  ⟨96,9,[.var 80,.var 81,.var 82],[],
    [⟨181,0,.app (ctor contra) [.var 80]⟩,
     ⟨182,1,.app (ctor contra) [.var 81]⟩,
     ⟨183,2,.app (ctor contra) [.var 82]⟩],[]⟩

def env (contra : Bool) : Option Environment :=
  GeneralDeclarativeWitnessCoverageFixture357.prepare {bundle with
    roles := ⟨0,[⟨9,3,[(0,none),(1,none),(2,none)]⟩]⟩,
    declarations := [declaration contra]}

def asked (contra : Bool) : Demand :=
  ⟨9,[point (first contra),point 61,point (last contra)],[⟨0,201⟩,⟨1,202⟩,⟨2,203⟩]⟩

def layout (contra : Bool) : Layout :=
  ⟨current,[(80,point (first contra)),(81,point 61),(82,point (last contra))],
    [60,61,62,201,202,203],fun _ => ⟨0,0,0⟩,fun _ _ => 0⟩

def wire (contra : Bool) (i : Nat) : Wire :=
  ⟨i,181+i,201+i,.unary (ctor contra) (.bind (80+i))⟩

def address (i : Nat) : Address := ⟨owner,0,i,i,201+i,181+i⟩
def authority : ReleaseAuthority := ⟨[address 0,address 1,address 2]⟩

structure Run (contra : Bool) where
  environment : Environment
  prepared : Prepared environment frame (asked contra) (layout contra)
  lower : Compiled prepared table (wire contra 0) 4
  center : Compiled prepared table (wire contra 1) 4
  upper : Compiled prepared table (wire contra 2) 4
  stage₁ : World
  stage₂ : World
  final : World
  write₁ : install prepared lower board = some stage₁
  write₂ : install prepared center stage₁.board = some stage₂
  write₃ : install prepared upper stage₂.board = some final

def run (contra : Bool) : Option (Run contra) := do
  let e ← env contra
  let p ← prepare e frame (asked contra) (layout contra)
  let lo ← compile p table (wire contra 0) 4
  let mid ← compile p table (wire contra 1) 4
  let hi ← compile p table (wire contra 2) 4
  match one : install p lo board with
  | none => none
  | some f =>
    match two : install p mid f.board with
    | none => none
    | some g =>
      match three : install p hi g.board with
      | none => none
      | some result => some ⟨e,p,lo,mid,hi,f,g,result,one,two,three⟩

def expected (contra : Bool) : List Write :=
  [⟨address 0,.unary (ctor contra) (.leaf (first contra))⟩,
   ⟨address 1,.unary (ctor contra) (.leaf 61)⟩,
   ⟨address 2,.unary (ctor contra) (.leaf (last contra))⟩]

def checked {contra} (r : Run contra) : Bool :=
  decide (r.final.board.writes = expected contra ∧
    [r.lower.write,r.center.write,r.upper.write] = expected contra) &&
  (checkExactRelease r.final.board authority r.lower.write).isSome &&
  (checkExactRelease r.final.board authority r.center.write).isSome &&
  (checkExactRelease r.final.board authority r.upper.write).isSome

theorem actual_three_authored_outputs (contra : Bool) :
    ((run contra).map checked).getD false = true := by cases contra <;> decide +kernel

end Yulang.GeneralDeclarativeWitnessThreeNative362
