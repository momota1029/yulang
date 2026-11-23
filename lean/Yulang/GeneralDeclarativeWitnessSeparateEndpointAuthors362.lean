import Yulang.GeneralDeclarativeWitnessScopedNativeWindows362

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 71000
set_option maxHeartbeats 78000000
namespace Yulang.GeneralDeclarativeWitnessSeparateEndpointAuthors362
open GeneralDeclarativeWitnessThreeNative362 (ctor first last point)
open GeneralDeclarativeWitnessRecordWidthFixture359 (current)
open GeneralDeclarativeWitnessCoverageFixture357 (bundle)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarativeWitnessScopedBindings359 (FrameKey)
open GeneralDeclarativeWitnessNativePreparation360 (Layout Prepared prepare)
open GeneralDeclarativeWitnessNativeInstall360 (World Board install Fits NativeViews)
open GeneralDeclarativeWitnessNativeValue360 (Compiled Address Write compile)
open GeneralDeclarativeWitnessNativeRelease360 (ReleaseAuthority checkExactRelease)
open GeneralDeclarativeWitnessAssociatedDescriptor359 (Wire)
open GeneralDeclarativeWitnessTypedRelease354 (Stamp)
open GeneralDeclarativeWitnessInheritedModeFixture357 (table)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarations (Declaration)

def payload (contra : Bool) (i : Nat) : Nat := if i = 0 then first contra else if i = 1 then 61 else last contra
def role (i : Nat) := 12+i
def declId (i : Nat) := 110+i
def field (i : Nat) := 401+i
def version (i : Nat) := 4+i
def target (i : Nat) := 301+i
def key (i : Nat) : FrameKey := ⟨[12,i],declId i,i⟩
def owner (i : Nat) : Stamp := ⟨[12,i],role i,declId i,version i⟩
def address (i : Nat) : Address := ⟨owner i,i,0,0,target i,field i⟩
def row (contra : Bool) (i : Nat) : Write := ⟨address i,.unary (ctor contra) (.leaf (payload contra i))⟩
def authority : ReleaseAuthority := ⟨[address 0,address 1,address 2]⟩

def declaration (contra : Bool) (i : Nat) : Declaration :=
  ⟨declId i,role i,[.var 83],[],[⟨field i,0,.app (ctor contra) [.var 83]⟩],[]⟩

def input (contra : Bool) : Option Environment :=
  GeneralDeclarativeWitnessCoverageFixture357.prepare {bundle with
    roles := ⟨0,[⟨role 0,1,[(0,none)]⟩,⟨role 1,1,[(0,none)]⟩,⟨role 2,1,[(0,none)]⟩]⟩,
    declarations := [declaration contra 0,declaration contra 1,declaration contra 2]}

def request (contra : Bool) (i : Nat) : Demand :=
  ⟨role i,[point (payload contra i)],[⟨0,target i⟩]⟩

def layout (contra : Bool) (i : Nat) (w : World) : Layout :=
  ⟨w.ordinary,[(83,point (payload contra i))],[60,61,62,301,302,303],
    fun _ => ⟨0,0,0⟩,fun _ _ => 0⟩

def wire (contra : Bool) (i : Nat) : Wire :=
  ⟨0,field i,target i,.unary (ctor contra) (.bind 83)⟩

structure Published (contra : Bool) (e : Environment) (before : World) (i : Nat) where
  prepared : Prepared e (key i) (request contra i) (layout contra i before)
  native : Compiled prepared table (wire contra i) (version i)
  final : World
  installed : install prepared native before.board = some final

def publish (contra : Bool) (e : Environment) (before : World) (i : Nat) :
    Option (Published contra e before i) := do
  let p ← prepare e (key i) (request contra i) (layout contra i before)
  let write ← compile p table (wire contra i) (version i)
  match saved : install p write before.board with
  | none => none
  | some w => some ⟨p,write,w,saved⟩

def initial : World := ⟨current,⟨[owner 0,owner 1,owner 2],[]⟩⟩

structure Ordered (contra : Bool) where
  env : Environment
  before : Published contra env initial 0
  center : Published contra env before.final 1
  after : Published contra env center.final 2

def run (contra : Bool) : Option (Ordered contra) := do
  let env ← input contra
  let lo ← publish contra env initial 0
  let mid ← publish contra env lo.final 1
  let hi ← publish contra env mid.final 2
  pure ⟨env,lo,mid,hi⟩

def checked {contra} (p : Ordered contra) : Bool :=
  decide (p.after.final.board.writes = [row contra 0,row contra 1,row contra 2] ∧
    [p.before.native.write,p.center.native.write,p.after.native.write] = [row contra 0,row contra 1,row contra 2]) &&
  (checkExactRelease p.after.final.board authority p.before.native.write).isSome &&
  (checkExactRelease p.after.final.board authority p.center.native.write).isSome &&
  (checkExactRelease p.after.final.board authority p.after.native.write).isSome

theorem actual_three_independent_authors (contra : Bool) :
    ((run contra).map checked).getD false = true := by cases contra <;> decide +kernel

def dryOwner (b : Board) (i : Nat) : Board :=
  {b with active := b.active.filter (fun x => decide (x ≠ owner i))}

def control {contra} (p : Ordered contra) : Bool :=
  let w := dryOwner p.after.final.board 0
  (checkExactRelease w authority p.before.native.write).isNone &&
  (checkExactRelease w authority p.center.native.write).isSome &&
  (checkExactRelease w authority p.after.native.write).isSome &&
  (checkExactRelease p.after.final.board ⟨[address 0]⟩ p.before.native.write).isSome &&
  (checkExactRelease p.after.final.board ⟨[address 0]⟩ p.after.native.write).isNone

theorem independent_author_validity_can_change_alone (contra : Bool) :
    ((run contra).map control).getD false = true := by cases contra <;> decide +kernel

end Yulang.GeneralDeclarativeWitnessSeparateEndpointAuthors362
