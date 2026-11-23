import Yulang.GeneralDeclarativeWitnessNativeBodyFixture360
import Yulang.GeneralDeclarativeWitnessNativeRelease360

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 53000
set_option maxHeartbeats 50000000
namespace Yulang.GeneralDeclarativeWitnessNativePipeline360
open GeneralDeclarativeWitnessNativePreparation360 (Prepared)
open GeneralDeclarativeWitnessNativeBodyFixture360 (input body initial request view)
open GeneralDeclarativeWitnessJointObservation359 (parentScope)
open GeneralDeclarativeWitnessNominalRecordFixture359 (route ctor)
open GeneralDeclarativeWitnessInheritedModeFixture357 (table)
open GeneralDeclarativeWitnessNativeValue360 (Address Write Code Compiled compile)
open GeneralDeclarativeWitnessNativeInstall360 (Board World install atTarget)
open GeneralDeclarativeWitnessNativeRelease360 (ReleaseAuthority checkExactRelease)
open GeneralDeclarativeWitnessAssociatedDescriptor359 (Wire)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarativeWitnessTypedRelease354 (Stamp)
open GeneralDeclarativeWitnessCompiler350 (printDemand)
open GeneralDeclarativeWhere319 (Capture)

def stamp : Stamp := ⟨[5],5,72,3⟩
def gate : Board := ⟨[stamp],[]⟩
def authorizedAddress : Address := ⟨stamp,0,0,0,101,111⟩
def authority : ReleaseAuthority := ⟨[authorizedAddress]⟩
def wire (negative : Bool) : Wire := ⟨0,111,101,route negative 80⟩
def valueCode (negative : Bool) : Code := .unary 55 (.unary (ctor negative) (.leaf 61))

structure Run (negative : Bool) where
  env : Environment
  prepared : Prepared env parentScope request initial
  output : Compiled prepared table (wire negative) 3
  current : World
  installed : install prepared output gate = some current

def run (negative : Bool) : Option (Run negative) := do
  let env ← input negative
  let prepared ← body env
  let output ← compile prepared table (wire negative) 3
  match installed : install prepared output gate with
  | none => none
  | some current => some ⟨env,prepared,output,current,installed⟩

def confirm {negative} (r : Run negative) : Bool :=
  view r.prepared &&
  decide (r.prepared.kids.map printDemand = [(6,[(106,61,107)],[(0,105)])]) &&
  decide (r.output.write = ⟨authorizedAddress,valueCode negative⟩) &&
  decide (atTarget r.current.board 101 = some r.output.write) &&
  (checkExactRelease r.current.board authority r.output.write).isSome

theorem actual_compiler_write_and_child (negative : Bool) : ((run negative).map confirm).getD false = true := by
  cases negative <;> decide +kernel

def wrongVersion (addr : Address) : Address := {addr with owner := {addr.owner with version := 2}}
def wrongOrdinal (addr : Address) : Address := {addr with outputOrdinal := 1}
def wrongPath (addr : Address) : Address := {addr with owner := {addr.owner with path := [5,0]}}
def wrongScope (addr : Address) : Address := {addr with declarationOrdinal := 1}

def tamper (negative : Bool) (r : Run negative) : Bool :=
  let saved := r.output.write
  let changedCode := {saved with code := .unary 55 (.unary (ctor negative) (.leaf 67))}
  (checkExactRelease gate authority saved).isSome ||
  (checkExactRelease r.current.board ⟨[]⟩ saved).isSome ||
  (checkExactRelease r.current.board authority {saved with address := wrongVersion saved.address}).isSome ||
  (checkExactRelease r.current.board authority {saved with address := wrongOrdinal saved.address}).isSome ||
  (checkExactRelease r.current.board authority {saved with address := wrongPath saved.address}).isSome ||
  (checkExactRelease r.current.board authority {saved with address := wrongScope saved.address}).isSome ||
  (checkExactRelease {r.current.board with writes := [changedCode]} authority saved).isSome ||
  (install r.prepared r.output r.current.board).isSome

theorem source_version_grant_and_actual_value_are_separate (negative : Bool) :
    ((run negative).map (tamper negative)).getD true = false := by cases negative <;> decide +kernel

end Yulang.GeneralDeclarativeWitnessNativePipeline360
