import Yulang.GeneralDeclarativeWitnessReleasedObservation360

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 57000
set_option maxHeartbeats 53000000
namespace Yulang.GeneralDeclarativeWitnessReleasedForward360
open GeneralDeclarativeWitnessNestedInstall360 (Run written requested layout)
open GeneralDeclarativeWitnessNativeBodyFixture360 (childDecl)
open GeneralDeclarativeWitnessCoverageFixture357 (bundle)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarativeWitnessNativePreparation360 (Prepared Layout prepare)
open GeneralDeclarativeWitnessNativePipeline360 (wire gate authority valueCode)
open GeneralDeclarativeWitnessNativeValue360 (compile Write)
open GeneralDeclarativeWitnessNativeInstall360 (World Fits NativeViews)
open GeneralDeclarativeWitnessNativeSnapshot360 (commit)
open GeneralDeclarativeWitnessNativeRelease360 (ExactRelease checkExactRelease)
open GeneralDeclarativeWitnessReleasedObservation360 (actualRead observe)
open GeneralDeclarativeWitnessInheritedModeFixture357 (table)
open GeneralDeclarativeWitnessCompiler350 (printDemand)
open GeneralDeclarativeWitnessJointObservation359 (parentScope secondSpan)
open GeneralDeclarativeWitnessScopedBindings359 (FrameKey)
open GeneralDeclarations (Declaration)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWhere319 (Capture)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeHead320 (Models)

def forward : Declaration :=
  ⟨74,7,[.var 90,.app 55 [.var 91]],[⟨181,8,[.var 90],[]⟩],[],[]⟩
def receive : Declaration := ⟨75,8,[.var 92],[],[],[]⟩
def authored (negative : Bool) : Option Environment :=
  GeneralDeclarativeWitnessCoverageFixture357.prepare {bundle with
    roles := ⟨0,[⟨5,2,[(0,none)]⟩,⟨6,1,[(0,none)]⟩,⟨7,2,[]⟩,⟨8,1,[]⟩]⟩,
    declarations := [written negative,childDecl,forward,receive]}

def originalBody (negative : Bool) : Option (Run negative) := do
  let e ← authored negative
  let p ← prepare e parentScope requested layout
  let compiled ← compile p table (wire negative) 3
  match wrote : commit p compiled ⟨layout.named,gate⟩ with
  | none => none
  | some final => some ⟨e,p,compiled,final,wrote⟩

def forwardKey : FrameKey := ⟨[7],74,2⟩
def knownTarget : Capture := ⟨101,101,101⟩
def forwardDemand : Demand := ⟨7,[knownTarget,secondSpan],[]⟩
def fixed (before : World) : Layout :=
  ⟨before.ordinary,[(90,knownTarget),(91,secondSpan)],[101,105,106,107,108,109],
    fun _ => ⟨0,0,0⟩,fun _ _ => 0⟩

structure Forwarded {negative : Bool} (r : Run negative) where
  emitted : Prepared r.env forwardKey forwardDemand (fixed r.final)
  child : Demand
  literal : emitted.kids = [child]
  slot : Capture
  input : child.arguments = [slot]
  addressed : slot.center = r.typed.write.address.target
  auth : ExactRelease r.final.board authority r.typed.write

def send {negative : Bool} (r : Run negative) : Option (Forwarded r) := do
  let auth ← checkExactRelease r.final.board authority r.typed.write
  let out ← prepare r.env forwardKey forwardDemand (fixed r.final)
  match actual : out.kids with
  | [child] =>
    match found : child.arguments with
    | [span] =>
      if fixed : span.center = r.typed.write.address.target then
        some ⟨out,child,actual,span,found,fixed,auth⟩
      else none
    | _ => none
  | _ => none

def Forwarded.world {negative r} (c : @Forwarded negative r) : World := ⟨c.emitted.stage,r.final.board⟩

def confirm {negative r} (c : @Forwarded negative r) : Bool :=
  decide (printDemand c.child = (8,[(110,101,111)],[]) ∧ c.emitted.whereRows = [] ∧
    r.typed.write.code = valueCode negative)

theorem different_actual_body_compiles_child_at_released_center (negative : Bool) :
    ((originalBody negative).bind fun r => (send r).map confirm).getD false = true := by
  cases negative <;> decide +kernel

/-- This later prepared body is different from the original writer's
where clause. Its emitted child's center is literally the installed
typed target. The typed value is read from the same current native view,
not from the ordinary type assigned to that numerical name. -/
theorem child_reads_exact_released_output {negative r} (c : @Forwarded negative r)
    (m : Assignment) (v : NativeViews) (fit : Fits c.world m v) :
    c.emitted.kids = [c.child] ∧ c.child.arguments = [c.slot] ∧
    c.slot.center = r.typed.write.address.target ∧
    v c.slot.center = some (r.typed.code.eval m) := by
  have exact := GeneralDeclarativeWitnessNativeRelease360.checked_exact_written_value (w := c.world) c.auth m v fit
  exact ⟨c.literal,c.input,c.addressed,c.addressed.symm ▸ exact⟩

theorem no_authority_no_forwarded_use {negative} (r : Run negative)
    (absent : GeneralDeclarativeWitnessNativeInstall360.atTarget r.final.board r.typed.write.address.target = none) :
    send r = none := by
  have no := GeneralDeclarativeWitnessNativeRelease360.not_installed_not_released
    (gate := authority) (addr := r.typed.write.address) absent
  simp [send,checkExactRelease,no]

end Yulang.GeneralDeclarativeWitnessReleasedForward360
