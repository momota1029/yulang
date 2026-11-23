import Yulang.GeneralDeclarativeWitnessForwardModel360

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 57000
set_option maxHeartbeats 53000000
namespace Yulang.GeneralDeclarativeWitnessNativeReceiver360
open GeneralDeclarativeWitnessReleasedForward360 (Forwarded originalBody send)
open GeneralDeclarativeWitnessForwardModel360 (actual_child_binds_native_payload)
open GeneralDeclarativeWitnessNestedInstall360 (Run)
open GeneralDeclarativeWitnessNativePreparation360 (Prepared Layout prepare context)
open GeneralDeclarativeWitnessNativeInstall360 (World Fits NativeViews)
open GeneralDeclarativeWitnessNativeSnapshot360 (same)
open GeneralDeclarativeWitnessScopedBindings359 (FrameKey slots)
open GeneralDeclarativeWitnessReleasedObservation360 (observe actualRead)
open GeneralDeclarativeWitnessCompiler350 (Finished execute)
open GeneralDeclarativeWitnessLiteral349 (preserves preserves_iff)
open GeneralDeclarativeGrowth327 (restrict)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWhere319 (Capture)
open GeneralNominalCommonBridge (Assignment)

def key : FrameKey := ⟨[7,0],75,3⟩
def receiverLayout {negative r} (f : @Forwarded negative r) : Layout :=
  ⟨f.world.ordinary,[(92,f.slot)],[101,105,106,107,108,109,110,111,112,113],
    fun _ => ⟨0,0,0⟩,fun _ _ => 0⟩

structure Received {negative : Bool} {r : Run negative} (f : Forwarded r) where
  prepared : Prepared r.env key f.child (receiverLayout f)
  literalHead : prepared.impl.head = [.var 92]
  span : Capture
  bound : slots [prepared.captures] key 92 = some span
  center : span.center = f.slot.center
  body : Finished
  ran : execute (context r.env f.child prepared.impl (receiverLayout f)) = some body
  noWrites : body.fixed = []
  noKids : body.kids = []
  kept : preserves f.world.ordinary body.state = true

def receive {negative} {r : Run negative} (f : Forwarded r) : Option (Received f) := do
  let p ← prepare r.env key f.child (receiverLayout f)
  if head : p.impl.head = [.var 92] then
    match chosen : slots [p.captures] key 92 with
    | none => none
    | some cap =>
      if sameCenter : cap.center = f.slot.center then
        match ran : execute (context r.env f.child p.impl (receiverLayout f)) with
        | none => none
        | some body =>
          if exact : body.fixed = [] ∧ body.kids = [] ∧ preserves f.world.ordinary body.state = true then
            some ⟨p,head,cap,chosen,sameCenter,body,ran,exact.1,exact.2.1,exact.2.2⟩
          else none
      else none
  else none

def Received.world {negative r f} (read : @Received negative r f) : World := ⟨read.body.state,f.world.board⟩

def checked {negative r f} (read : @Received negative r f) : Bool :=
  decide (read.span.lower = 114 ∧ read.span.center = 101 ∧ read.span.upper = 115)

theorem source_body_receives_original_native_center (negative : Bool) :
    ((originalBody negative).bind fun r => (send r).bind fun f => (receive f).map checked).getD false = true := by
  cases negative <;> decide +kernel

theorem same_model_received_binder {negative} {r : Run negative} {f : Forwarded r}
    (root : originalBody negative = some r) (sent : send r = some f) (read : Received f)
    (m : Assignment) (v : NativeViews) (valid : Fits read.world m v) :
    read.prepared.impl.head = [.var 92] ∧ read.span.center = 101 ∧
    (v read.span.center).bind (fun ty => observe ty (actualRead negative)) = some (m 61).1 ∧
    read.body.fixed = [] ∧ read.body.kids = [] := by
  have prior : Fits f.world m v := ⟨restrict ((preserves_iff ..).mp read.kept) m valid.1,valid.2⟩
  obtain ⟨actual,seen⟩ := actual_child_binds_native_payload root sent m v prior
  exact ⟨read.literalHead,read.center.trans actual,read.center.symm ▸ seen,read.noWrites,read.noKids⟩

end Yulang.GeneralDeclarativeWitnessNativeReceiver360
