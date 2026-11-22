import Yulang.GeneralDeclarativeWitnessTagNodeFixture351

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 25000
set_option maxHeartbeats 11000000
namespace Yulang.GeneralDeclarativeWitnessTagMix351
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeWitnessOrigins350 (Table Attached attach)
open GeneralDeclarativeWitnessTagSources351 (Inline Named NamedBounds Script Ref inline named directBounds)
open GeneralDeclarativeWitnessTagLocal351 (parse context)
open GeneralDeclarativeWitnessBound349 (Range fits bounds_sound)
open GeneralDeclarativeWitnessCompiler350 (Context Finished execute)
open GeneralDeclarativeWitnessTagFixture351 (sourceUpper firstArm lastArm ref atUpper span)
open GeneralDeclarativeTaggedFixture340 (a d chosen registry keep fallback targets outer)
open GeneralDeclarativeHiddenDecl324 (catalogue interpretation)
open GeneralDeclarativePlainFixture323 (source)

/-- A direct literal is already a legitimate named-route outcome.
The conversion uses its original anchored row; the converse is
not provided and would be false for a recursively named arm. -/
def asNamed {s : State} {t : Table} {auth : Attached s t} {n tag : Nat}
    (got : Inline auth n tag) : Named auth tag (.variable n) :=
  ⟨got.payload,GeneralDeclarativeTaggedNamed340.prior got.read⟩

def lowerDirect {s : State} {t : Table} (auth : Attached s t) (arg : Capture)
    (tag : Nat) (claim : Range) (lower : Ref) (upper : Script) : Option (NamedBounds auth arg tag) := do
  if okay : fits s arg claim = true then
    let l ← inline auth arg.lower tag lower
    let h ← named auth tag (.variable arg.upper) upper
    pure ⟨asNamed l,h,bounds_sound okay⟩
  else none

def lowerRow : Equation := ⟨0,outer⟩
def state : State := ⟨⟨[],[(0,1),(1,2)]⟩,[lowerRow,sourceUpper,firstArm,lastArm]⟩
def backed : Table := ⟨[lowerRow,sourceUpper,firstArm],[(lastArm,19)],[19]⟩

def one (rows : Table) : Option Context := do
  let aLive ← attach state rows
  let binding ← lowerDirect aLive a 7 span (ref 0) atUpper
  let pat ← parse catalogue interpretation source 7
  pure (context (r := registry) d chosen (.named binding) pat keep fallback targets)

theorem hybrid_compiles :
    (((one backed).bind execute).map (fun f => decide (f.fixed = [⟨6,.variable 13⟩]) &&
      f.kids.isEmpty)).getD false = true := by decide +kernel

theorem hybrid_keeps_upper_source_requirement :
    (one {backed with released := []}).isSome = false := by decide +kernel

theorem cannot_use_direct_for_both :
    ((attach state backed).map (fun t => (directBounds t a 7 span (ref 0) (ref 1)).isSome)).getD false
      = false := by decide +kernel


def upperDirect {s : State} {t : Table} (auth : Attached s t) (arg : Capture)
    (tag : Nat) (claim : Range) (lower : Script) (upper : Ref) : Option (NamedBounds auth arg tag) := do
  if okay : fits s arg claim = true then
    let l ← named auth tag (.variable arg.lower) lower
    let h ← inline auth arg.upper tag upper
    pure ⟨l,asNamed h,bounds_sound okay⟩
  else none

def upperRow : Equation := ⟨2,outer⟩
def upperMixed : State := ⟨state.normal,
  [GeneralDeclarativeWitnessTagFixture351.sourceLow,upperRow,firstArm,lastArm]⟩
def upperBacked : Table :=
  ⟨[GeneralDeclarativeWitnessTagFixture351.sourceLow,upperRow,firstArm],[(lastArm,19)],[19]⟩

def upperOne (rows : Table) (relation : Range) : Option Context := do
  let aLive ← attach upperMixed rows
  let binding ← upperDirect aLive a 7 relation GeneralDeclarativeWitnessTagFixture351.atLower (ref 1)
  let pat ← parse catalogue interpretation source 7
  pure (context (r := registry) d chosen (.named binding) pat keep fallback targets)

theorem other_hybrid_compiles :
    (((upperOne upperBacked span).bind execute).map (fun f => decide (f.fixed = [⟨6,.variable 13⟩]) &&
      f.kids.isEmpty)).getD false = true := by decide +kernel

theorem literal_upper_does_not_replace_missing_lower :
    (upperOne {upperBacked with released := []} span).isSome = false := by decide +kernel

theorem endpoints_must_belong_to_actual_interval :
    (upperOne upperBacked ⟨.interval 1,.interval 0⟩).isSome = false := by decide +kernel


def wrongTagArm : Equation := ⟨4,.variant 8 GeneralDeclarativeTaggedFixture340.eBool⟩
def wrongTagState : State := ⟨state.normal,[lowerRow,sourceUpper,firstArm,wrongTagArm]⟩
def wrongTagView : Table := ⟨[lowerRow,sourceUpper,firstArm],[(wrongTagArm,19)],[19]⟩

/-- A released arm of another tag is not evidence for a same-tag merge.
This is a recognition failure, not a language verdict about mixed tags. -/
theorem different_tag_does_not_supply_same_tag_payload :
    ((attach wrongTagState wrongTagView).map (fun t =>
      (lowerDirect t a 7 span (ref 0) atUpper).isSome)).getD false = false := by decide +kernel

end Yulang.GeneralDeclarativeWitnessTagMix351
