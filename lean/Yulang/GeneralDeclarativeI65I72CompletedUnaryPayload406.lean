import Yulang.GeneralDeclarativeI65I72CompletedUnaryGate406

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72
open GeneralDeclarativeI65
open CommonRecursiveNominalIntervals (Endpoint)
open GeneralDeclarativeWhere319 (Capture InInterval)
open GeneralDeclarativeDemand320 (Bounds bounds_sound)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)

def literalUnaryPayloadName406 (key : Nat) : Endpoint Nat → Option Nat
  | .nominal constructor [.inl (.point (.ordinary (.var name)))] =>
    if constructor = key then some name else none
  | _ => none

theorem unary_payload_name_read_exact406 {key name : Nat} {original : Endpoint Nat} :
    literalUnaryPayloadName406 key original = some name ↔ original = unaryNominalPoint404 key name := by
  constructor
  · intro found
    cases original with
    | ordinary => cases found
    | nominal c args =>
      cases args with
      | nil => cases found
      | cons first rest =>
        cases rest with
        | cons => simp [literalUnaryPayloadName406] at found
        | nil =>
          cases first with
          | inr => cases found
          | inl bounds =>
            cases bounds with
            | interval => cases found
            | point point =>
              cases point with
              | nominal => cases found
              | ordinary expression =>
                cases expression with
                | var payload =>
                  change (if c=key then some payload else none) = some name at found
                  split at found
                  · subst c
                    cases found
                    rfl
                  · cases found
                | _ => cases found
  · rintro rfl
    simp [literalUnaryPayloadName406,unaryNominalPoint404]

/-- Read the original typed input indication at this *consumer*
occurrence, argument 0 and actual constructor's value path [0].
This is an existing stored Origin at the whole actual input name;
it is not the lower Origin that may be absent for this branch.
Neither endpoint payload is used to pick the name. -/
structure OriginalPayload406 {s q row needs forest}
    (chosen : PreselectedUnary406 s q row (needs := needs) forest) where
  source : Origin
  authored : source ∈ s.core.origins
  originalRoute : OriginRoute s.core source chosen.gate.arg.center
  center : Nat
  exactPath : literalUnaryPayloadName406 chosen.gate.key source.endpoint = some center
  retainedBounds : Bounds s.core.current.ordinary ⟨chosen.gate.lowerPayload,center,chosen.gate.upperPayload⟩

/-- Given an available original syntax indication, the name is
decoded from the typed value payload itself. No extra name or
agreement with an endpoint is a premise of the construction. -/
def readOriginalUnaryPayload406 {s q row needs forest}
    (chosen : PreselectedUnary406 s q row (needs := needs) forest)
    (input : Origin) (available : input ∈ s.core.origins)
    (exact : OriginRoute s.core input chosen.gate.arg.center)
    (bounds : ∀ c, literalUnaryPayloadName406 chosen.gate.key input.endpoint = some c →
      Bounds s.core.current.ordinary ⟨chosen.gate.lowerPayload,c,chosen.gate.upperPayload⟩) :
    Option (OriginalPayload406 chosen) :=
  match hit : literalUnaryPayloadName406 chosen.gate.key input.endpoint with
  | none => none
  | some c => some ⟨input,available,exact,c,hit,bounds c hit⟩

def OriginalPayload406.interval {s q row needs forest}
    {chosen : PreselectedUnary406 s q row (needs := needs) forest} (input : OriginalPayload406 chosen) : Capture :=
  ⟨chosen.gate.lowerPayload,input.center,chosen.gate.upperPayload⟩

def OriginalPayload406.names {s q row needs forest}
    {chosen : PreselectedUnary406 s q row (needs := needs) forest} (input : OriginalPayload406 chosen) : Nat → Capture :=
  fun n => if n = chosen.gate.binder then input.interval else emptyCapture403

def originalNativeFrame406 {s q row needs forest}
    (chosen : PreselectedUnary406 s q row (needs := needs) forest) (name : OriginalPayload406 chosen) :
    AuthoredBodyFrame393 s.core q :=
  frameAtSource395 (by simp [chosen.gate.only]) chosen.authoredOrdinal chosen.declarationAt unusedPlacement403 name.names

theorem original_payload_names_the_exact_native_capture406 {s q row needs forest}
    {chosen : PreselectedUnary406 s q row (needs := needs) forest}
    (payload : OriginalPayload406 chosen) (m : Model) (fit : Fits s m) :
    q.demand.arguments[0]? = some chosen.gate.arg ∧
    OriginRoute s.core payload.source chosen.gate.arg.center ∧
    m.nativeSyntax payload.source.slot = some (unaryNominalPoint404 chosen.gate.key
      ((originalNativeFrame406 chosen payload).input chosen.gate.binder).center) ∧
    ((originalNativeFrame406 chosen payload).input chosen.gate.binder).lower = chosen.gate.lowerPayload ∧
    ((originalNativeFrame406 chosen payload).input chosen.gate.binder).upper = chosen.gate.upperPayload ∧
    ((originalNativeFrame406 chosen payload).input chosen.gate.binder).center = payload.center ∧
    InInterval (m.assignment chosen.gate.lowerPayload).1 (m.assignment chosen.gate.upperPayload).1
      (m.assignment payload.center).1 := by
  have literal : (originalNativeFrame406 chosen payload).input chosen.gate.binder = payload.interval := by
    change payload.names chosen.gate.binder = payload.interval
    simp [OriginalPayload406.names]
  rw [literal]
  refine ⟨by simp [chosen.gate.exactArg],payload.originalRoute,?_,rfl,rfl,rfl,
    bounds_sound payload.retainedBounds m.assignment fit.1.1⟩
  change m.nativeSyntax payload.source.slot = some (unaryNominalPoint404 chosen.gate.key payload.center)
  exact (fit.2 _ payload.authored).trans (congrArg some (unary_payload_name_read_exact406.mp payload.exactPath))

theorem if_original_path_name_differs_capture_keeps_both_differences406 {s q row needs forest}
    {chosen : PreselectedUnary406 s q row (needs := needs) forest} (payload : OriginalPayload406 chosen)
    (differentLower : payload.center ≠ chosen.gate.lowerPayload)
    (differentUpper : payload.center ≠ chosen.gate.upperPayload) :
    ((originalNativeFrame406 chosen payload).input chosen.gate.binder).center ≠ chosen.gate.lowerPayload ∧
    ((originalNativeFrame406 chosen payload).input chosen.gate.binder).center ≠ chosen.gate.upperPayload := by
  change (payload.names chosen.gate.binder).center ≠ _ ∧ (payload.names chosen.gate.binder).center ≠ _
  simp [OriginalPayload406.names,OriginalPayload406.interval,differentLower,differentUpper]

/-- The current source carrier's missing input is precise. This does
not negate the preselection theorem: lacking this original authored
indication does not let a guard guess or deny. A separately supplied
logical B6 path-name input is not present in the C402 State yet. -/
theorem missing_original_input_prevents_this_readback_only406 {s q row needs forest}
    (chosen : PreselectedUnary406 s q row (needs := needs) forest)
    (missing : ∀ o : Origin, o ∈ s.core.origins → ¬OriginRoute s.core o chosen.gate.arg.center) :
    ¬Nonempty (OriginalPayload406 chosen) := by
  rintro ⟨a⟩
  exact missing a.source a.authored a.originalRoute

end Yulang.GeneralDeclarativeI65.I72
