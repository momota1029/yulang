import Yulang.GeneralDeclarativeWitnessAssociatedFixture359

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 51000
set_option maxHeartbeats 44000000
namespace Yulang.GeneralDeclarativeWitnessPlannedComparison359
open GeneralDeclarativeWitnessAssociatedDescriptor359 (Wire Described describe authorized_inputs_only)
open GeneralDeclarativeWitnessScopedBindings359 (Frame FrameKey slots attached)
open GeneralDeclarativeWitnessNominalSource359 (Route Location Built build AtSource)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarativeWitnessFullIntervals357 (ContextDerives compiled_full_exact)
open GeneralDeclarativeWitnessSparseIntervals357 (Compiled compile)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeHead320 (Models)
open GeneralNominalCommonBridge (Assignment)
open CommonDeclaredNominalInspection (Registry)
open CommonRecursiveNominalIntervals (ContextWellFormed)
open CommonNominalFullCarrier (model)

structure Plan (e : Environment) (table : Registry) (fs : List Frame)
    (writer receiver : FrameKey) (d : Demand) (wire : Wire) (site : Location) (read : Route) where
  produced : Described e table fs writer d wire
  useSite : attached receiver site
  expected : Built e table (slots fs receiver) false site read
  comparison : Compiled e table false produced.endpoint expected.endpoint

def plan (e : Environment) (table : Registry) (fs : List Frame)
    (writer receiver : FrameKey) (d : Demand) (wire : Wire) (site : Location)
    (read : Route) : Option (Plan e table fs writer receiver d wire site read) :=
  if exactSite : attached receiver site then do
    let produced ← describe e table fs writer d wire
    let expected ← build e table (slots fs receiver) false site read
    let comparison ← compile e table false produced.endpoint expected.endpoint
    pure ⟨produced,exactSite,expected,comparison⟩
  else none

/-- This is dependent comparison of two descriptions, not installation
at the fixed target, release of an output, or success of a where body. -/
theorem scoped_plan_meaning {e table fs writer receiver d wire site read}
    (agrees : Plan e table fs writer receiver d wire site read) (m : Assignment)
    (verifies : ∀ atom ∈ agrees.comparison.rows,atom.Holds model m) :
    d.outputs[wire.ordinal]? = some agrees.produced.requested ∧
    agrees.produced.requested.target = wire.target ∧ AtSource e site read ∧
    ContextWellFormed table false agrees.produced.endpoint ∧
    ContextWellFormed table false agrees.expected.endpoint ∧
    ContextDerives table m false agrees.produced.endpoint agrees.expected.endpoint :=
  ⟨agrees.produced.indexed,agrees.produced.fixed,agrees.expected.source,
    (compiled_full_exact table m false _ _).mp
      ⟨agrees.comparison.rows,agrees.comparison.exact,verifies⟩⟩

open GeneralDeclarativeWitnessNominalRecordFixture359
  (current exactAtoms genuine common_source_model generated_checks_follow_from_authored_base route last)
open GeneralDeclarativeWitnessJointObservation359 (parentScope secondScope secondSpan)
open GeneralDeclarativeWitnessAssociatedFixture359 (available request frames wires)
open GeneralDeclarativeWitnessInheritedModeFixture357 (table)

def allFrames : List Frame := frames ++ [⟨secondScope,[(81,secondSpan)]⟩]
def firstWrite (negative : Bool) : Wire := ⟨0,111,101,route negative 80⟩

def trial (e : Environment) (negative : Bool) :=
  plan e table allFrames parentScope secondScope request (firstWrite negative) last (route negative 81)

theorem output_descriptor_keeps_context (negative : Bool) :
    ((available negative).bind fun e => (trial e negative).map (fun a => a.comparison.rows)) =
      some exactAtoms := by cases negative <;> decide +kernel

theorem true_source_keeps_target (negative : Bool) (m : Assignment)
    (fits : Models current m) :
    ∃ (e : Environment) (a : Plan e table allFrames parentScope secondScope request (firstWrite negative) last (route negative 81)),
      available negative = some e ∧ a.produced.requested.target = 101 ∧
      ContextDerives table m false a.produced.endpoint a.expected.endpoint := by
  have ran := output_descriptor_keeps_context negative
  cases loaded : available negative with
  | none => rw [loaded] at ran; cases ran
  | some e =>
    rw [loaded] at ran
    change (trial e negative).map (fun a => a.comparison.rows) = _ at ran
    cases outcome : trial e negative with
    | none => simp [outcome] at ran
    | some a =>
      have exactRows : a.comparison.rows = exactAtoms := by simpa [outcome] using ran
      have reads := scoped_plan_meaning a m
        (fun atom used => generated_checks_follow_from_authored_base m fits atom (exactRows ▸ used))
      exact ⟨e,a,rfl,reads.2.1,reads.2.2.2.2.2⟩

end Yulang.GeneralDeclarativeWitnessPlannedComparison359
