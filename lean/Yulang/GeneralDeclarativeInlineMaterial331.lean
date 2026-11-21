import Yulang.GeneralDeclarativeInlineAllocation331
import Yulang.GeneralDeclarativeObserverGrowth330

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeInlineMaterial331
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeInlineTrace331 (Read realize)
open GeneralDeclarativeInlineAllocation331 (jobs renamed captures bounded actual_capture name_walk)
open GeneralDeclarativeTermWalk322 (Occurrence Walk)
open GeneralDeclarativeTermOccurrences322 (actual_positions)
open GeneralDeclarativeStableReads329 (One)
open GeneralDeclarativeGrowth327 (Extends trans facts fits)
open GeneralDeclarativeOpaqueConserve328 (Retains)
open GeneralDeclarativeEntailment320 (Entails Holds appendFacts model_append conservative_append)
open GeneralDeclarativeRecordPoints330 (fieldName)
open GeneralDeclarativeNewNames321 (after supply old_plus_extra supply_avoids)
open GeneralDeclarativeTraceNames321 (names)
open GeneralDeclarativeFootprint321 (stateNames)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans)
open GeneralDeclarationPatterns (normalize)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeObserverGrowth330 (preserve backed_same)

def protect (arg : Capture) (targets : List Nat) (uses : List Occurrence) : List Nat :=
  [arg.lower,arg.center,arg.upper] ++ targets ++ uses.flatMap (fun o => names o.term)
def seed (s : State) (arg : Capture) (targets : List Nat) (uses : List Occurrence) : Nat :=
  after ((stateNames s ++ protect arg targets uses) ++ (jobs uses).flatMap names)
def ordinary (s : State) (arg : Capture) (targets : List Nat) (uses : List Occurrence) : List Equation :=
  supply s (protect arg targets uses) (jobs uses)
def named (s : State) (arg : Capture) (targets : List Nat) (uses : List Occurrence) : State :=
  appendFacts s (ordinary s arg targets uses)

theorem old_names_protected {s : State} {e : Equation}
    (written : e ∈ ordinary s arg targets uses)
    (old : n ∈ stateNames s ++ protect arg targets uses) : e.left ≠ n :=
  supply_avoids written (List.mem_append_left _ old)

theorem recursive_occurrence_protected {s : State} {e : Equation}
    (written : e ∈ ordinary s arg targets uses) (fromSource : o ∈ uses) (inside : n ∈ names o.term) :
    e.left ≠ n :=
  old_names_protected written (List.mem_append_right _ (List.mem_append_right _
    (List.mem_flatMap.mpr ⟨o,fromSource,inside⟩)))

/-- The result names are completely determined before inspecting any
model. Raw names (with their exact source positions) are retained;
only a captured composite term gets a fresh ordinary definition.
The extra whole-head row merely records the computed model equality.
No row added by this step becomes evidence of a source origin. -/
theorem read {s : State} {p : Supported s done}
    (box : Bounds s a) (shown : translate c i (normalize pat) = some code)
    (fromSource : Read (restriction p) .actual (.variable a.center) code used) (targets : List Nat) :
    ∃ t, Retains s t targets ∧ One t c i a pat (captures (seed s a targets used) used) ∧
      (ordinary s a targets used) ⊆ t.equations ∧
      ∀ o ∈ captures (seed s a targets used) used, Bounds t o.2 := by
  let stage := named s a targets used
  let n := seed s a targets used
  let batch := ordinary s a targets used
  obtain ⟨raw,rootTruth,rootWalk⟩ := realize fromSource
  obtain ⟨rebuilt,namedTruth,namedWalk⟩ := name_walk rootWalk n
  have actual := (actual_positions rootWalk).2
  rw [actual_capture n used actual] at namedWalk
  let readRow : Equation := ⟨a.center,rebuilt⟩
  let state := appendFacts stage [readRow]
  have store : Extends s state := trans (facts _ _) (facts _ _)
  have semantic : Entails stage readRow := by
    intro m valid
    obtain ⟨incoming,batchSound⟩ := (model_append (s := s) (rows := batch) m).mp valid
    exact eqv_trans (rootTruth m incoming) (namedTruth m batchSound)
  refine ⟨state,⟨store,?_⟩,⟨fits store box,_,rebuilt,shown,.row
      (List.mem_append_right _ List.mem_cons_self),namedWalk⟩,
    (fun _ e => List.mem_append_left _ (List.mem_append_right _ e)),bounded state n used⟩
  intro m valid
  obtain ⟨lift,kept⟩ := old_plus_extra s (protect a targets used) (jobs used) m valid
  refine ⟨_,(conservative_append (s := stage) (fun e known => ?_) _).mpr lift,?_⟩
  · cases List.mem_singleton.mp known
    exact semantic
  · intro n old
    rcases List.mem_append.mp old with source|target
    · exact kept n (List.mem_append_left _ source)
    · exact kept n (List.mem_append_right _ (List.mem_append_left _ (List.mem_append_right _ target)))

theorem not_new_origin {s t : State} (p : Supported s done) (grown : Extends s t)
    (row : Equation) : row ∈ (restriction (preserve p grown)).equations ↔ row ∈ (restriction p).equations :=
  backed_same p grown row

end Yulang.GeneralDeclarativeInlineMaterial331
