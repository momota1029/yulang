import Yulang.GeneralDeclarativeNestedRebuild332
import Yulang.GeneralDeclarativeInlineMaterial331

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeNestedMaterial332
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeInlineTrace331 (Read realize)
open GeneralDeclarativeInlineAllocation331 (captures renamed actual_capture name_walk bounded jobs)
open GeneralDeclarativeInlineMaterial331 (ordinary named seed protect)
open GeneralDeclarativeNestedRebuild332 (rebuild computed)
open GeneralDeclarativeTermOccurrences322 (actual_positions)
open GeneralDeclarativeTermWalk322 (Occurrence)
open GeneralDeclarativeEntailment320 (Entails appendFacts model_append conservative_append)
open GeneralDeclarativeNewNames321 (old_plus_extra)
open GeneralDeclarativeGrowth327 (Extends trans facts fits)
open GeneralDeclarativeOpaqueConserve328 (Retains)
open GeneralDeclarativeStableReads329 (One)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans)
open GeneralDeclarationPatterns (normalize)

def assemble (s : State) (arg : Capture) (fixed : List Nat) (code : Expr)
    (uses : List Occurrence) : Option (State × List (Nat × Capture)) := do
  let n := seed s arg fixed uses
  let (body,over) ← rebuild code (renamed n uses)
  if over.isEmpty then
    pure (appendFacts (named s arg fixed uses) [⟨arg.center,body⟩],captures n uses)
  else none

/-- The same named state and spans are computable. This is an
ordinary syntax-driven head row preserving all existing model
coordinates; it acquires no new source origin. -/
theorem assemble_exact {s : State} {p : Supported s done}
    (box : Bounds s a) (printed : translate c i (normalize pat) = some code)
    (fromSource : Read (restriction p) .actual (.variable a.center) code used) (fixed : List Nat) :
    ∃ out spans, assemble s a fixed code used = some (out,spans) ∧
      Retains s out fixed ∧ One out c i a pat spans ∧
      ordinary s a fixed used ⊆ out.equations ∧ (∀ o ∈ spans, Bounds out o.2) ∧
      ∀ m, Models out m ↔ Models (named s a fixed used) m := by
  let old := named s a fixed used
  let n := seed s a fixed used
  let batch := ordinary s a fixed used
  obtain ⟨raw,truth,walk⟩ := realize fromSource
  obtain ⟨rebuilt,definition,exactWalk⟩ := name_walk walk n
  have rawPrinted : rebuild code (renamed n used) = some (rebuilt,[]) := by
    simpa only [List.append_nil] using computed exactWalk []
  have positions := (actual_positions walk).2
  rw [actual_capture n used positions] at exactWalk
  let readRow : Equation := ⟨a.center,rebuilt⟩
  let state := appendFacts old [readRow]
  have written : Extends s state := trans (facts _ _) (facts _ _)
  have supportedEq : Entails old readRow := by
    intro m valid
    obtain ⟨previous,definitions⟩ := (model_append (s := s) (rows := batch) m).mp valid
    exact eqv_trans (truth m previous) (definition m definitions)
  refine ⟨state,captures n used,?_,⟨written,?_⟩,⟨fits written box,_,rebuilt,printed,
      .row (List.mem_append_right _ List.mem_cons_self),exactWalk⟩,
    (fun _ e => List.mem_append_left _ (List.mem_append_right _ e)),bounded state n used,?_⟩
  · unfold assemble
    change (do
      let (body,over) ← rebuild code (renamed n used)
      if over.isEmpty then pure (appendFacts old [⟨a.center,body⟩],captures n used) else none) =
        some (state,captures n used)
    simp [rawPrinted,state,readRow]
  · intro m valid
    obtain ⟨lift,kept⟩ := old_plus_extra s (protect a fixed used) (jobs used) m valid
    refine ⟨_,(conservative_append (s := old) (fun e occurred => ?_) _).mpr lift,?_⟩
    · cases List.mem_singleton.mp occurred
      exact supportedEq
    · intro k sees
      rcases List.mem_append.mp sees with already|target
      · exact kept k (List.mem_append_left _ already)
      · exact kept k (List.mem_append_right _ (List.mem_append_left _ (List.mem_append_right _ target)))
  · intro m
    exact conservative_append (s := old) (rows := [readRow]) (fun e occurred => by
      cases List.mem_singleton.mp occurred
      exact supportedEq) m

theorem computed_frame {s : State} {p : Supported s done}
    (box : Bounds s a) (printed : translate c i (normalize pat) = some code)
    (fromSource : Read (restriction p) .actual (.variable a.center) code used)
    (checked : assemble s a fixed code used = some (out,spans)) :
    Retains s out fixed ∧ One out c i a pat spans ∧ ordinary s a fixed used ⊆ out.equations ∧
      (∀ o ∈ spans, Bounds out o.2) ∧ ∀ m, Models out m ↔ Models (named s a fixed used) m := by
  obtain ⟨t,captures,result,data⟩ := assemble_exact box printed fromSource fixed
  have same := Option.some.inj (result.symm.trans checked)
  cases same
  exact data

end Yulang.GeneralDeclarativeNestedMaterial332
