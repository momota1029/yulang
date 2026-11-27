import Yulang.GeneralDeclarativeI65I74FiniteCaptureBoundary462
import Yulang.GeneralDeclarativeWitnessVarianceFixtures357

set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
namespace Yulang.GeneralDeclarativeI65.I72.EligibleFieldStart461.FiniteCapture462QA
open Yulang.GeneralDeclarativeI65
open GeneralDeclarationPatterns (Pattern StableSmaller Smaller counted substArgs)
open GeneralDeclarations (Declaration Clause)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralSourceMetadataRows291 (Row)
open GeneralDeclarativeWitnessVarianceFixtures357 (source)
open GeneralDeclarativeWitnessSparseVariance357 (compile)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarativeWitnessDeclaredState357 (point authoredRegistry)
open GeneralDeclarativeWitnessClassifyVariance357 (DeclarationReady)
open RetainedFull445
open WrittenPattern460

private def intTy : Pattern := .app 4 []
private def x : Pattern := .var 3
private def pairPat (left right : Pattern) : Pattern := .app 8 [left,right]
private def head : Pattern :=
  pairPat x (.join (.variant 7 (pairPat intTy x)) (.variant 7 (pairPat x intTy)))
private def condition : Pattern := pairPat x (.variant 7 (pairPat x x))
private def where_ : Clause := ⟨60,19,[condition],[]⟩
private def declaration : Declaration := ⟨218,19,[head],[where_],[],[]⟩

private def sourceMeta : InputBundle :=
  let keys : List Row := [⟨4,some ⟨[],4⟩,.primitive (.scalar .int)⟩,
    ⟨8,some ⟨[.type,.type],8⟩,.primitive .pair⟩]
  ⟨⟨.absent,keys⟩,⟨.absent,keys⟩,⟨0,[⟨19,1,[]⟩]⟩,[declaration]⟩

private def input : Option FullProblem := do
  let modes ← compile source
  let bundle ← GeneralSourceMetadataBareBundle291.compile sourceMeta
  let env : Environment := ⟨3,2,0,source,modes,bundle⟩
  let core : CoreState := ⟨⟨env,⟨⟨[],[]⟩,[]⟩,[]⟩,[],[],[]⟩
  let atlas : B6OccurrenceAtlas401 core := ⟨fun _ _ _ _ => none⟩
  pure (liftProblem ⟨⟨core,atlas⟩,⟨[71,2],⟨19,[point 0],[]⟩⟩⟩)

private def p : FullProblem := input.get (by decide +kernel)
private def shell := readFiniteSourceShell p.old ⟨0,0,0⟩

/-- info: [true, true, true] -/
#guard_msgs in
#eval [shell.isSome,GeneralDeclarationPatterns.checkSmaller [head] [condition],
  (readFiniteSourceShell p.old ⟨0,0,1⟩).isNone]

open FiniteCaptureBoundary462
private def failing : CaptureTable := [(3,intTy)]
private def noCapture : CaptureTable := []
private def onlyIrrelevantName : CaptureTable := [(999,intTy)]
private def filteredShadow : CaptureTable := [(3,.var 10),(3,intTy)]

/-- info: [true, false, false, false] -/
#guard_msgs in
#eval [badCapture [head] [condition] failing,badCapture [head] [condition] noCapture,
  badCapture [head] [condition] onlyIrrelevantName,badCapture [head] [condition] filteredShadow]

theorem finite_bad_capture_refutes_exact_authored_ready_not_initial_shell462
    (a : OriginalAnchor p.old)
    (shell : StartShell p.old a)
    (whichHead : a.original = head) (whichClause : a.clause = where_) :
    ¬ DeclarationReady (authoredRegistry p.old.state.core.current) a.declaration := by
  apply (actual_shell_readiness_failure_iff_finite_bad_capture shell).mpr
  refine ⟨failing,?_⟩
  rw [(shell_is_bound_to_the_single_actual_source_and_its_locations shell).2.2.1,whichHead,whichClause]
  decide +kernel

theorem concrete_capture_table_has_real_authored_shell462 :
    (readFiniteSourceShell p.old ⟨0,0,0⟩).isSome = true ∧ badCapture [head] [condition] failing = true := by
  decide +kernel

#print axioms finite_bad_capture_refutes_exact_authored_ready_not_initial_shell462
#print axioms concrete_capture_table_has_real_authored_shell462
end Yulang.GeneralDeclarativeI65.I72.EligibleFieldStart461.FiniteCapture462QA
