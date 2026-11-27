import Yulang.GeneralDeclarativeI65I74FiniteSourceShell461
import Yulang.GeneralDeclarativeWitnessVarianceFixtures357

set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
namespace Yulang.GeneralDeclarativeI65.I72.EligibleFieldStart461.LateCaptureQA
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

private def concreteCapture (n : Nat) : Pattern := if n = 3 then intTy else .var n

theorem authored_coalescence_after_capture_destroys_strict_descent :
    ¬ StableSmaller [head] [condition] := by
  intro old
  have mono := (old concreteCapture).1
  have equal : counted (substArgs concreteCapture [head]) =
      counted (substArgs concreteCapture [condition]) := by
    unfold head condition x pairPat intTy concreteCapture counted
    simp [substArgs,Pattern.subst,GeneralDeclarationPatterns.normalizeArgs,
      GeneralDeclarationPatterns.normalize,GeneralDeclarationPatterns.merge]
    simp [intTy,GeneralDeclarationPatterns.normalize,GeneralDeclarationPatterns.normalizeArgs]
  rw [equal] at mono
  exact (Nat.lt_irrefl _) mono

theorem finite_same_source_shell_does_not_supply_late_stability
    (a : OriginalAnchor p.old)
    (h : StartShell p.old a)
    (headIs : a.original = head) (whereIs : a.clause = where_) :
    ¬ DeclarationReady (authoredRegistry p.old.state.core.current) a.declaration := by
  have locations := shell_is_bound_to_the_single_actual_source_and_its_locations h
  have equivalence := actual_shell_ready_iff_same_original_stable_capture h
  intro ready
  have stability := equivalence.mp ready
  rw [locations.2.2.1,headIs,whereIs] at stability
  exact authored_coalescence_after_capture_destroys_strict_descent stability

theorem actual_visible_source_cannot_be_ready_despite_static_decrease :
    visible p.state.base.core p.root = [declaration] ∧
    ¬ DeclarationReady (authoredRegistry p.state.base.core.current) declaration := by
  refine ⟨by decide +kernel,?_⟩
  intro ready
  exact authored_coalescence_after_capture_destroys_strict_descent
    (ready.descent where_ List.mem_cons_self).2

#print axioms actual_visible_source_cannot_be_ready_despite_static_decrease
#print axioms authored_coalescence_after_capture_destroys_strict_descent
#print axioms finite_same_source_shell_does_not_supply_late_stability

end Yulang.GeneralDeclarativeI65.I72.EligibleFieldStart461.LateCaptureQA
