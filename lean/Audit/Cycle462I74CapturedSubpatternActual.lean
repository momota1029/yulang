import Yulang.GeneralDeclarativeI65I74CapturedSubpattern462
import Yulang.GeneralDeclarativeI65I74CapturedStabilityCertificate462
import Yulang.GeneralDeclarativeI65I74FiniteCaptureBoundary462
import Yulang.GeneralDeclarativeWitnessVarianceFixtures357

set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
namespace Yulang.GeneralDeclarativeI65.I72.EligibleFieldStart461.CapturedSubpattern462QA
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
  pairPat (.variant 7 (pairPat x intTy)) (.join (.variant 9 x) (.variant 10 x))
private def condition : Pattern := pairPat x intTy
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

open CapturedSubpattern462
open CapturedNormalForm462
open FiniteCaptureBoundary462
def chosen : List Edge := [.argument 0,.tagValue]

/-- info: [true, false, false, false, false, false] -/
#guard_msgs in
#eval [checkStrictSubtree [head] [condition] chosen,
  checkStrictSubtree [head] [condition] [.argument 1,.tagValue],
  checkStrictSubtree [head] [condition] [.argument 0],
  checkStrictSubtree [head] [condition] [],verifiesStable 9 [head] [condition],
  badCapture [head] [condition] [(3,intTy)]]

theorem actual_retained_subpattern_is_stable_beyond_closed_profile462 :
    StableSmaller [head] [condition] ∧ ∀ key, verifiesStable key [head] [condition] = false := by
  constructor
  · apply nonempty_actual_subtree_is_stable_under_every_capture (path := chosen)
    · exact structural_subtree_exact_finite_address.mp (by decide +kernel)
    · simp [chosen]
  · intro key
    simp [verifiesStable,head,condition,pairPat,x,intTy,simplifyArgs,simplify,
      RecordTree455.checkTrees,RecordTree455.checkTree]

theorem actual_subpattern_proves_the_same_original_ready462 :
    visible p.old.state.core p.old.root = [declaration] ∧
      DeclarationReady (authoredRegistry p.old.state.core.current) declaration := by
  have sourceBits : RecordTrail455.localAuthorBits p.old.state.core.current.environment declaration = true := by
    decide +kernel
  obtain ⟨cover,sig,id,produced,outputOnly,lexicalScope⟩ := (RecordTrail455.local_author_bits_exact455 ..).mp sourceBits
  refine ⟨by decide +kernel,⟨sig,id,produced,outputOnly,lexicalScope,
    GeneralDeclarativeWitnessModeDeclaration357.scoped_decl cover,?_⟩⟩
  intro c chosen
  have same : c = where_ := List.mem_singleton.mp chosen
  subst c
  have stable := actual_retained_subpattern_is_stable_beyond_closed_profile462.1
  refine ⟨?_,stable⟩
  change Smaller [head] [condition]
  simpa only [IdenticalTagProjection459.identity_args_capture_spells_original459] using stable Pattern.var

#print axioms actual_retained_subpattern_is_stable_beyond_closed_profile462
#print axioms actual_subpattern_proves_the_same_original_ready462
end Yulang.GeneralDeclarativeI65.I72.EligibleFieldStart461.CapturedSubpattern462QA
