import Yulang.CommonPatternDeclaredPresence
import Yulang.CommonCaseCoreDataCompletion

/-! Resolved presence validation is performed before the original finite
Core case generator. No source expression or slot is replaced. A blocked
preparation is `none`, whereas ordinary inference failure after successful
presence validation is `some []`; unresolved metadata is therefore not
misreported as an unsatisfiable generated type problem.

This connects declared presence to the existing pure record case family.
Input declarations are the finite resolved metadata at original pattern
positions. Their complete derivation from general source typing, optional
fields without defaults, and principal effect rows remain separate. -/

namespace Yulang.CommonCasePresenceGeneration

set_option backward.isDefEq.respectTransparency false

open Core
open PresenceGeneration (Comp Formula)
open CommonPatternDeclaredPresence (Declarations Legal Report check report check_exact)
open CommonCaseCoreBoundedGeneration (Arm)
open CommonCaseRecordReadout (Specification)
open CommonPatternGenerationProvenance (SafeFormula)

abbrev AnnotatedArm := Declarations × Arm

def original (arms : List AnnotatedArm) : List Arm := arms.map Prod.snd

def SourceLegal (arms : List AnnotatedArm) : Prop :=
  ∀ arm ∈ arms, Legal arm.1 arm.2.1

def checkAll (arms : List AnnotatedArm) : Bool :=
  arms.all fun arm => check arm.1 arm.2.1

def reports (arms : List AnnotatedArm) : List Report :=
  arms.map fun arm => report arm.1 arm.2.1

theorem check_all_exact (arms : List AnnotatedArm) : checkAll arms = true ↔ SourceLegal arms := by
  simp [checkAll, SourceLegal, List.all_eq_true, check_exact]

def generate (specification : Specification) (subject : Required.Term) (arms : List AnnotatedArm) :
    Option (Formula (Fin 3)) :=
  if checkAll arms then
    some (CommonCaseCoreDataPrefixSolved.principal specification subject (original arms))
  else none

def Premises (specification : Specification) (subject : Required.Term) (arms : List AnnotatedArm)
    (input target : Common.Ty) (cap : Common.Row) : Prop :=
  SourceLegal arms ∧
    CommonCaseCoreDataPrefixSolved.Premises specification subject (original arms) input target cap

/-- For every original finite subject and arm list, every resolved metadata
table, and every independent assignment, successful finite generation and
its satisfaction are equivalent to source presence legality and the same
independent Core/coverage/environment premises. Nothing is demanded of a
solver parameter after the family is returned. -/
theorem generate_exact (specification : Specification) (subject : Required.Term)
    (arms : List AnnotatedArm) (assignment : Fin 3 → Comp Common.model) :
    (∃ formula, generate specification subject arms = some formula ∧
      formula.Holds Common.model assignment) ↔
      Premises specification subject arms (assignment 0).1 (assignment 1).1 (assignment 2).2 := by
  cases checked : checkAll arms with
  | false =>
      have illegal : ¬ SourceLegal arms := by
        intro legal
        have accepted := (check_all_exact arms).mpr legal
        simp [checked] at accepted
      simp [generate, checked, Premises, illegal]
  | true =>
      have legal := (check_all_exact arms).mp checked
      simp [generate, checked, Premises, legal, CommonCaseCoreDataPrefixSolved.principal_exact]

theorem generated_safe (specification : Specification) (subject : Required.Term)
    (arms : List AnnotatedArm) (formula : Formula (Fin 3))
    (generated : generate specification subject arms = some formula) : SafeFormula formula := by
  unfold generate at generated
  split at generated
  · cases generated
    exact CommonCaseCoreDataPrefixSolved.principal_safe specification subject (original arms)
  · cases generated

end Yulang.CommonCasePresenceGeneration
