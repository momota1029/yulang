import Yulang.GeneralDeclarativeI65I74RecordRule412
import Yulang.GeneralDeclarativeWitnessModeDeclaration357

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RecordK2412
open GeneralDeclarativeI65
open GeneralDeclarationPatterns (Pattern normalize normalizeArgs substArgs counted encodeArgs
  CountsCovered Smaller ConservativeSmaller StableSmaller checkSmaller_exact lowerArgs checkSmaller)
open GeneralDeclarativeWitnessChecks349 (counts ids identified binds produced lexical output_only names scope_sound)
open GeneralDeclarativeWitnessProblem349 (splitAnd)
open GeneralDeclarativeWitnessModeCoverage357 (DeclarationCovered)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeWitnessSignature349 (checked_signature)
open GeneralDeclarations (Clause Declaration DeclarationChecked)

theorem closed_nested_record_stable412 (box tick empty binder : Nat) :
    StableSmaller [closedHead412 box tick empty binder] [closedWhere412 box empty binder] := by
  intro capture
  constructor
  · simp [closedHead412,closedWhere412,counted,substArgs,Pattern.subst,normalizeArgs,normalize,encodeArgs,Pattern.encode,
      Roles.argsSize,Roles.Term.size] <;> omega
  · intro q
    simp [closedHead412,closedWhere412,counted,substArgs,Pattern.subst,normalizeArgs,normalize,encodeArgs,Pattern.encode,
      Roles.argsOccurrences,Roles.Term.occurrences]

def recordDescent412 (head child : List Pattern) : Bool :=
  (counts head child && checkSmaller head child) &&
    CheckedRoles.checkCondition (lowerArgs (normalizeArgs head)) ⟨0,counted child⟩

theorem checked_closed_record_descent412 {box tick empty binder : Nat}
    (ok : recordDescent412 [closedHead412 box tick empty binder] [closedWhere412 box empty binder] = true) :
    CountsCovered [closedHead412 box tick empty binder] [closedWhere412 box empty binder] ∧
    Smaller [closedHead412 box tick empty binder] [closedWhere412 box empty binder] ∧
    ConservativeSmaller [closedHead412 box tick empty binder] [closedWhere412 box empty binder] ∧
    StableSmaller [closedHead412 box tick empty binder] [closedWhere412 box empty binder] :=
  ⟨splitAnd (splitAnd (splitAnd ok).1).1,
    (checkSmaller_exact ..).mp (splitAnd (splitAnd ok).1).2,
    (splitAnd ok).2,closed_nested_record_stable412 box tick empty binder⟩

def header412 (s : GeneralDeclarativeWitnessDeclaredState357.Current) (d : Declaration) : Bool :=
  let source := s.environment.source
  (GeneralDeclarativeWitnessSignature349.checks source.roles d &&
    ids d) && ((binds d && lexical d) && names d)

theorem checked_record_header412 {s : GeneralDeclarativeWitnessDeclaredState357.Current}
    {d : Declaration} {c : Clause} {box tick empty binder : Nat}
    (cov : DeclarationCovered s.environment d) (header : header412 s d = true)
    (head : d.head = [closedHead412 box tick empty binder])
    (only : d.requirements = [c]) (body : c.arguments = [closedWhere412 box empty binder])
    (desc : recordDescent412 d.head c.arguments = true) :
    DeclarationChecked (authoredRegistry s).constructors (authoredRegistry s).roles d := by
  obtain ⟨top,tail⟩ := splitAnd header
  obtain ⟨sg,ix⟩ := splitAnd top
  obtain ⟨b,scope⟩ := splitAnd tail
  obtain ⟨prod,lex⟩ := splitAnd b
  have tested := checked_closed_record_descent412 (head ▸ body ▸ desc)
  refine ⟨checked_signature sg,identified ix,produced prod,output_only lex,scope_sound scope,
    GeneralDeclarativeWitnessModeDeclaration357.scoped_decl cov,?_,?_,?_,?_⟩
  all_goals
    intro x seen
    rw [only] at seen
    cases List.mem_singleton.mp seen
    rw [head,body]
  · exact tested.1
  · exact tested.2.1
  · exact tested.2.2.1
  · exact tested.2.2.2

end Yulang.GeneralDeclarativeI65.I72.RecordK2412
