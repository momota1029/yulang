import Yulang.GeneralDeclarativeI65I74CompletedLowerNativeHeader437

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.MergedOutput439
open GeneralDeclarations (Declaration Checked DeclarationChecked)
open GeneralDeclarationPatterns
open GeneralDeclarativeWitnessDeclaredState357 (Current authoredRegistry)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarativeWitnessModeCoverage357 (Coverage DeclarationCovered)
open GeneralDeclarativeWitnessProblem349 (splitAnd)
open GeneralDeclarativeWitnessChecks349 (counts checkedDescent descent_parts ids identified binds produced lexical output_only names scope_sound)

def closedNullaryDescent439 (head child : List Pattern) : Bool :=
  match head, child with
  | [.app _ []],[] =>
    (counts head child && checkSmaller head child) &&
      CheckedRoles.checkCondition (lowerArgs (normalizeArgs head)) ⟨0,counted child⟩
  | _,_ => checkedDescent head child

/-- The original signature/coverage/Paterson/capture conditions stay
the same. The old Boolean's `stableSchema` only recognizes a unary
binder; a closed nullary child needs no capture substitution at all. -/
theorem closed_nullary_descent_sound439 {head child : List Pattern}
    (checked : closedNullaryDescent439 head child = true) :
    CountsCovered head child ∧ Smaller head child ∧ ConservativeSmaller head child ∧ StableSmaller head child := by
  unfold closedNullaryDescent439 at checked
  split at checked
  · next key =>
    have ⟨part,conservative⟩ := splitAnd checked
    have ⟨countedOK,smallerOK⟩ := splitAnd part
    have smaller := (checkSmaller_exact _ _).mp smallerOK
    refine ⟨splitAnd countedOK,smaller,conservative,?_⟩
    intro capture
    change Smaller [.app key []] []
    exact smaller
  · exact descent_parts checked

def checksDeclaration439 (env : Environment) (d : Declaration) : Bool :=
  (GeneralDeclarativeWitnessSignature349.checks env.source.roles d && ids d) &&
    ((binds d && lexical d) &&
      (names d && d.requirements.all (fun c => closedNullaryDescent439 d.head c.arguments)))

theorem checks_declaration_sound439 {s : Current} {d : Declaration}
    (cov : DeclarationCovered s.environment d) (ok : checksDeclaration439 s.environment d = true) :
    DeclarationChecked (authoredRegistry s).constructors (authoredRegistry s).roles d := by
  obtain ⟨top,tail⟩ := splitAnd ok
  obtain ⟨sg,ix⟩ := splitAnd top
  obtain ⟨a,b⟩ := splitAnd tail
  obtain ⟨pc,lx⟩ := splitAnd a
  obtain ⟨ns,cs⟩ := splitAnd b
  have forClause (c) (h : c ∈ d.requirements) :=
    closed_nullary_descent_sound439 (List.all_eq_true.mp cs c h)
  exact ⟨GeneralDeclarativeWitnessSignature349.checked_signature sg,identified ix,produced pc,
    output_only lx,scope_sound ns,GeneralDeclarativeWitnessModeDeclaration357.scoped_decl cov,
    fun c h => (forClause c h).1,fun c h => (forClause c h).2.1,
    fun c h => (forClause c h).2.2.1,fun c h => (forClause c h).2.2.2⟩

def checkHeader439 (env : Environment) : Bool :=
  (GeneralSourceMetadataRoles291.check env.source.roles &&
    GeneralDeclarativeWitnessModeCoverage357.check env) &&
  (decide (env.source.declarations.map Declaration.id).Nodup &&
    env.source.declarations.all (checksDeclaration439 env))

theorem checked_header439 {s : Current} (ok : checkHeader439 s.environment = true) :
    Checked (authoredRegistry s) ∧ Coverage s.environment := by
  obtain ⟨a,b⟩ := splitAnd ok
  obtain ⟨valid,declared⟩ := splitAnd a
  obtain ⟨keys,checks⟩ := splitAnd b
  have roles := (GeneralSourceMetadataRoles291.check_exact _).mp valid
  have coverage := (GeneralDeclarativeWitnessModeCoverage357.check_exact roles).mp declared
  exact ⟨⟨of_decide_eq_true keys,fun d h =>
    checks_declaration_sound439 (coverage.1 d h) (List.all_eq_true.mp checks d h)⟩,coverage⟩

end Yulang.GeneralDeclarativeI65.I72.MergedOutput439
