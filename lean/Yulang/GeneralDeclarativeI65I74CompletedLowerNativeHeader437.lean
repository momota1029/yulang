import Yulang.GeneralDeclarativeWitnessHeader349
import Yulang.GeneralDeclarativeWitnessModeDeclaration357

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.CompletedNativeHeader437

open GeneralDeclarations (Declaration Checked DeclarationChecked)
open GeneralDeclarativeWitnessDeclaredState357 (Current authoredRegistry)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarativeWitnessModeCoverage357 (Coverage DeclarationCovered)
open GeneralDeclarativeWitnessProblem349 (splitAnd)
open GeneralDeclarativeWitnessChecks349 (identified produced output_only scope_sound descent_parts)

def checkHeader (env : Environment) : Bool :=
  (GeneralSourceMetadataRoles291.check env.source.roles &&
    GeneralDeclarativeWitnessModeCoverage357.check env) &&
    GeneralDeclarativeWitnessHeader349.checkedRegistry env.source

theorem checkedDecl {s : Current} {d : Declaration}
    (cov : DeclarationCovered s.environment d)
    (ok : GeneralDeclarativeWitnessHeader349.checksDecl s.environment.source d = true) :
    DeclarationChecked (authoredRegistry s).constructors (authoredRegistry s).roles d := by
  obtain ⟨top,tail⟩ := splitAnd ok
  obtain ⟨sg,ix⟩ := splitAnd top
  obtain ⟨a,b⟩ := splitAnd tail
  obtain ⟨pc,lx⟩ := splitAnd a
  obtain ⟨ns,cs⟩ := splitAnd b
  have forClause (c) (h : c ∈ d.requirements) := descent_parts (List.all_eq_true.mp cs c h)
  exact ⟨GeneralDeclarativeWitnessSignature349.checked_signature sg,identified ix,produced pc,
    output_only lx,scope_sound ns,GeneralDeclarativeWitnessModeDeclaration357.scoped_decl cov,
    fun c h => (forClause c h).1,fun c h => (forClause c h).2.1,
    fun c h => (forClause c h).2.2.1,fun c h => (forClause c h).2.2.2⟩

theorem checkedHeader {s : Current} (ok : checkHeader s.environment = true) :
    Checked (authoredRegistry s) ∧ Coverage s.environment := by
  obtain ⟨a,b⟩ := splitAnd ok
  obtain ⟨valid,declared⟩ := splitAnd a
  obtain ⟨keys,checks⟩ := splitAnd b
  have roles := (GeneralSourceMetadataRoles291.check_exact _).mp valid
  have coverage := (GeneralDeclarativeWitnessModeCoverage357.check_exact roles).mp declared
  exact ⟨⟨of_decide_eq_true keys, fun d h =>
    checkedDecl (coverage.1 d h) (List.all_eq_true.mp checks d h)⟩,coverage⟩

end Yulang.GeneralDeclarativeI65.CompletedNativeHeader437
