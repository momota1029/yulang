import Yulang.GeneralDeclarativeWitnessClassifyVariance357
import Yulang.GeneralDeclarativeWitnessCovariantDescent353

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessModeDeclaration357
open GeneralDeclarativeWitnessClassifyVariance357 (SourceChecked DeclarationReady)
open GeneralDeclarativeWitnessDeclaredState357 (Current authoredRegistry)
open GeneralDeclarativeWitnessModeCoverage357 (Covers CoversList DeclarationCovered Coverage)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralSourceMetadataBundle291 (registry)
open GeneralDeclarationPatterns (Pattern WellScoped ArgsWellScoped)
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWitnessProblem349 (splitAnd)
open GeneralDeclarativeWitnessChecks349 (identified produced output_only scope_sound)
open GeneralDeclarativeWitnessSignature349 (checked_signature)
open GeneralDeclarativeWitnessCovariantDescent353 (legal descent_sound)

mutual
theorem pattern_scope (e : Environment) :
    ∀ p : Pattern,Covers e p → WellScoped (registry e.source).constructors p
  | .var _, _ => trivial
  | .app _ args, h => by
    obtain ⟨hit⟩ := h.1
    exact ⟨⟨hit.declared,hit.actual,hit.exactArity⟩,patterns_scope e args h.2⟩
  | .record _ a b, h => ⟨pattern_scope e a h.1,pattern_scope e b h.2⟩
  | .variant _ payload, h => pattern_scope e payload h
  | .join a b, h => ⟨pattern_scope e a h.1,pattern_scope e b h.2⟩

theorem patterns_scope (e : Environment) :
    ∀ ps : List Pattern,CoversList e ps → ArgsWellScoped (registry e.source).constructors ps
  | [], _ => trivial
  | a::b, h => ⟨pattern_scope e a h.1,patterns_scope e b h.2⟩
end

theorem scoped_decl {s : Current} {d : Declaration} (h : DeclarationCovered s.environment d) :
    d.ConstructorScoped (authoredRegistry s).constructors :=
  ⟨patterns_scope _ _ h.1,
   fun clause shows => ⟨patterns_scope _ _ (h.2.1 clause shows).1,
      fun o present => pattern_scope _ _ ((h.2.1 clause shows).2 o present)⟩,
   fun o present => pattern_scope _ _ (h.2.2 o present)⟩

theorem declaration_ready {s : Current} {d : Declaration} (covered : DeclarationCovered s.environment d)
    (accepted : legal s.environment.source d = true) : DeclarationReady (authoredRegistry s) d := by
  obtain ⟨top,tail⟩ := splitAnd accepted
  obtain ⟨sig,ids⟩ := splitAnd top
  obtain ⟨left,right⟩ := splitAnd tail
  obtain ⟨binds,lexical⟩ := splitAnd left
  obtain ⟨scope,descent⟩ := splitAnd right
  exact ⟨checked_signature sig,identified ids,produced binds,output_only lexical,scope_sound scope,
    scoped_decl covered,fun c h => descent_sound (List.all_eq_true.mp descent c h)⟩

def ready (s : Current) : Bool :=
  decide ((authoredRegistry s).declarations.map Declaration.id).Nodup &&
    (authoredRegistry s).declarations.all (legal s.environment.source)

theorem source_ready {s : Current} (covered : Coverage s.environment) (checked : ready s = true) :
    SourceChecked s :=
  ⟨of_decide_eq_true (splitAnd checked).1,
   fun decl inBook => declaration_ready (covered.1 decl inBook)
     (List.all_eq_true.mp (splitAnd checked).2 decl inBook)⟩

end Yulang.GeneralDeclarativeWitnessModeDeclaration357
