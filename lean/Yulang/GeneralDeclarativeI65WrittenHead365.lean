import Yulang.GeneralDeclarativeI65OriginArity365
import Yulang.GeneralDeclarativeNormalizeScope322

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65
open GeneralDeclarativeWitnessConstructorModes357 (Environment Use)
open GeneralDeclarativeWitnessModeCoverage357 (Covers CoversList DeclarationCovered)
open GeneralDeclarativeNormalizeScope322 (normal_length)
open GeneralDeclarationPatterns (Pattern normalize normalizeArgs)
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeWhere319 (Capture)

theorem cover_at_actual_source_position (e : Environment) (ps : List Pattern) (p : Pattern)
    (seen : p ∈ ps) (all : CoversList e ps) : Covers e p := by
  induction ps with
  | nil => cases seen
  | cons head tail ih =>
    rcases List.mem_cons.mp seen with first | later
    · exact first ▸ all.1
    · exact ih later all.2

/-- A direct normalized nominal application reads its real key and
arity from the actual written declaration in the same environment.
The proof does not accept a naked mode vector asserted by a witness. -/
theorem actual_written_application_use {s : State} {arg : Capture} {decl : Declaration}
    {ctor : Nat} {ps : List Pattern} (w : ModeWindow s arg (.app ctor ps))
    (present : .app ctor ps ∈ decl.head)
    (cover : DeclarationCovered s.current.environment decl) :
    Nonempty (Use s.current.environment w.name w.arguments.length) := by
  have observation : Pattern.app ctor (normalizeArgs ps) = Pattern.app w.name w.arguments := by
    simpa only [normalize] using w.syntaxHead
  obtain ⟨same,length⟩ := Pattern.app.inj observation
  have original := cover_at_actual_source_position s.current.environment decl.head (.app ctor ps) present cover.1
  rw [← same,← length,normal_length]
  exact original.1

theorem actual_written_arity_reflects_both_origins {s : State} {arg : Capture} {decl : Declaration}
    {ctor : Nat} {ps : List Pattern} (w : ModeWindow s arg (.app ctor ps))
    (actual : decl ∈ (authoredRegistry s.current).declarations)
    (present : .app ctor ps ∈ decl.head)
    (cover : DeclarationCovered s.current.environment decl) :
    decl ∈ (authoredRegistry s.current).declarations ∧
      w.arguments.length = w.firstArgs.length ∧ w.arguments.length = w.lastArgs.length := by
  obtain ⟨use⟩ := actual_written_application_use w present cover
  exact ⟨actual,same_written_arity_at_both_origins w use⟩

end Yulang.GeneralDeclarativeI65
