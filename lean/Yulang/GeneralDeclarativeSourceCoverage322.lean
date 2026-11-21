import Yulang.GeneralDeclarativeNormalizeCovered322
import Yulang.GeneralDeclarativeEmissionClause322
import Yulang.GeneralDeclarativeSourceCodes321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeSourceCoverage322
open GeneralNominalCenteredHeadWFSource (PatternCovered PatternsCovered DeclarationCovered)
open GeneralDeclarativeNormalizeCovered322 (normalize_covered normalize_args_covered)
open GeneralNominalCenteredHeadMatExpressions (Expr translate translateMany translate_complete translateMany_complete)
open GeneralDeclarativeSourceCodes321 (outputCodes clauseCode clauseCodes args_exact)
open GeneralDeclarativeSourceEmission322 (Names useOutput)
open GeneralDeclarativeEmissionClause322 (Ready)
open GeneralDeclarativeEmissionOperands322 (Compound)
open GeneralDeclarativeEmissionOutputs322 (Direct)
open GeneralDeclarativeExistingClause322 (Refers)
open GeneralDeclarativeEqualities322 (Derives)
open GeneralDeclarativeSubstitution320 (logical)
open GeneralDeclarativeHead320 (State)
open GeneralDeclarations (Declaration Clause)
open GeneralDeclarationPatterns (normalize normalizeArgs)
open CommonRoleOutermostResolver (All₂)

theorem all_outputs {source : List GeneralDeclarations.Equation}
    (scope : ∀ eqn ∈ source, PatternCovered c interp eqn.rhs) :
    ∃ tables, outputCodes c interp source = some tables := by
  induction source with
  | nil => exact ⟨[],rfl⟩
  | cons h t ih =>
    obtain ⟨one,first⟩ := translate_complete (scope h List.mem_cons_self)
    obtain ⟨rest,more⟩ := ih (fun e member => scope e (List.mem_cons_of_mem _ member))
    exact ⟨(h.name,one)::rest,by simp [outputCodes,first,more]⟩

theorem one_clause {clause : Clause}
    (arguments : PatternsCovered r.constructors interp clause.arguments)
    (results : ∀ eqn ∈ clause.outputs, PatternCovered r.constructors interp eqn.rhs) :
    ∃ table, clauseCode r interp clause = some table := by
  obtain ⟨args,readArgs,_⟩ := translateMany_complete (normalize_args_covered arguments)
  obtain ⟨outputs,readOut⟩ := all_outputs results
  exact ⟨⟨args,outputs⟩,by simp [clauseCode,readArgs,readOut]⟩

theorem compile_requirements {decl : Declaration}
    (source : DeclarationCovered r.constructors interp decl) :
    ∃ tables, clauseCodes r interp decl.requirements = some tables := by
  have build (requirements : List Clause)
    (every : ∀ k ∈ requirements, PatternsCovered r.constructors interp k.arguments ∧
      ∀ eqn ∈ k.outputs, PatternCovered r.constructors interp eqn.rhs) :
      ∃ tables, clauseCodes r interp requirements = some tables := by
    induction requirements with
    | nil => exact ⟨[],rfl⟩
    | cons h t ih =>
      obtain ⟨first,readFirst⟩ := one_clause (every h List.mem_cons_self).1 (every h List.mem_cons_self).2
      obtain ⟨tail,readTail⟩ := ih (fun k used => every k (List.mem_cons_of_mem _ used))
      exact ⟨first::tail,by simp [clauseCodes,readFirst,readTail]⟩
  exact build decl.requirements source.2.1

/-- After source metadata coverage the compiler tables need not be assumed.
Only ordinary derivations for genuine compound operands and non-binder
targets remain. Direct binder placements are handled by the emitter. -/
theorem ready_from_forms {s : State} {names : Names} {clause : Clause}
    (args : PatternsCovered r.constructors interp clause.arguments)
    (outs : ∀ eqn ∈ clause.outputs, PatternCovered r.constructors interp eqn.rhs)
    (compound : ∀ (i : Nat) pat code, clause.arguments[i]? = some pat →
      translate r.constructors interp (normalize pat) = some code →
      Compound pat → Refers s names.input code (fallback i))
    (named : ∀ eqn ∈ clause.outputs, ∀ code,
      translate r.constructors interp (normalize eqn.rhs) = some code → ¬Direct decl eqn →
      Derives s (.variable (useOutput decl names targets eqn).target) (logical names.input .actual code)) :
    Ready s r interp decl clause names fallback targets := by
  obtain ⟨codes,translation,_⟩ := translateMany_complete (normalize_args_covered args)
  have terms := args_exact translation
  have at_pos {ps : List GeneralDeclarationPatterns.Pattern} {es : List Expr}
      (zipped : All₂ (fun p code => translate r.constructors interp (normalize p) = some code) ps es)
      (i : Nat) {p code} (pos : ps[i]? = some p) (seen : es[i]? = some code) :
      translate r.constructors interp (normalize p) = some code := by
    induction zipped generalizing i with
    | nil => cases i <;> cases pos
    | @cons first exp before after hd tl ih =>
      cases i with
      | zero =>
        have h : first = p := Option.some.inj pos
        have c : exp = code := Option.some.inj seen
        subst p
        subst code
        exact hd
      | succ j => exact ih j pos seen
  refine ⟨⟨codes,terms,fun i p code there read => compound i p code there (at_pos terms i there read)⟩,?_⟩
  intro eqn present
  have actual := outs eqn present
  obtain ⟨raw,hr⟩ := translate_complete actual
  obtain ⟨norm,hn⟩ := translate_complete (normalize_covered actual)
  exact ⟨raw,norm,hr,hn,named eqn present norm hn⟩

end Yulang.GeneralDeclarativeSourceCoverage322
