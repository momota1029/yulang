import Yulang.GeneralDeclarativeI65I74AuthoredNormalScope461
import Yulang.GeneralDeclarativeI65I74ActualRawNominalMode461

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.EligibleFieldStart461
open WrittenPattern460
open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarativeWitnessModeCoverage357 (Covers CoversList)
open GeneralDeclarativeWitnessConstructorModes357 (Use check_has_no_fallback)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralNominalCenteredHeadMatExpressions (Expr application)
open AuthoredInspectQuery456 (AuthoredQuery AuthoredQueries AuthoredApplication legacyApply)
open GeneralCandidateInspection (Primitive)
open RecordTraversal455.MixedQA (ChildAt)
open InlineStructuralPolicy458 (policy)

private theorem legacy_nominal_uses_existing_declared_name
    {s : CoreState} {original actual : Nat} {args out : List Expr}
    (covered : Use s.current.environment original args.length)
    (compiled : legacyApply s original args = some (.nominal actual out)) :
    actual = original := by
  have found : (authoredRegistry s.current).constructors original = some covered.declared :=
    (check_has_no_fallback covered).1
  have arity := covered.exactArity
  cases prim : (interpretation s.current.environment.source.snapshot).primitives original with
  | some op =>
    by_cases params : covered.declared.parameters = op.parameters <;>
      simp [legacyApply,application,found,Option.bind,arity,prim,params] at compiled
  | none =>
    by_cases params : (interpretation s.current.environment.source.snapshot).invariantNominal original = true ∧
        covered.declared.parameters = List.replicate args.length .type
    · have eq : Expr.nominal covered.declared.name args = .nominal actual out := by
        simpa [legacyApply,application,found,Option.bind,arity,prim,params] using compiled
      exact (Expr.nominal.inj eq).1.symm.trans covered.declaredName
    · simp [legacyApply,application,found,Option.bind,arity,prim,params] at compiled

private theorem compiled_application_vector_has_source_arity {s : CoreState} {raw code}
    (all : AuthoredQueries s raw code) : raw.length = code.length := by
  cases all with
  | nil => rfl
  | cons _ rest => simp [compiled_application_vector_has_source_arity rest]

theorem earlier_nominal_compiled_and_raw_modes_share_original_term
    {s : CoreState} {p : Pattern} {key xs}
    (coverage : Covers s.current.environment p)
    (authored : AuthoredQuery s p (.nominal key xs))
    (mode : InlineNominalPoint458.HasMode s key) :
    ∃ child expr, p = .app key [child] ∧ xs = [expr] ∧
      queryKeys s key = .covariantPoint ∧ AuthoredQuery s child expr := by
  cases p
  case var | record | variant | join => cases authored
  case app original inputs =>
    cases authored with
    | app vector actual =>
      cases actual with
      | legacy run =>
        obtain ⟨covered⟩ := coverage.1
        have count := compiled_application_vector_has_source_arity vector
        have src := legacy_nominal_uses_existing_declared_name (count ▸ covered) run
        subst original
        obtain ⟨use,kind,_⟩ := mode
        rw [declared_mode_cannot_choose_legacy_application use kind] at run
        cases run
      | declaredPoint old use name table =>
        cases vector with
        | cons child rest =>
          cases rest
          exact ⟨_,_,rfl,rfl,(exact_declared_unary_application_at_original_key use name table (.variable 0)).1,child⟩

theorem actual_compiled_primitive_has_exact_primitive_arity
    {s : CoreState} {p : Pattern} {tag args}
    (authored : AuthoredQuery s p (.primitive tag args)) :
    args.length = tag.parameters.length := by
  cases p
  case var | record | variant | join => cases authored
  case app key written =>
    cases authored with
    | app vector compiled =>
      cases compiled with
      | legacy run =>
        obtain ⟨_,_,arity,_,layout,rfl⟩ := primitive_application_exact_signature.mp run
        exact arity.symm.trans (congrArg List.length layout)

end Yulang.GeneralDeclarativeI65.I72.EligibleFieldStart461
