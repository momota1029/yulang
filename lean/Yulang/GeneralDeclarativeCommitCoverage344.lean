import Yulang.GeneralDeclarativeNormalizedPort344
import Yulang.GeneralDeclarativeNormalizeCovered322

set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeCommitCoverage344
open GeneralDeclarationPatterns (Pattern Constructors normalize)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCenteredHeadMatExpressions (Expr translate translateMany application translateMany_complete)
open GeneralNominalCenteredHeadWFSource (ConstructorUse PatternCovered PatternsCovered)
open GeneralDeclarativeNormalizeCovered322 (normalize_args_covered)
open GeneralDeclarativeClauseBatch327 (prepare all_read)
open GeneralNominalCenters (Plan)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarations (Clause)
open GeneralWhereVersionSemantics317 (Holds)
open GeneralDeclarativeNormalizedPort344 (genuine_code)
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeWhere319 (Capture)

variable {c : Constructors} {i : Interpretation}

theorem application_used (printed : application c i key args = some e) :
    ConstructorUse c i key args.length := by
  cases decl : c key with
  | none => simp [application,decl] at printed
  | some d =>
    by_cases arity : d.parameters.length = args.length
    · cases prim : i.primitives key with
      | some p =>
        by_cases correct : d.parameters = p.parameters
        · exact ⟨d,decl,arity,.inl ⟨p,prim,correct⟩⟩
        · simp [application,decl,arity,prim,correct] at printed
      | none =>
        by_cases correct : i.invariantNominal key = true ∧ d.parameters = List.replicate args.length .type
        · exact ⟨d,decl,arity,.inr correct⟩
        · simp [application,decl,arity,prim,correct] at printed
    · simp [application,decl,arity] at printed

mutual
theorem used (p : Pattern) (printed : translate c i p = some e) : PatternCovered c i p := by
  cases p with
  | var _ => exact trivial
  | app key ps =>
    cases enc : translateMany c i ps with
    | none => simp [translate,enc] at printed
    | some qs =>
      have app : application c i key qs = some e := by simpa [translate,enc] using printed
      obtain ⟨cover,len⟩ := many ps enc
      exact ⟨len ▸ application_used app,cover⟩
  | record label a b =>
    cases lhs : translate c i a <;> cases rhs : translate c i b <;> simp [translate,lhs,rhs] at printed
    exact ⟨used a lhs,used b rhs⟩
  | variant label a =>
    cases got : translate c i a <;> simp [translate,got] at printed
    exact used a got
  | join a b =>
    cases lhs : translate c i a <;> cases rhs : translate c i b <;> simp [translate,lhs,rhs] at printed
    exact ⟨used a lhs,used b rhs⟩
termination_by sizeOf p

theorem many (ps : List Pattern) (printed : translateMany c i ps = some es) :
    PatternsCovered c i ps ∧ es.length = ps.length := by
  cases ps with
  | nil =>
    cases Option.some.inj printed
    exact ⟨trivial,rfl⟩
  | cons a b =>
    cases head : translate c i a <;> cases tail : translateMany c i b <;> simp [translateMany,head,tail] at printed
    cases printed
    obtain ⟨covered,len⟩ := many b tail
    exact ⟨⟨used a head,covered⟩,by simp [len]⟩
termination_by sizeOf ps
end

theorem cover_list {ps : List Pattern} (point : ∀ q ∈ ps, PatternCovered c i q) : PatternsCovered c i ps := by
  induction ps with
  | nil => exact trivial
  | cons p ps ih =>
    exact ⟨point p List.mem_cons_self,ih (fun q here => point q (List.mem_cons_of_mem _ here))⟩

theorem cover_accepted (p : Plan rs) (cl : Clause) (inside : cl ∈ p.packet.declaration.requirements)
    (sig : cl.Signature rs) (m : Assignment) (valid : Holds p m) :
    PatternsCovered p.packet.registry.constructors p.packet.context.interpretation cl.arguments := by
  apply cover_list
  intro q read
  obtain ⟨j,h,exactly⟩ := List.mem_iff_getElem.mp read
  let idx : Fin (rs cl.role).arity := ⟨j,by rw [← sig.1]; exact h⟩
  obtain ⟨e,compiled⟩ := genuine_code p cl inside sig idx m valid
  change translate p.packet.registry.constructors p.packet.context.interpretation cl.arguments[j] = some e at compiled
  rw [exactly] at compiled
  exact used q compiled

/-- A complete genuine versioned packet supplies coverage of all
its actual where inputs, so the ordinary normalized input pass
exists without a separate blanket constructor-coverage hypothesis.
This does not assert output/default coverage of other declarations. -/
theorem batch_available (p : Plan rs) (m : Assignment) (typed : Holds p m)
    (s : State) (protect : List Nat) (cap : Nat → Capture) :
    ∃ t ports, prepare p.packet.registry.constructors p.packet.context.interpretation protect cap s
      p.packet.declaration.requirements = some (t,ports) := by
  apply all_read
  intro cl found
  have exactCoverage := cover_accepted p cl found (p.packet.checked.signature.2.2.2 cl found) m typed
  obtain ⟨codes,ran,_⟩ := translateMany_complete (normalize_args_covered exactCoverage)
  exact ⟨codes,by simpa only [GeneralNominalChildAssembly.normalize_map] using ran⟩

end Yulang.GeneralDeclarativeCommitCoverage344
