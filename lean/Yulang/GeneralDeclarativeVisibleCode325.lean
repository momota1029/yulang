import Yulang.GeneralNominalCenteredHeadMatExpressions
import Yulang.GeneralDeclarativeNFNode324

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeVisibleCode325
open GeneralNominalCenteredHeadWFSource (ConstructorUse PatternCovered PatternsCovered)
open GeneralNominalCenteredHeadMatExpressions (Expr application translate translateMany translate_complete)
open GeneralDictionaryAssociatedProvenance (Supplies)
open GeneralDeclarativeOutputs320 (bodyPattern)
open GeneralDeclarativeNFNode324 (BodyCoverage)
open GeneralDeclarationPatterns (normalize)

theorem application_was_covered (built : application c interp key args = some exp) :
    ConstructorUse c interp key args.length := by
  unfold application at built
  cases there : c key with
  | none => simp [there] at built
  | some ctor =>
    by_cases arity : ctor.parameters.length = args.length
    · cases p : interp.primitives key with
      | none =>
        by_cases nominal : interp.invariantNominal key = true ∧
            ctor.parameters = List.replicate args.length .type
        · exact ⟨ctor,there,arity,.inr nominal⟩
        · simp [there,arity,p,nominal] at built
      | some tag =>
        by_cases sizes : ctor.parameters = tag.parameters
        · exact ⟨ctor,there,arity,.inl ⟨tag,p,sizes⟩⟩
        · simp [there,arity,p,sizes] at built
    · simp [there,arity] at built

mutual
theorem code_was_covered (built : translate c interp p = some exp) :
    PatternCovered c interp p := by
  cases p with
  | var => trivial
  | app n args =>
    cases children : translateMany c interp args with
    | none => simp [translate,children] at built
    | some xs =>
      have app : application c interp n xs = some exp := by simpa [translate,children] using built
      have ⟨coverage,sizes⟩ := codes_were_covered children
      exact ⟨sizes ▸ application_was_covered app,coverage⟩
  | record l a b =>
    cases x : translate c interp a with
    | none => simp [translate,x] at built
    | some one =>
      cases y : translate c interp b with
      | none => simp [translate,x,y] at built
      | some last => exact ⟨code_was_covered x,code_was_covered y⟩
  | variant l a =>
    cases x : translate c interp a with
    | none => simp [translate,x] at built
    | some one => exact code_was_covered (p := a) x
  | join a b =>
    cases x : translate c interp a with
    | none => simp [translate,x] at built
    | some one =>
      cases y : translate c interp b with
      | none => simp [translate,x,y] at built
      | some last => exact ⟨code_was_covered x,code_was_covered y⟩
termination_by sizeOf p

theorem codes_were_covered (built : translateMany c interp ps = some xs) :
    PatternsCovered c interp ps ∧ xs.length = ps.length := by
  cases ps with
  | nil =>
    cases Option.some.inj built
    exact ⟨trivial,rfl⟩
  | cons a rest =>
    cases left : translate c interp a with
    | none => simp [translateMany,left] at built
    | some first =>
      cases right : translateMany c interp rest with
      | none => simp [translateMany,left,right] at built
      | some tail =>
        have actual : first :: tail = xs := by simpa [translateMany,left,right] using built
        subst xs
        have h := codes_were_covered right
        exact ⟨⟨code_was_covered left,h.1⟩,congrArg Nat.succ h.2⟩
termination_by sizeOf ps
end

theorem code_iff :
    (∃ exp, translate c interp p = some exp) ↔ PatternCovered c interp p :=
  ⟨fun ⟨_,proof⟩ => code_was_covered proof,translate_complete⟩

/-- Exactly the supplied parsed bodies for the actual requested names
need successful normalized translation. No assumption about the raw RHS,
other associated outputs, or unrelated catalogue entries is used. -/
theorem body_coverage_exact :
    BodyCoverage r interp d impl ↔
      ∀ out ∈ d.outputs, ∀ body, Supplies r.roles impl out.name body →
        ∃ exp, translate r.constructors interp (normalize (bodyPattern body)) = some exp := by
  exact ⟨fun cover out h body taken => code_iff.mpr (cover out h body taken),
    fun all out h body taken => code_iff.mp (all out h body taken)⟩

end Yulang.GeneralDeclarativeVisibleCode325
