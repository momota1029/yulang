import Yulang.CorePatterns
import Yulang.CaseTree

/-! Ordered cases on shared syntax, with the historical unscoped-default
coverage rules. Scoped defaults have their separate pattern bridge. -/
namespace Yulang.Core.Case
open CaseValues
abbrev Term := Data.Term
abbrev Arm (F : Type) := CasePatterns.Pattern F (Term F) × Option (Term F) × Term F

mutual
  def embed (scope : List Nat) : CaseTree.Expr F → Term F
    | .leaf code => .leaf (Data.embed scope code)
    | .caseE selected arms => .caseE (embed scope selected) (embedArms scope arms)
    | .pair a b => .pair (embed scope a) (embed scope b)
    | .letE name a b => .letE (some name) (embed scope a) (embed (name :: scope) b)

  def embedArms (scope : List Nat) : CaseTree.Arms F → List (Arm F)
    | .nil => []
    | .cons p g body rest =>
        (Patterns.map (Data.embed scope) p, g.map (Data.embed (p.names ++ scope)),
          embed (p.names ++ scope) body) :: embedArms scope rest
end

def coverage (arms : List (Arm F)) : List (CaseCoverage.Arm F (Term F)) :=
  arms.map fun a => ⟨a.1, a.2.1.isSome⟩

@[simp] theorem coverage_embed (scope : List Nat) (arms : CaseTree.Arms F) :
    coverage (embedArms scope arms) =
      arms.coverage.map (Patterns.arm (Data.embed scope)) := by
  cases arms with
  | nil => rfl
  | cons p g body rest =>
    simp only [embedArms, coverage, List.map_cons, CaseTree.Arms.coverage, Patterns.arm]
    rw [show (g.map (Data.embed (p.names ++ scope))).isSome = g.isSome by cases g <;> rfl]
    exact congrArg (List.cons _) (coverage_embed scope rest)

mutual
  inductive Typing : List (Nat × Ty F) → Term F → Ty F → Prop where
    | leaf : Data.Typing (types.map Prod.snd) code target → Typing types (.leaf code) target
    | caseE {domain : CaseCoverage.Domain} {defaultDomains : Term F → CaseCoverage.Domain} :
        Typing types scrutinee (domain.denote F) → ArmsTyping types arms (domain.denote F) target →
        CaseCoverage.Covered defaultDomains (coverage arms) domain →
        (∀ code ∈ CaseCoverage.armDefaults (coverage arms),
          Data.Typing (types.map Prod.snd) code ((defaultDomains code).denote F)) →
        Typing types (.caseE scrutinee arms) target
    | caseVariants {row : CaseCoverage.VariantRow} {defaultDomains : Term F → CaseCoverage.Domain} :
        Typing types scrutinee (Ty.variants (CaseCoverage.semanticRow row)) →
        ArmsTyping types arms (Ty.variants (CaseCoverage.semanticRow row)) target →
        CaseCoverage.VariantsCovered defaultDomains (coverage arms) row →
        (∀ code ∈ CaseCoverage.armDefaults (coverage arms),
          Data.Typing (types.map Prod.snd) code ((defaultDomains code).denote F)) →
        Typing types (.caseE scrutinee arms) target
    | pair : Typing types first left → Typing types last right →
        Typing types (.pair first last) (Ty.pair left right)
    | letE : Typing types definition input → Typing ((name, input) :: types) body output →
        Typing types (.letE (some name) definition body) output
    | widen : Typing types expression input → Ty.Le input output → Typing types expression output

  inductive ArmsTyping : List (Nat × Ty F) → List (Arm F) → Ty F → Ty F → Prop where
    | nil : ArmsTyping types [] input target
    | cons {guard : Option (Term F)} :
        CasePatterns.Typing (fun code type => Data.Typing (types.map Prod.snd) code type)
          pattern input bindings →
        (∀ code, guard = some code →
          Data.Typing ((bindings ++ types).map Prod.snd) code (Ty.literal .bool)) →
        Typing (bindings ++ types) body target → ArmsTyping types rest input target →
        ArmsTyping types ((pattern, guard, body) :: rest) input target
end

def model (F : Type) : TypingModel ⟨Empty, Empty, Empty, F, Empty⟩ :=
  ⟨List (Nat × Ty F), Ty F, Typing⟩

private theorem defaults_preserved
    {types : List (Nat × Ty F)} {arms : CaseTree.Arms F}
    {domains : CaseDataTerms.Expr F → CaseCoverage.Domain}
    (defaults : ∀ code ∈ CaseCoverage.armDefaults arms.coverage,
      CaseDataTerms.Typing types code ((domains code).denote F)) :
    ∀ code ∈ CaseCoverage.armDefaults (coverage (embedArms (types.map Prod.fst) arms)),
      Data.Typing (types.map Prod.snd) code
        ((domains (Data.decode (types.map Prod.fst) code)).denote F) := by
  intro code member
  rw [coverage_embed, Patterns.armDefaults_map] at member
  obtain ⟨source, sourceMember, sourceEq⟩ := List.mem_map.mp member
  subst code
  simpa using Data.preserved (defaults source sourceMember)

theorem preserved (h : CaseTree.Typing types expression target) :
    Typing types (embed (types.map Prod.fst) expression) target := by
  induction h using CaseTree.Typing.rec
    (motive_2 := fun types arms input target _ =>
      ArmsTyping types (embedArms (types.map Prod.fst) arms) input target)
  case leaf h => exact .leaf (Data.preserved h)
  case caseE selected armsTyped covered defaults ihs iha =>
    rename_i types scrutinee arms target domain domains
    apply Typing.caseE (defaultDomains := domains ∘ Data.decode (types.map Prod.fst)) ihs iha
    · rw [coverage_embed, Patterns.covered_map]
      simpa only [Function.comp_def, Data.decode_embed] using covered
    · exact defaults_preserved defaults
  case caseVariants selected armsTyped covered defaults ihs iha =>
    rename_i types scrutinee arms target row domains
    apply Typing.caseVariants (defaultDomains := domains ∘ Data.decode (types.map Prod.fst)) ihs iha
    · rw [coverage_embed, Patterns.variantsCovered_map]
      simpa only [Function.comp_def, Data.decode_embed] using covered
    · exact defaults_preserved defaults
  case pair a b iha ihb => exact .pair iha ihb
  case letE a b iha ihb => exact .letE iha ihb
  case widen h below ih => exact .widen ih below
  case nil => exact .nil
  case cons pattern guards bodyTyped restTyped ihb ihr =>
    rename_i types p input bindings body target rest guard
    have names := Patterns.typing_names pattern
    apply ArmsTyping.cons
    · exact Patterns.typing_map _ pattern (fun _ _ h => Data.preserved h)
    · intro code found
      cases eq : guard with
      | none => simp [eq] at found
      | some original =>
        simp only [eq, Option.map_some, Option.some.injEq] at found
        subst code
        simpa [List.map_append, names] using Data.preserved (guards original eq)
    · simpa [List.map_append, names] using ihb
    · exact ihr


private theorem defaults_reflected
    {types : List (Nat × Ty F)} {arms : CaseTree.Arms F}
    {domains : Term F → CaseCoverage.Domain}
    (defaults : ∀ code ∈ CaseCoverage.armDefaults (coverage (embedArms (types.map Prod.fst) arms)),
      Data.Typing (types.map Prod.snd) code ((domains code).denote F)) :
    ∀ code ∈ CaseCoverage.armDefaults arms.coverage,
      CaseDataTerms.Typing types code ((domains (Data.embed (types.map Prod.fst) code)).denote F) := by
  intro code member
  apply Data.reflected (defaults _ ?_) types code rfl rfl
  rw [coverage_embed, Patterns.armDefaults_map]
  exact List.mem_map.mpr ⟨code, member, rfl⟩

theorem reflected (h : Typing types expression target) :
    ∀ source, embed (types.map Prod.fst) source = expression →
      CaseTree.Typing types source target := by
  induction h using Typing.rec
    (motive_2 := fun types arms input target _ =>
      ∀ source, embedArms (types.map Prod.fst) source = arms →
        CaseTree.ArmsTyping types source input target)
  case nil source syntaxEq =>
    cases source <;> simp only [embedArms] at syntaxEq
    · exact .nil
    · cases syntaxEq
  case cons pattern guards body rest ihb ihr source syntaxEq =>
    cases source with
    | nil => cases syntaxEq
    | cons p g b tail =>
      simp only [embedArms] at syntaxEq
      cases syntaxEq
      rename_i input bindings types target
      have names : bindings.map Prod.fst = p.names := by
        simpa using Patterns.typing_names pattern
      apply CaseTree.ArmsTyping.cons
      · exact Patterns.typing_reflect _ pattern
          (fun d t h => Data.reflected h types d rfl rfl) p rfl
      · intro code found
        apply (Data.conservative (bindings ++ types) code (Ty.literal .bool)).mpr
        simpa only [Core.Typing, Data.model, List.map_append, names] using guards _ (by simp [found])
      · apply ihb b
        simp [List.map_append, names]
      · exact ihr tail rfl
  all_goals intro source syntaxEq
  case widen h below ih => exact .widen (ih source syntaxEq) below
  all_goals cases source <;> simp only [embed] at syntaxEq
  all_goals cases syntaxEq
  case leaf.leaf.refl =>
    apply CaseTree.Typing.leaf
    exact Data.reflected ‹_› _ _ rfl rfl
  case caseE.caseE.refl =>
    rename_i types target domain domains scrutinee arms selected ihs armTyped covered defaults iha
    apply CaseTree.Typing.caseE (defaultDomains := domains ∘ Data.embed (types.map Prod.fst))
      (ihs scrutinee rfl) (iha arms rfl)
    · exact (Patterns.covered_map _ _ _ _).mp (by simpa only [coverage_embed] using covered)
    · exact defaults_reflected defaults
  case caseVariants.caseE.refl =>
    rename_i types target row domains scrutinee arms selected ihs armTyped covered defaults iha
    apply CaseTree.Typing.caseVariants (defaultDomains := domains ∘ Data.embed (types.map Prod.fst))
      (ihs scrutinee rfl) (iha arms rfl)
    · exact (Patterns.variantsCovered_map _ _ _ _).mp (by simpa only [coverage_embed] using covered)
    · exact defaults_reflected defaults
  case pair.pair.refl => apply CaseTree.Typing.pair <;> solve_by_elim
  case letE.letE.refl => apply CaseTree.Typing.letE <;> solve_by_elim


theorem conservative (types : List (Nat × Ty F))
    (expression : CaseTree.Expr F) (target : Ty F) :
    CaseTree.Typing types expression target ↔
      Core.Typing (model F) types (embed (types.map Prod.fst) expression) target := by
  constructor
  · exact preserved
  · intro h; exact reflected h expression rfl

end Yulang.Core.Case
