import Yulang.CoreData
import Yulang.CaseCoverage
import Yulang.ScopedCasePatterns

/-! Structural transport of the existing independent pattern/coverage rules.
Mapping defaults does not change order, binders, guards or coverage domains. -/
namespace Yulang.Core.Patterns
open CasePatterns CaseValues

def map (f : D → E) : Pattern F D → Pattern F E
  | .wildcard => .wildcard
  | .bind a => .bind a
  | .literal a => .literal a
  | .intRange a b => .intRange a b
  | .pair a b => .pair (map f a) (map f b)
  | .recordEnd => .recordEnd
  | .field a b c => .field a (map f b) (map f c)
  | .defaultField a b c d => .defaultField a (f b) (map f c) (map f d)
  | .nil => .nil
  | .cons a b => .cons (map f a) (map f b)
  | .snoc a b => .snoc (map f a) (map f b)
  | .variant a b => .variant a (map f b)
  | .nominal a b c => .nominal a b (map f c)
  | .or a b => .or (map f a) (map f b)
  | .as a b => .as (map f a) b

@[simp] theorem names_map (f : D → E) (p : Pattern F D) : (map f p).names = p.names := by
  induction p <;> simp [map, Pattern.names, *]

@[simp] theorem map_comp (f : D → E) (g : E → R) (p : Pattern F D) :
    map g (map f p) = map (g ∘ f) p := by
  induction p <;> simp [map, *]

@[simp] theorem map_id (p : Pattern F D) : map id p = p := by
  induction p <;> simp [map, *]

theorem typing_names (h : CasePatterns.Typing predicate pattern input bindings) :
    bindings.map Prod.fst = pattern.names := by
  induction h <;> simp_all [Pattern.names, List.map_append]

theorem scoped_names (h : ScopedCasePatterns.Typing predicate types pattern input bindings) :
    bindings.map Prod.fst = pattern.names := by
  induction h <;> simp_all [Pattern.names, List.map_append]

theorem typing_map (f : D → E)
    (h : CasePatterns.Typing predicate pattern input bindings)
    (defaults : ∀ d t, predicate d t → mapped (f d) t) :
    CasePatterns.Typing mapped (map f pattern) input bindings := by
  induction h
  all_goals try simp only [map] at *
  all_goals first
    | apply CasePatterns.Typing.wildcard <;> first | assumption | apply defaults; assumption
    | apply CasePatterns.Typing.bind <;> first | assumption | apply defaults; assumption
    | apply CasePatterns.Typing.literal <;> first | assumption | apply defaults; assumption
    | apply CasePatterns.Typing.intRange <;> first | assumption | apply defaults; assumption
    | apply CasePatterns.Typing.pair <;> first | assumption | apply defaults; assumption
    | apply CasePatterns.Typing.recordEnd <;> first | assumption | apply defaults; assumption
    | apply CasePatterns.Typing.field <;> first | assumption | apply defaults; assumption
    | apply CasePatterns.Typing.defaultField <;> first | assumption | apply defaults; assumption
    | apply CasePatterns.Typing.nil <;> first | assumption | apply defaults; assumption
    | apply CasePatterns.Typing.cons <;> first | assumption | apply defaults; assumption
    | apply CasePatterns.Typing.snoc <;> first | assumption | apply defaults; assumption
    | apply CasePatterns.Typing.variant <;> first | assumption | apply defaults; assumption
    | apply CasePatterns.Typing.mergedVariant <;> first | assumption | apply defaults; assumption
    | apply CasePatterns.Typing.nominal <;> first | assumption | apply defaults; assumption
    | apply CasePatterns.Typing.mergedNominal <;> first | assumption | apply defaults; assumption
    | apply CasePatterns.Typing.or <;> first | assumption | apply defaults; assumption
    | apply CasePatterns.Typing.as <;> first | assumption | apply defaults; assumption
    | apply CasePatterns.Typing.narrow <;> first | assumption | apply defaults; assumption

theorem typing_reflect (f : D → E)
    (h : CasePatterns.Typing mapped pattern input bindings)
    (defaults : ∀ d t, mapped (f d) t → predicate d t) :
    ∀ source, map f source = pattern → CasePatterns.Typing predicate source input bindings := by
  induction h
  all_goals intro source eq
  case narrow below _ ih => exact .narrow below (ih source eq)
  all_goals cases source <;> simp only [map] at eq
  all_goals cases eq
  all_goals first
    | apply CasePatterns.Typing.wildcard
    | apply CasePatterns.Typing.bind
    | apply CasePatterns.Typing.literal
    | apply CasePatterns.Typing.intRange
    | apply CasePatterns.Typing.pair
    | apply CasePatterns.Typing.recordEnd
    | apply CasePatterns.Typing.field
    | apply CasePatterns.Typing.defaultField
    | apply CasePatterns.Typing.nil
    | apply CasePatterns.Typing.cons
    | apply CasePatterns.Typing.snoc
    | apply CasePatterns.Typing.variant
    | apply CasePatterns.Typing.mergedVariant
    | apply CasePatterns.Typing.nominal
    | apply CasePatterns.Typing.mergedNominal
    | apply CasePatterns.Typing.or
    | apply CasePatterns.Typing.as
  all_goals solve_by_elim

theorem checkOne_map (f : D → E) (domains : E → CaseCoverage.Domain)
    (pattern : Pattern F D) (input : CaseCoverage.Domain) :
    CaseCoverage.checkOne domains (map f pattern) input =
      CaseCoverage.checkOne (domains ∘ f) pattern input := by
  induction pattern generalizing input <;>
    simp [map, CaseCoverage.checkOne, Function.comp_def, *]

def arm (f : D → E) (a : CaseCoverage.Arm F D) : CaseCoverage.Arm F E :=
  ⟨map f a.pattern, a.guarded⟩

theorem covered_map (f : D → E) (domains : E → CaseCoverage.Domain)
    (arms : List (CaseCoverage.Arm F D)) (input : CaseCoverage.Domain) :
    CaseCoverage.Covered domains (arms.map (arm f)) input ↔
      CaseCoverage.Covered (domains ∘ f) arms input := by
  rw [← CaseCoverage.check_exact, ← CaseCoverage.check_exact]
  simp [CaseCoverage.check, List.any_map, arm, checkOne_map]

theorem variantsCovered_map (f : D → E) (domains : E → CaseCoverage.Domain)
    (arms : List (CaseCoverage.Arm F D)) (row : CaseCoverage.VariantRow) :
    CaseCoverage.VariantsCovered domains (arms.map (arm f)) row ↔
      CaseCoverage.VariantsCovered (domains ∘ f) arms row := by
  rw [← CaseCoverage.checkVariants_exact, ← CaseCoverage.checkVariants_exact]
  simp [CaseCoverage.checkVariants, CaseCoverage.check, List.any_map, arm, checkOne_map]

@[simp] theorem patternDefaults_map (f : D → E) (pattern : Pattern F D) :
    CaseCoverage.patternDefaults (map f pattern) =
      (CaseCoverage.patternDefaults pattern).map f := by
  induction pattern <;> simp [map, CaseCoverage.patternDefaults, List.map_append, *]

@[simp] theorem armDefaults_map (f : D → E) (arms : List (CaseCoverage.Arm F D)) :
    CaseCoverage.armDefaults (arms.map (arm f)) = (CaseCoverage.armDefaults arms).map f := by
  simp [CaseCoverage.armDefaults, arm, List.flatMap_map, List.map_flatMap]

end Yulang.Core.Patterns
