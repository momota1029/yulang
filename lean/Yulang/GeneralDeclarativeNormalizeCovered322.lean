import Yulang.GeneralDeclarativeNormalizeScope322
import Yulang.GeneralNominalCenteredHeadMatExpressions

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeNormalizeCovered322
open GeneralDeclarationPatterns (Pattern Constructors WellScoped ArgsWellScoped normalize normalizeArgs)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCenteredHeadWFSource (ConstructorUse PatternCovered PatternsCovered)
open GeneralDeclarativeNormalizeScope322 (checked_normal well_args)
open GeneralNominalCenteredHeadMatExpressions (translate translateMany translate_complete translateMany_complete)

noncomputable def interpreted (c : Constructors) (interp : Interpretation) : Constructors := by
  classical
  exact fun key => (c key).filter fun d => decide (ConstructorUse c interp key d.parameters.length)

theorem selected_iff {c : Constructors} {interp : Interpretation} {name decl}
    : interpreted c interp name = some decl ↔
      c name = some decl ∧ ConstructorUse c interp name decl.parameters.length := by
  classical
  cases orig : c name <;> simp [interpreted,orig]

theorem lookup_scope {c : Constructors} {interp : Interpretation} (name arity : Nat) :
    ConstructorUse c interp name arity ↔
    ∃ decl, interpreted c interp name = some decl ∧ decl.parameters.length = arity := by
  constructor
  · intro cover
    have remembered := cover
    obtain ⟨decl,found,card,_⟩ := cover
    refine ⟨decl,(selected_iff).mpr ⟨found,?_⟩,card⟩
    simpa only [card] using remembered
  · rintro ⟨decl,meaning,card⟩
    exact card ▸ (selected_iff.mp meaning).2

mutual
 theorem scope_iff (c : Constructors) (interp : Interpretation) (p : Pattern) :
    PatternCovered c interp p ↔ WellScoped (interpreted c interp) p := by
  cases p with
  | var => rfl
  | app name args => exact and_congr (lookup_scope name args.length) (scope_many_iff c interp args)
  | record label a b => exact and_congr (scope_iff c interp a) (scope_iff c interp b)
  | variant tag p => exact scope_iff c interp p
  | join a b => exact and_congr (scope_iff c interp a) (scope_iff c interp b)
 termination_by sizeOf p
 theorem scope_many_iff (c : Constructors) (interp : Interpretation) (ps : List Pattern) :
    PatternsCovered c interp ps ↔ ArgsWellScoped (interpreted c interp) ps := by
  cases ps with
  | nil => rfl
  | cons first rest => exact and_congr (scope_iff c interp first) (scope_many_iff c interp rest)
 termination_by sizeOf ps
end

/-- Only constructors actually appearing in the original source require
metadata. Hiding and grouping do not introduce uncovered applications. -/
theorem normalize_covered {c : Constructors} {interp : Interpretation} {p : Pattern}
    (source : PatternCovered c interp p) : PatternCovered c interp (normalize p) :=
  (scope_iff c interp (normalize p)).mpr (checked_normal _ p ((scope_iff c interp p).mp source))

theorem normalize_args_covered {c : Constructors} {interp : Interpretation} {patterns : List Pattern}
    (source : PatternsCovered c interp patterns) : PatternsCovered c interp (normalizeArgs patterns) :=
  (scope_many_iff c interp (normalizeArgs patterns)).mpr
    (well_args _ patterns ((scope_many_iff c interp patterns).mp source))

theorem normalized_compiles {c : Constructors} {interp : Interpretation} {p : Pattern}
    (source : PatternCovered c interp p) :
    ∃ code, translate c interp (normalize p) = some code :=
  translate_complete (normalize_covered source)

end Yulang.GeneralDeclarativeNormalizeCovered322
