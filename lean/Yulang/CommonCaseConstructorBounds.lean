import Yulang.CommonCaseRecordSourceCoverage
import Yulang.CommonPatternGenerationProvenance

/-! Actual finite constraints for constructor-tree and record input bounds.
Fresh child references expose variant comparisons at supported root positions;
no unsupported nested target or semantic comparison atom is introduced. -/

namespace Yulang.CommonCaseConstructorBounds

set_option backward.isDefEq.respectTransparency false

open Core.PresenceGeneration
open CommonCaseBaseOrdered (Tree)

def generate : Tree → {α : Type} → TyTerm α → Formula α
  | .base kind, _, input => .tyLe input (.base kind)
  | .pair first last, _, input => .existsSlot (.existsSlot (.and
      (.tyLe (input.rename fun x => some (some x)) (.pair fresh₀.ty fresh₁.ty))
      (.and (generate first fresh₀.ty) (generate last fresh₁.ty))))
  | .variant tag payload, _, input => .existsSlot (.and
      (.tyLe (input.rename some) (.variant tag (.var none))) (generate payload (.var none)))

theorem generate_exact (tree : Tree) (ρ : α → Comp Common.model) (input : TyTerm α) :
    (generate tree input).Holds Common.model ρ ↔ Common.Subtype (input.eval Common.model ρ) tree.type := by
  induction tree generalizing α with
  | base kind => rfl
  | pair first last ihf ihl =>
      simp only [generate, Formula.Holds, ihf, ihl, fresh₀, fresh₁, CompTerm.var,
        TyTerm.eval_rename, TyTerm.eval, Function.comp_def, extend_some]
      constructor
      · rintro ⟨left, right, below, firstBelow, lastBelow⟩
        exact Common.subtype_trans below ((Common.common_pair_iff _ _ _ _).mpr ⟨firstBelow, lastBelow⟩)
      · intro below
        exact ⟨(first.type, Common.rowEmpty), (last.type, Common.rowEmpty), below,
          Common.subtype_refl _, Common.subtype_refl _⟩
  | variant tag payload ih =>
      simp only [generate, Formula.Holds, ih, TyTerm.eval_rename, TyTerm.eval, extend_comp_some]
      constructor
      · rintro ⟨child, below, childBelow⟩
        exact Common.subtype_trans below ((Common.common_variant_iff tag _ _).mpr childBelow)
      · intro below
        exact ⟨(payload.type, Common.rowEmpty), below, Common.subtype_refl _⟩

def generateRequired (name : Nat) (tree : Tree) (input : TyTerm α) : Formula α :=
  .existsSlot (.and (.tyLe (input.rename some) (.required name (.var none))) (generate tree (.var none)))

theorem generateRequired_exact (name : Nat) (tree : Tree) (ρ : α → Comp Common.model) (input : TyTerm α) :
    (generateRequired name tree input).Holds Common.model ρ ↔
      Common.Subtype (input.eval Common.model ρ) (Common.required name tree.type) := by
  simp only [generateRequired, Formula.Holds, generate_exact, TyTerm.eval_rename, TyTerm.eval, extend_comp_some]
  constructor
  · rintro ⟨child, below, childBelow⟩
    exact Common.subtype_trans below (Common.common_record_mono name childBelow (Common.subtype_refl Common.emptyRecord))
  · intro below
    exact ⟨(tree.type, Common.rowEmpty), below, Common.subtype_refl _⟩

def generateRecord : CommonCaseRecordReadout.Specification → {α : Type} → TyTerm α → Formula α
  | [], _, input => .tyLe input .emptyRecord
  | (name, tree) :: rest, _, input => .and (generateRequired name tree input) (generateRecord rest input)

theorem generateRecord_exact (specification : CommonCaseRecordReadout.Specification)
    (ρ : α → Comp Common.model) (input : TyTerm α) :
    (generateRecord specification input).Holds Common.model ρ ↔
      Common.Subtype (input.eval Common.model ρ) (CommonCaseRecordReadout.type specification) := by
  induction specification with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨name, tree⟩
      simp only [generateRecord, Formula.Holds, generateRequired_exact, ih, CommonCaseRecordReadout.type]
      exact (Common.common_inter_is_meet _ _ _).symm

open CommonPatternGenerationProvenance

theorem safe_generate (tree : Tree) (input : TyTerm α) (good : Input input) : SafeFormula (generate tree input) := by
  induction tree generalizing α with
  | base kind => exact safe_tyLe _ _ good (.old rfl) rfl
  | pair first last ihf ihl =>
      exact .existsSlot (.existsSlot (.and
        (safe_tyLe _ _ (good.rename _) (.old rfl) rfl)
        (.and (ihf fresh₀.ty ⟨rfl, rfl, rfl⟩) (ihl fresh₁.ty ⟨rfl, rfl, rfl⟩))))
  | variant tag payload ih =>
      exact .existsSlot (.and (safe_tyLe _ _ (good.rename some) (.variant rfl) rfl) (ih (.var none) ⟨rfl, rfl, rfl⟩))

theorem safe_generateRequired (name : Nat) (tree : Tree) (input : TyTerm α) (good : Input input) :
    SafeFormula (generateRequired name tree input) :=
  .existsSlot (.and (safe_tyLe _ _ (good.rename some) (.old rfl) rfl) (safe_generate tree (.var none) ⟨rfl, rfl, rfl⟩))

theorem safe_generateRecord (specification : CommonCaseRecordReadout.Specification)
    (input : TyTerm α) (good : Input input) : SafeFormula (generateRecord specification input) := by
  induction specification with
  | nil => exact safe_tyLe _ _ good (.old rfl) rfl
  | cons entry rest ih => exact .and (safe_generateRequired entry.1 entry.2 input good) ih

end Yulang.CommonCaseConstructorBounds
