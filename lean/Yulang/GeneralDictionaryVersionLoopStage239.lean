import Yulang.GeneralDictionaryVersionLoopFrame239
import Yulang.GeneralDictionaryVersionLoopPatched239
import Yulang.GeneralDictionaryVersionLoopInitial238
set_option backward.isDefEq.respectTransparency false
/-! Stage invariants for the proposed actual source iteration. The zero stage
is constructed here; later stages require actual guarded rounds, not a desired
reachable-path assumption. -/
namespace Yulang.GeneralDictionaryVersionLoopStage239
open GeneralDictionaryVersionLoopSource237
open GeneralDictionaryVersionLoopBook239 (plan)
open GeneralDictionaryVersionLoopFrame239 (Shape)
open GeneralDictionaryVersionLoopFamilyNovel239 (bad)
open GeneralNominalVersionedJournal232

structure Stage (n : Nat) where
 state : State roles
 shape : Shape state n
 reachable : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles)
   sourceRegistry root state
 recorded : ∀ index < n, plan index ∈ state.plans
 valid : Models state model
 future : ∀ index, n ≤ index → Models state (bad index)

theorem initial_shape : Shape initial 0 where
 current := GeneralDictionaryVersionLoopBook239.context_zero.symm
 source := rfl
 rawSites := rfl
 centers := rfl
 choice := by intro _ h; cases h

noncomputable def zero : Stage 0 where
 state := initial
 shape := initial_shape
 reachable := ⟨initial,GeneralDictionaryVersionLoopInitial238.initial_source,.refl⟩
 recorded := by intro _ before; omega
 valid := initial_model
 future := fun index _ => GeneralDictionaryVersionLoopPatched239.initial_model index

theorem novel (stage : Stage n) :
 ¬ GeneralNominalVersionedKernel232.Committed stage.state (plan n) :=
 GeneralDictionaryVersionLoopFamilyNovel239.novel_from_bad n _ _ _ stage.state (stage.future n (Nat.le_refl n))
end Yulang.GeneralDictionaryVersionLoopStage239
