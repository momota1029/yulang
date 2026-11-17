import Yulang.GeneralDictionaryLooseIterationFrame240
import Yulang.GeneralDictionaryLooseIterationPatched240
import Yulang.GeneralDictionaryLooseLoopInitial240
set_option backward.isDefEq.respectTransparency false
/-! Stage invariants for the proposed actual source iteration. The zero stage
is constructed here; later stages require actual guarded rounds, not a desired
reachable-path assumption. -/
namespace Yulang.GeneralDictionaryLooseIterationStage240
open GeneralDictionaryLooseLoopSource240
open GeneralDictionaryLooseIterationBook240 (plan)
open GeneralDictionaryLooseIterationFrame240 (Shape)
open GeneralDictionaryLooseFamilyNovel240 (bad)
open GeneralNominalVersionedJournal232

structure Stage (n : Nat) where
 state : State roles
 shape : Shape state n
 reachable : B4TargetV8.Reachable (GeneralNominalPointSourceBoundary240.boundary roles)
   sourceRegistry root state
 recorded : ∀ index < n, plan index ∈ state.plans
 valid : Models state model
 future : ∀ index, n ≤ index → Models state (bad index)

theorem initial_shape : Shape initial 0 where
 current := GeneralDictionaryLooseIterationBook240.context_zero.symm
 source := rfl
 rawSites := rfl
 centers := rfl
 choice := by intro _ h; cases h

noncomputable def zero : Stage 0 where
 state := initial
 shape := initial_shape
 reachable := ⟨initial,GeneralDictionaryLooseLoopInitial240.initial_source,.refl⟩
 recorded := by intro _ before; omega
 valid := initial_model
 future := fun index _ => GeneralDictionaryLooseIterationPatched240.initial_model index

theorem novel (stage : Stage n) :
 ¬ GeneralNominalVersionedKernel232.Committed stage.state (plan n) :=
 GeneralDictionaryLooseFamilyNovel240.novel_from_bad n _ _ _ stage.state (stage.future n (Nat.le_refl n))
end Yulang.GeneralDictionaryLooseIterationStage240
