import Yulang.GeneralRebaseSemanticChart281
import Yulang.GeneralRebaseProjectedEdgeCount279

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseChartStep281
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralRebaseMixedCounts277 (Actual quietCap)
open GeneralRebaseProjectedEdgeCount279 (Seen Fresh)
open GeneralRebaseSemanticChart281 (Entails Gain Loss Decreases)
open GeneralRebaseQuietBound277 (Counted remaining_le)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable split reachable_step administrative_plans)
open GeneralNominalFiniteProgress (remaining remaining_monotone remaining_decreases)

structure Chart (F V : Type) where
  facts : List F
  agrees : Assignment → V → Prop
  meaning : F → V → Prop

def Public (chart : Chart F V) (state : State roles) (value : V) : Prop :=
  ∃ m, chart.agrees m value ∧ Models state m

def Recorded (chart : Chart F V) (state : State roles) (fact : F) : Prop :=
  Entails chart.meaning (Public chart) state fact

def Strict (chart : Chart F V) (before after : State roles) : Prop :=
  Fresh before after ∨ Gain chart.facts chart.meaning (Public chart) before after

def Step (chart : Chart F V) (r : Registry) (root : Occurrence roles)
    (before after : State roles) : Prop :=
  Actual r root before after ∧ (after.plans.length = before.plans.length ∨ Strict chart before after)

theorem restrict {chart : Chart F V} (step : Actual r root before after) :
    Decreases (Public chart) before after := by
  rintro v ⟨m,agreed,holds⟩
  exact ⟨m,agreed,GeneralNominalVersionedMixedKernel234.step_models step holds⟩

theorem monotone (chart : Chart F V) (step : Actual r root before after) :
    ∀ f, Recorded chart before f → Recorded chart after f :=
  GeneralRebaseSemanticChart281.entailment_mono (restrict step)

theorem quiet_kept {chart : Chart F V} (step : Actual r root before after)
    (quiet : after.plans.length = before.plans.length) : Step chart r root before after :=
  ⟨step,Or.inl quiet⟩

theorem semantic_kept {chart : Chart F V} (step : Actual r root before after)
    (gain : Gain chart.facts chart.meaning (Public chart) before after) :
    Step chart r root before after := ⟨step,Or.inr (Or.inr gain)⟩

theorem graph_kept {chart : Chart F V} (step : Actual r root before after) (fresh : Fresh before after) :
    Step chart r root before after := ⟨step,Or.inr (Or.inl fresh)⟩

theorem strict_iff {chart : Chart F V}
    (exact : GeneralRebaseSemanticChart281.Complete chart.facts chart.meaning (Public chart) after) :
    Strict chart before after ↔ Fresh before after ∨ Loss (Public chart) before after :=
  or_congr Iff.rfl (GeneralRebaseSemanticChart281.loss_iff_gain exact).symm

theorem strict_relative {chart : Chart F V} {base : V → Prop}
    (domain : ∀ v, Public chart before v → base v)
    (exact : ∀ v, base v →
      (Public chart after v ↔ ∀ f ∈ chart.facts, Recorded chart after f → chart.meaning f v)) :
    Strict chart before after ↔ Fresh before after ∨ Loss (Public chart) before after :=
  or_congr Iff.rfl (GeneralRebaseSemanticChart281.relative_loss_iff domain exact).symm

theorem uncount {r : Registry} {root : Occurrence roles} {start after : State roles}
    {chart : Chart F V} (walk : Counted (Step chart r root) start n after) :
    Counted (Actual r root) start n after := by
  induction walk with
  | nil => exact .nil
  | tail _ step ih => exact .tail ih step.1

end Yulang.GeneralRebaseChartStep281
