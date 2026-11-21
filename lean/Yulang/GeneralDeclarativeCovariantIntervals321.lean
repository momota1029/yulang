import Yulang.GeneralDeclarativePairProjection321
import Yulang.GeneralDeclarativeCaptureClosure320

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeCovariantIntervals321
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeDemand320 (Bounds bounds_sound)
open GeneralDeclarativeWhere319 (Capture InInterval)
open GeneralDeclarativeEntailment320 (Entails)
open GeneralDeclarativePairCut321 (pairCode)
open GeneralDeclarativeCaptureClosure320 (atoms withOrdinary ordinary_models)
open CommonNominalFullCarrier (common_pair_iff subtype_trans model)
open GeneralNominalCommonBridge (Assignment)
open PresenceNormalForm (Atom All)

/-- Component intervals come from the actual pair's ordinary projection
together with both endpoint projections. Unlike the nominal argument
theorem, covariance does not recover actual component names from endpoints. -/
structure PairBounds (s : State) (whole first second : Capture) : Prop where
  interval : Bounds s whole
  lower : Entails s ⟨whole.lower,pairCode first.lower second.lower⟩
  actual : Entails s ⟨whole.center,pairCode first.center second.center⟩
  upper : Entails s ⟨whole.upper,pairCode first.upper second.upper⟩

theorem component_bounds {s : State} {whole left right : Capture}
    (projections : PairBounds s whole left right) (m : Assignment) (valid : Models s m) :
    InInterval (m left.lower).1 (m left.upper).1 (m left.center).1 ∧
    InInterval (m right.lower).1 (m right.upper).1 (m right.center).1 := by
  have b := bounds_sound projections.interval m valid
  have l := projections.lower m valid
  have c := projections.actual m valid
  have u := projections.upper m valid
  have leftRight := (common_pair_iff ..).mp (subtype_trans l.2 (subtype_trans b.1 c.1))
  have rightLeft := (common_pair_iff ..).mp (subtype_trans c.2 (subtype_trans b.2 u.1))
  exact ⟨⟨leftRight.1,rightLeft.1⟩,⟨leftRight.2,rightLeft.2⟩⟩

theorem projected_atoms {s : State} {whole left right : Capture}
    (projections : PairBounds s whole left right) (m : Assignment) (valid : Models s m) :
    All model m (atoms left ++ atoms right) := by
  have spans := component_bounds projections m valid
  apply (PresenceNormalForm.all_append ..).mpr
  constructor
  · intro atom present
    rcases List.mem_cons.mp present with rfl|tail
    · exact spans.1.1
    · cases List.mem_singleton.mp tail
      exact spans.1.2
  · intro atom present
    rcases List.mem_cons.mp present with rfl|tail
    · exact spans.2.1
    · cases List.mem_singleton.mp tail
      exact spans.2.2

theorem record_pair_bounds {s : State} {whole left right : Capture}
    (projections : PairBounds s whole left right) (m : Assignment) :
    Models (withOrdinary s (atoms left ++ atoms right)) m ↔ Models s m :=
  (ordinary_models m).trans ⟨And.left,fun valid => ⟨valid,projected_atoms projections m valid⟩⟩

theorem recorded_components (s : State) (left right : Capture) :
    Bounds (withOrdinary s (atoms left ++ atoms right)) left ∧
      Bounds (withOrdinary s (atoms left ++ atoms right)) right := by
  have lift (a : Atom Nat) (used : a ∈ atoms left ++ atoms right) :
      a ∈ (withOrdinary s (atoms left ++ atoms right)).normal.ordinary :=
    List.mem_append_right _ used
  constructor
  · exact ⟨.constraint (lift _ (List.mem_append_left _ List.mem_cons_self)),
      .constraint (lift _ (List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self)))⟩
  · exact ⟨.constraint (lift _ (List.mem_append_right _ List.mem_cons_self)),
      .constraint (lift _ (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)))⟩

end Yulang.GeneralDeclarativeCovariantIntervals321
