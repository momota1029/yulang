import Yulang.GeneralDeclarativeStableAnchor329
import Yulang.GeneralDeclarativeCongruence322

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeStableBackedAnchor329
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeMerge320 (Merge equality_sound lower_exact upper_exact)
open GeneralDeclarativeBounds319 (bound_sound)
open GeneralDeclarativeOrigins321 (Supported restriction restrict_models)
open GeneralDeclarativeStableAnchor329 (atoms close origins knowledge_transferred)
open GeneralDeclarativeLowerKnown321 (Alias Knows)
open GeneralDeclarativeCaptureClosure320 (ordinary_models)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Equivalent subtype_trans subtype_refl)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans)

def BackedPoints {s : State} (p : Supported s done) (seed : Capture) (rest : List Capture) : Prop :=
  ∀ a ∈ seed :: rest, Alias (restriction p) a.lower a.center ∧ Alias (restriction p) a.upper a.center

theorem alias_value {s : State} {p : Supported s done}
    (backed : Alias (restriction p) a b) (m : Assignment) (fit : Models s m) :
    Equivalent (m a).1 (m b).1 :=
  GeneralDeclarativeCongruence322.sound (.variable backed) m (restrict_models p m fit) .actual

theorem all_values {s : State} {p : Supported s done} (merge : Merge s seed rest cap)
    (point : BackedPoints p seed rest) (m : Assignment) (fit : Models s m) :
    Equivalent (m cap.lower).1 (m cap.center).1 ∧ Equivalent (m cap.upper).1 (m cap.center).1 := by
  have lo := equality_sound merge.lowerEq m fit
  have hi := equality_sound merge.upperEq m fit
  have linked (a) (seen : a ∈ seed :: rest) : Equivalent (m a.center).1 (m cap.center).1 :=
    ⟨bound_sound m fit.1 (merge.sameCenter a seen).1,bound_sound m fit.1 (merge.sameCenter a seen).2⟩
  have lows (a) (seen : a ∈ seed :: rest) : Equivalent (m a.lower).1 (m cap.center).1 :=
    eqv_trans (alias_value (point a seen).1 m fit) (linked a seen)
  have highs (a) (seen : a ∈ seed :: rest) : Equivalent (m a.upper).1 (m cap.center).1 :=
    eqv_trans (alias_value (point a seen).2 m fit) (linked a seen)
  have anyLo := (lower_exact m seed rest (m cap.center).1).mpr (fun a h => (lows a h).1)
  have anyHi := (upper_exact m seed rest (m cap.center).1).mpr (fun a h => (highs a h).2)
  have seedIn := ((lower_exact m seed rest _).mp (subtype_refl _)) seed List.mem_cons_self
  have seedOut := ((upper_exact m seed rest _).mp (subtype_refl _)) seed List.mem_cons_self
  exact ⟨⟨subtype_trans lo.1 anyLo,subtype_trans (lows seed List.mem_cons_self).2 (subtype_trans seedIn lo.2)⟩,
    ⟨subtype_trans hi.1 (subtype_trans seedOut (highs seed List.mem_cons_self).1),subtype_trans anyHi hi.2⟩⟩

/-- Distinct logical endpoints can be collapsed only when they are
already backed equivalent to their own actual names. A pending-only
output equality cannot serve as a BackedPoints witness. The ordinary
merge equations and their chosen actual anchor are separate premises. -/
theorem expose {s : State} {p : Supported s done} (merge : Merge s seed rest cap)
    (points : BackedPoints p seed rest) (anchor : Knows (restriction p) cap.center tag) :
    (∀ m, Models (close s cap) m ↔ Models s m) ∧
      Knows (restriction (origins p cap)) cap.lower tag := by
  refine ⟨?_,knowledge_transferred p anchor⟩
  intro m
  rw [close,ordinary_models]
  refine ⟨And.left,fun fit => ⟨fit,?_⟩⟩
  intro atom accepted
  have ⟨lo,hi⟩ := all_values merge points m fit
  simp only [atoms,List.mem_cons,List.not_mem_nil,or_false] at accepted
  rcases accepted with yes|yes|yes|yes <;> cases yes
  · exact lo.1
  · exact lo.2
  · exact hi.1
  · exact hi.2

end Yulang.GeneralDeclarativeStableBackedAnchor329
