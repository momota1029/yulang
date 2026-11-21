import Yulang.GeneralDeclarativeOrigins321
import Yulang.GeneralDeclarativeLowerKnown321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeNormalSupport321
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeOrigins321 (Origin Available Supported Backed)
open GeneralDeclarativeLowerKnown321 (Knows)
open PresenceNormalForm (Atom)

structure NormalSupport (s : State) (completed : Nat → Prop) where
  eq : Supported s completed
  atomFrom : Atom Nat → Origin → Prop
  spanFrom : (Nat × Nat) → Origin → Prop
  ordinary_atom : ∀ {atom o}, atomFrom atom o → atom ∈ s.normal.ordinary
  ordinary_span : ∀ {span o}, spanFrom span o → span ∈ s.normal.intervals

def AtomReady (p : NormalSupport s completed) (atom : Atom Nat) : Prop :=
  ∃ origin, p.atomFrom atom origin ∧ Available completed origin

def SpanReady (p : NormalSupport s completed) (span : Nat × Nat) : Prop :=
  ∃ origin, p.spanFrom span origin ∧ Available completed origin

/-- The stronger observational restriction tracks core type/row atoms and
interval links as well. No such fact is removed from the actual model state. -/
noncomputable def observed (p : NormalSupport s completed) : State := by
  classical
  exact ⟨⟨s.normal.ordinary.filter (fun a => decide (AtomReady p a)),
    s.normal.intervals.filter (fun pr => decide (SpanReady p pr))⟩,
    (GeneralDeclarativeOrigins321.restriction p.eq).equations⟩

theorem atom_iff (p : NormalSupport s completed) (atom : Atom Nat) :
    atom ∈ (observed p).normal.ordinary ↔ AtomReady p atom := by
  classical
  simp only [observed,List.mem_filter,decide_eq_true_eq]
  exact ⟨And.right,fun h => ⟨p.ordinary_atom h.choose_spec.1,h⟩⟩

theorem span_iff (p : NormalSupport s completed) (span : Nat × Nat) :
    span ∈ (observed p).normal.intervals ↔ SpanReady p span := by
  classical
  simp only [observed,List.mem_filter,decide_eq_true_eq]
  exact ⟨And.right,fun h => ⟨p.ordinary_span h.choose_spec.1,h⟩⟩

theorem restricted_valid (p : NormalSupport s completed) (m) (valid : Models s m) :
    Models (observed p) m :=
  ⟨⟨fun a h => valid.1.1 a (p.ordinary_atom ((atom_iff p a).mp h).choose_spec.1),
    fun pr h => valid.1.2 pr (p.ordinary_span ((span_iff p pr).mp h).choose_spec.1)⟩,
    (GeneralDeclarativeOrigins321.restrict_models p.eq m valid).2⟩

theorem without_unsettled_link (p : NormalSupport s completed) (pr : Nat × Nat)
    (only : ∀ origin, p.spanFrom pr origin → ∃ owner, origin = .output owner ∧ ¬completed owner) :
    pr ∉ (observed p).normal.intervals := by
  intro h
  obtain ⟨origin,source,ready⟩ := (span_iff p pr).mp h
  obtain ⟨owner,rfl,unknown⟩ := only origin source
  cases ready with
  | completed known => exact unknown known

theorem ordinary_link_stays (p : NormalSupport s completed) (pr : Nat × Nat)
    (owned : p.spanFrom pr (.output owner)) (m) (valid : Models s m) :
    CommonNominalFullCarrier.Subtype (m pr.1).1 (m pr.2).1 :=
  valid.1.2 pr (p.ordinary_span owned)

end Yulang.GeneralDeclarativeNormalSupport321
