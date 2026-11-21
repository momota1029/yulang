import Yulang.GeneralDeclarativeStableMerge329
import Yulang.GeneralDeclarativeOutputOrigins323

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeStableAnchor329
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeMerge320 (Merge equality_sound lower_exact upper_exact)
open GeneralDeclarativeBounds319 (bound_sound)
open GeneralDeclarativeCaptureClosure320 (withOrdinary ordinary_models)
open GeneralDeclarativeOrigins321 (Supported restriction backed_iff)
open GeneralDeclarativeLowerKnown321 (Alias Knows knows_alias)
open GeneralDeclarativeGrowth327 (aliases ordinary)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Equivalent subtype_trans subtype_refl)

def LiteralPoints (seed : Capture) (other : List Capture) : Prop :=
  ∀ a ∈ seed :: other, a.lower = a.center ∧ a.upper = a.center

/-- A repeated binder whose input views are genuine named points
has ordinary joined/met endpoints equal to its selected center.
For true nonpoint intervals no such collapse is asserted. -/
theorem values {s : State} (merged : Merge s seed rem cap) (points : LiteralPoints seed rem)
    (m : Assignment) (valid : Models s m) :
    Equivalent (m cap.lower).1 (m cap.center).1 ∧ Equivalent (m cap.upper).1 (m cap.center).1 := by
  have lo := equality_sound merged.lowerEq m valid
  have hi := equality_sound merged.upperEq m valid
  have tied (a : Capture) (seen : a ∈ seed::rem) : Equivalent (m a.center).1 (m cap.center).1 :=
    ⟨bound_sound m valid.1 (merged.sameCenter a seen).1,
     bound_sound m valid.1 (merged.sameCenter a seen).2⟩
  have everyLower := (lower_exact m seed rem (m cap.center).1).mpr (fun a h =>
    by rw [(points a h).1]; exact (tied a h).1)
  have everyUpper := (upper_exact m seed rem (m cap.center).1).mpr (fun a h =>
    by rw [(points a h).2]; exact (tied a h).2)
  have seedInto := ((lower_exact m seed rem _).mp (subtype_refl _)) seed List.mem_cons_self
  have seedOut := ((upper_exact m seed rem _).mp (subtype_refl _)) seed List.mem_cons_self
  rw [(points seed List.mem_cons_self).1] at seedInto
  rw [(points seed List.mem_cons_self).2] at seedOut
  exact ⟨⟨subtype_trans lo.1 everyLower,
    subtype_trans (tied seed List.mem_cons_self).2 (subtype_trans seedInto lo.2)⟩,
    ⟨subtype_trans hi.1 (subtype_trans seedOut (tied seed List.mem_cons_self).1),
      subtype_trans everyUpper hi.2⟩⟩

def atoms (cap : Capture) : List (PresenceNormalForm.Atom Nat) :=
  [.tyLe (.var cap.lower) (.var cap.center),.tyLe (.var cap.center) (.var cap.lower),
   .tyLe (.var cap.upper) (.var cap.center),.tyLe (.var cap.center) (.var cap.upper)]

def close (s : State) (cap : Capture) : State := withOrdinary s (atoms cap)

theorem preserves {s : State} (merged : Merge s seed rem cap) (points : LiteralPoints seed rem)
    (m : Assignment) : Models (close s cap) m ↔ Models s m := by
  rw [close,ordinary_models]
  refine ⟨And.left,fun fit => ⟨fit,?_⟩⟩
  obtain ⟨lo,hi⟩ := values merged points m fit
  intro atom listed
  simp only [atoms,List.mem_cons,List.not_mem_nil,or_false] at listed
  rcases listed with h|h|h|h <;> cases h
  · exact lo.1
  · exact lo.2
  · exact hi.1
  · exact hi.2

def origins {s : State} (p : Supported s done) (cap : Capture) : Supported (close s cap) done :=
  ⟨p.derivesFrom,fun x => p.ordinary x⟩

theorem same_inherited {s : State} (p : Supported s done) (cap : Capture) (e : Equation) :
    e ∈ (restriction (origins p cap)).equations ↔ e ∈ (restriction p).equations := by
  rw [backed_iff,backed_iff]
  rfl

theorem knowledge_transferred {s : State} (p : Supported s done) (known : Knows (restriction p) cap.center tag) :
    Knows (restriction (origins p cap)) cap.lower tag := by
  have lift : GeneralDeclarativeGrowth327.Extends (restriction p) (restriction (origins p cap)) :=
    ⟨fun _ listed => List.mem_append_left _ listed,fun _ h => h,
      fun e h => (same_inherited p cap e).mpr h⟩
  have next : Knows (restriction (origins p cap)) cap.center tag := by
    obtain ⟨e,stored,link,shape⟩ := known
    exact ⟨e,lift.equations stored,aliases lift link,shape⟩
  exact knows_alias (.bounds (.constraint (List.mem_append_right _ List.mem_cons_self))
    (.constraint (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)))) next

/-- A named point aggregate can carry an already authorized
constructor to the generated child's lower endpoint. The proof
retains origins exactly, and the atom addition is justified in all
models by the selected center equations plus the actual point views. -/
theorem anchored {s : State} (p : Supported s done) (merged : Merge s seed rem cap)
    (points : LiteralPoints seed rem) (known : Knows (restriction p) cap.center tag) :
    (∀ m, Models (close s cap) m ↔ Models s m) ∧
    Knows (restriction (origins p cap)) cap.lower tag :=
  ⟨preserves merged points,knowledge_transferred p known⟩

end Yulang.GeneralDeclarativeStableAnchor329
