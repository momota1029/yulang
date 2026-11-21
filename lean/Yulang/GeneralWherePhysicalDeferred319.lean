import Yulang.GeneralWherePhysicalNominal319

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 21000
set_option maxHeartbeats 14000000
namespace Yulang.GeneralWherePhysicalDeferred319
open GeneralWherePhysicalIndex319 (old new)
open GeneralWherePhysicalBase319 (Layout expand assignment_old source_old)
open GeneralWherePhysicalNominal319 (extend Checked Extra Added refinement denotes_iff nominal_old nominal_new)
open GeneralWherePhysicalView319 (head_term)
open GeneralCanonicalObservations (Recorded Observation)
open GeneralNominalState (State Models)
open GeneralNominalCommonBridge (Assignment)
open GeneralNormalizedObservation (Head Rewrites)
open Core.PresenceGeneration (TyTerm)

def deferred (s : State) (n : Nat) : Added s n := fun _ => .deferred .unresolved

theorem noAdded (l : Layout s.base n) (extra : Extra s n) : Checked l extra (deferred s n) := by
  intro i t notThere
  cases notThere

abbrev laid (s : State) (l : Layout s.base n) (extra : Extra s n) : State :=
  extend s l extra (deferred s n) (noAdded l extra)

theorem known_term (l : Layout s.base n) (extra : Extra s n)
    (m : Assignment) (valid : Models s m) (i : Fin (s.base.slots+n))
    (t : TyTerm (Fin (s.base.slots+n))) (hit : ((laid s l extra).view.heads i).term = some t) :
    (Observation.normalized (expand l extra) i t).Holds m := by
  refine Fin.addCases (fun j h => ?_) (fun j h => ?_) i hit
  · change ((Fin.addCases (motive := fun _ => Head s.view.shapes (s.base.slots+n))
      (fun k => GeneralWherePhysicalView319.head (old n) (s.view.heads k)) (deferred s n) (old n j))).term = _ at h
    rw [Fin.addCases_left,head_term] at h
    cases idx : (s.view.heads j).term with
    | none => simp [idx] at h
    | some saved =>
      rw [idx] at h
      have term := Option.some.inj h
      subst t
      change CommonNominalFullCarrier.Equivalent (m (GeneralWherePhysicalBase319.source l (old n j))).1 _
      rw [source_old,TyTerm.eval_rename,assignment_old]
      exact GeneralNominalState.normalized_models s m valid j saved idx
  · change ((Fin.addCases (motive := fun _ => Head s.view.shapes (s.base.slots+n))
      (fun k => GeneralWherePhysicalView319.head (old n) (s.view.heads k)) (deferred s n) (new s.base.slots j))).term = _ at h
    rw [Fin.addCases_right] at h
    cases h

/-- When new physical slots are still deferred, the expanded observer
publishes only old semantic observations, even if the slot identities
themselves are entirely new. No new endpoint equation is assumed. -/
theorem observations_from_old (l : Layout s.base n) (extra : Extra s n)
    (m : Assignment) (valid : Models s m) (seen : Recorded (laid s l extra) observation) :
    observation.Holds m := by
  cases seen with
  | scalar slot scalar recorded =>
    exact known_term l extra m valid slot _ (by rw [recorded]; rfl)
  | structural slot kind children recorded =>
    exact known_term l extra m valid slot _ (by rw [recorded]; rfl)
  | nominal i d found =>
    refine Fin.addCases (fun j h => ?_) (fun j h => ?_) i found
    · change GeneralWherePhysicalNominal319.nominals s n (old n j) = some d at h
      rw [nominal_old] at h
      cases hit : s.nominals j with
      | none => simp [hit] at h
      | some oldDesc =>
        rw [hit] at h
        have eq := Option.some.inj h
        subst d
        exact (denotes_iff (refinement s l extra (deferred s n) (noAdded l extra)) m j oldDesc).mpr
          (valid.2.1 j oldDesc hit)
    · change GeneralWherePhysicalNominal319.nominals s n (new s.base.slots j) = some d at h
      rw [nominal_new] at h; cases h

end Yulang.GeneralWherePhysicalDeferred319
