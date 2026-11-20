import Yulang.GeneralRebaseRowProjection287

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29200
set_option maxHeartbeats 15200000
namespace Yulang.GeneralRebaseRowActualPaths287
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentPacket287 (child plan)
open GeneralRebaseRowParentFrame287 (after effect after_exact)
open GeneralRebaseRowParentStep287 (actual_step at_frame)
open GeneralRebaseRowAdministrative287 (point_closed equality_is_reflexive already_known)
open GeneralRebaseRowTrustedBoundary287 (putTop outside_source)
open GeneralRebaseRowChildRaw287 (before_exact)
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalVersionedMixedKernel234 (Step Equal Installable)

theorem before_known (n : Nat) (small : n ≤ 1) : GeneralNominalState.Known raw n :=
  already_known true n small

theorem before_point_closed : GeneralNominalReobservationSteps.PointClosed raw := point_closed true

theorem before_equality (n k : Nat) (all : Equal before n k) : n = k :=
  equality_is_reflexive true n k (fun m valid =>
    all m ((before_exact m).mpr ((after_exact true m).mp valid).1))

theorem before_no_refresh {c : GeneralNominalCandidates.Context}
    (cert : GeneralNominalVersionedMixedObservations233.Refresh before c)
    (n : Nat) (old : ¬ GeneralNominalState.Known raw n) (new : GeneralNominalState.Known c.state n) : False := by
  by_cases small : n ≤ 1
  · exact old (before_known n small)
  · let witness := putTop (model Common.rowEmpty) n
    have valid : Models before witness := (before_exact witness).mpr
      ((outside_source _ (by omega)).mpr ((before_exact _).mp (before_model Common.rowEmpty)))
    obtain ⟨test,obs,head⟩ := GeneralNominalCenteredHeadMatStepCache.known_has_head new
    have stored := GeneralNominalVersionedMixedObservations233.cache_sound cert.cache
      (GeneralNominalSupport.head_recorded head) valid
    have checked := GeneralDictionaryGroundCopy218Refresh.head_holds head stored
    change test.Holds (if n=n then .top else (model Common.rowEmpty n).1) at checked
    rw [ite_eq_left rfl] at checked
    exact GeneralDictionaryGroundCopy218Refresh.top_no_head test checked

theorem one_effect (choice : Bool) (e : Effect roles)
    (registryEq : e.registry = registry choice) (snapshotEq : e.snapshot = before.core)
    (planEq : e.plan = plan choice) : e = effect choice := by
  rcases e with ⟨r,s,p,f,u,ready⟩
  change r = registry choice at registryEq
  change s = before.core at snapshotEq
  change p = plan choice at planEq
  subst r
  subst s
  subst p
  rfl

theorem only_before (choice : Bool) (next : State roles)
    (step : Step (registry choice) root before next) : next = after choice := by
  obtain ⟨focus,reached,move⟩ := step
  have there : focus = root :=
    GeneralNominalVersionedMixedTerminalStable234.generated_only (by rfl) (by rfl) reached
  cases move with
  | administrative rule =>
    cases rule with
    | enqueue _ absent => exact (absent _ (List.mem_singleton_self _) there.symm).elim
    | refresh c cert n _ old new => exact (before_no_refresh cert n old new).elim
    | equate n k _ _ same novel =>
      have eq := before_equality n k same
      subst k
      exact (novel (fun m _ => ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩)).elim
    | reobserve rev _ novel =>
      exact (GeneralNominalReobservationSteps.pointClosed_no_revision before_point_closed rev novel).elim
  | refresh _ c cert n _ old new => exact (before_no_refresh cert n old new).elim
  | install e allowed _ =>
    have p := e.frame
    rw [allowed.registry_eq,allowed.snapshot_eq,there] at p
    rw [one_effect choice e allowed.registry_eq allowed.snapshot_eq (at_frame choice p)]
    rfl
  | merge a b first last _ novel =>
    cases List.mem_singleton.mp first
    cases List.mem_singleton.mp last
    exact (novel (.refl _)).elim

theorem one_or_zero (choice : Bool) (s : State roles)
    (trace : B4Target.Steps (Step (registry choice) root) before s) :
    s = before ∨ s = after choice := by
  induction trace with
  | refl => exact Or.inl rfl
  | tail earlier edge ih =>
    rcases ih with rfl|rfl
    · exact Or.inr (only_before choice _ edge)
    · exact (GeneralRebaseRowClosure287.no_step choice _ edge).elim

theorem raw_accessible (choice : Bool) :
    Acc (fun next prev => Step (registry choice) root prev next) before := by
  constructor
  intro next edge
  cases only_before choice _ edge
  constructor
  intro last step
  exact (GeneralRebaseRowClosure287.no_step choice last step).elim

theorem maximal_endpoint (choice : Bool) (s : State roles)
    (trace : B4Target.Steps (Step (registry choice) root) before s)
    (halted : ∀ next, ¬ Step (registry choice) root s next) : s = after choice := by
  rcases one_or_zero choice s trace with rfl|done
  · exact (halted _ (actual_step choice)).elim
  · exact done

end Yulang.GeneralRebaseRowActualPaths287
