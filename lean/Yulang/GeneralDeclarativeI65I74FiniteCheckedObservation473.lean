import Yulang.GeneralDeclarativeI65I74CheckedObservationPath473

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.LiteralVisits473
open ObservationAlternatives473 (Place Positions oldPosition graphOf checkAlternatives readAlternatives)
open QuotientObservation471 (ExactCone ConeWire Wire ReturnsUpToEquality ReachableClosed
  embedded cone createCone checkCone checked_cone_exact created_cone_exact exact_finite_cone_replay_exists
  replayCone cone_cycle_iff_ambient_at_the_actual_site exists_exact_finite_replay)
open CommonRoleGraphBisimulation (Bisimulation check_bisimulation_exact)
open CommonRoleRegularGraph (successors)
open FiniteWorklist (Path)

def GuardedObservationInput (s : OwnState) (pos : Positions n)
    (rel : List (Fin n × Fin n)) (root : Fin n) : Prop :=
  pos.signs.Nodup ∧ (List.ofFn (oldPosition pos)).Nodup ∧
  Bisimulation (graphOf s pos) rel ∧
  (∀ (a b : Fin n), (a,b) ∈ rel →
    checkAlternatives s pos rel a = true ∧ checkAlternatives s pos rel b = true) ∧
  (∀ a, Path (successors (graphOf s pos)) root a → checkAlternatives s pos rel a = true) ∧
  ReachableClosed (graphOf s pos) root

theorem checked_alternatives_exact_for_fixed_input_and_both_signs
    {s : OwnState} {pos : Positions n} {rel : List (Fin n × Fin n)} {root : Fin n}
    (inputs : GuardedObservationInput s pos rel root) (b : Bool) :
    (∃ (m k : Nat) (w : ConeWire n m) (q : Wire m k),
      readAlternatives s pos rel root w q = some b) ↔
      (b = true ↔ ReturnsUpToEquality (graphOf s pos) root) := by
  constructor
  · rintro ⟨_,_,w,q,ok⟩
    exact (ObservationAlternatives473.all_actual_alternatives_have_a_real_bisimilar_source_coordinate ok).1
  · intro sign
    obtain ⟨labels,coords,bisim,ends,inside,closed⟩ := inputs
    let g := graphOf s pos
    let w := createCone g root
    have actual : ExactCone g root w := created_cone_exact closed
    have accepted : checkCone g root w = true := checked_cone_exact.mpr actual
    have same := cone_cycle_iff_ambient_at_the_actual_site actual
    have exact := exists_exact_finite_replay actual.2.2.1 w.site
    have main : (List.finRange _).all (fun j => checkAlternatives s pos rel (embedded w j)) = true := by
      apply List.all_eq_true.mpr
      intro j _
      apply inside
      change Path (successors g) root (Vector.ofFn (QuotientObservation471.reachableNames g root).get)[j.val]
      simpa using (QuotientObservation471.path_at_cone_point (g := g) (root := root) j)
    have back : rel.all (fun (first,last) =>
        checkAlternatives s pos rel first && checkAlternatives s pos rel last) = true := by
      apply List.all_eq_true.mpr
      rintro ⟨a,d⟩ present
      exact Bool.and_eq_true_iff.mpr (ends a d present)
    have relation : CommonRoleGraphBisimulation.checkBisimulation (graphOf s pos) rel = true :=
      (check_bisimulation_exact ..).mpr bisim
    change checkCone (graphOf s pos) root w = true at accepted
    have out : ∃ (k : Nat) (q : Wire _ k), QuotientObservation471.replay (cone w) w.site q = some b := by
      cases b
      · exact exact.2.mpr (fun cy => Bool.false_ne_true (sign.mpr (same.mp cy)))
      · exact exact.1.mpr (same.mpr (sign.mp rfl))
    obtain ⟨k,q,out⟩ := out
    exact ⟨_,k,w,q,by simp [readAlternatives,labels,coords,relation,main,back,replayCone,accepted,out]⟩

theorem independent_checkpoint_reifies_the_exact_site_and_sign
    {s : OwnState} {pos : Positions n} {rel : List (Fin n × Fin n)} {root : Fin n}
    (inputs : GuardedObservationInput s pos rel root) (b : Bool)
    (sign : b = true ↔ ReturnsUpToEquality (graphOf s pos) root) :
    ∃ checkpoint : Checkpoint n, checkpoint.which = root ∧
      readCheck s pos rel (oldPosition pos root) checkpoint = some b := by
  obtain ⟨m,k,w,q,read⟩ :=
    (checked_alternatives_exact_for_fixed_input_and_both_signs inputs b).mpr sign
  exact ⟨⟨root,m,k,w,q⟩,rfl,by simp [readCheck,read]⟩

theorem accepted_observation_yields_all_input_guards
    {s : OwnState} {pos : Positions n} {rel : List (Fin n × Fin n)}
    {root : Fin n} {w : ConeWire n m} {q : Wire m k} {b}
    (ok : readAlternatives s pos rel root w q = some b) :
    GuardedObservationInput s pos rel root := by
  have ends := fun a d (seen : (a,d) ∈ rel) =>
    ObservationAlternatives473.accepted_bisimulation_checks_both_endpoints_of_every_supplied_pair ok seen
  unfold readAlternatives at ok
  split at ok
  · rename_i pass
    obtain ⟨main,_⟩ := Bool.and_eq_true_iff.mp pass
    obtain ⟨first,every⟩ := Bool.and_eq_true_iff.mp main
    obtain ⟨unique,bisim⟩ := Bool.and_eq_true_iff.mp first
    obtain ⟨labels,coords⟩ := of_decide_eq_true unique
    have exact := (QuotientObservation471.cone_replay_sound ok).1
    refine ⟨labels,coords,(check_bisimulation_exact ..).mp bisim,fun a d h => ends a d h,?_,?_⟩
    · intro a path
      obtain ⟨j,_,same⟩ := QuotientObservation471.cone_pull_path exact path w.site exact.1
      have checked := List.all_eq_true.mp every j (List.mem_finRange _)
      simpa [same] using checked
    · exact QuotientObservation471.a_checked_closed_cone_requires_only_actual_reachable_closure.mp
        ⟨_,w,checked_cone_exact.mpr exact⟩
  · cases ok

theorem fixed_observation_result_has_exact_finite_witness_iff
    {s : OwnState} {pos : Positions n} {rel : List (Fin n × Fin n)} {root : Fin n} (b : Bool) :
    (∃ (m k : Nat) (scope : ConeWire n m) (q : Wire m k),
      readAlternatives s pos rel root scope q = some b) ↔
      GuardedObservationInput s pos rel root ∧
        (b = true ↔ ReturnsUpToEquality (graphOf s pos) root) := by
  constructor
  · rintro ⟨_,_,scope,q,ran⟩
    exact ⟨accepted_observation_yields_all_input_guards ran,
      (ObservationAlternatives473.all_actual_alternatives_have_a_real_bisimilar_source_coordinate ran).1⟩
  · rintro ⟨guard,sign⟩
    exact (checked_alternatives_exact_for_fixed_input_and_both_signs guard b).mpr sign

end Yulang.GeneralDeclarativeI65.I72.LiteralVisits473
