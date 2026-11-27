import Yulang.GeneralDeclarativeI65I74ObservationCone471

namespace Yulang.QuotientObservation471
open CommonRoleRegularGraph
open CommonRoleGraphBisimulation
open FiniteWorklist (Path)

def Across (a : Graph n) (b : Graph m) (left : Fin n) (right : Fin m) : Prop :=
  ∀ d, observe a d left = observe b d right

theorem paired_observations_give_actual_corresponding_child
    {a : Graph n} {b : Graph m} {xs : List (Fin n)} {ys : List (Fin m)}
    (same : ∀ d, xs.map (observe a d) = ys.map (observe b d))
    (x : Fin n) (child : x ∈ xs) : ∃ y ∈ ys, Across a b x y := by
  induction xs generalizing ys with
  | nil => cases child
  | cons head tail ih =>
    cases ys with
    | nil => have impossible := same 0; simp at impossible
    | cons other rest =>
      rcases List.mem_cons.mp child with eq | hit
      · subst x
        exact ⟨other,List.mem_cons_self,fun d => (List.cons.inj (same d)).1⟩
      · obtain ⟨y,there,through⟩ := ih (fun d => (List.cons.inj (same d)).2) hit
        exact ⟨y,List.mem_cons_of_mem _ there,through⟩

theorem across_nodes_keep_their_actual_successor_observations
    {a : Graph n} {b : Graph m} {i : Fin n} {j : Fin m} (same : Across a b i j) :
    ∀ d, (successors a i).map (observe a d) = (successors b j).map (observe b d) := by
  intro depth
  have next := same (depth + 1)
  cases left : a i <;> cases right : b j <;>
    simp [observe,left,right] at next <;> simp_all [successors]

theorem actual_nonempty_return_transfers_across_presentations
    {a : Graph n} {b : Graph m} {i : Fin n} {j : Fin m} (same : Across a b i j) :
    ReturnsUpToEquality a i → ReturnsUpToEquality b j := by
  have walk {x z : Fin n} (p : Path (successors a) x z) :
      ∀ y : Fin m, Across a b x y → ∃ q, Path (successors b) y q ∧ Across a b z q := by
    induction p with
    | nil => intro y eq; exact ⟨y,.nil _,eq⟩
    | cons step _ ih =>
      intro y eq
      obtain ⟨child,found,sameChild⟩ := paired_observations_give_actual_corresponding_child
        (across_nodes_keep_their_actual_successor_observations eq) _ step
      obtain ⟨target,tail,actual⟩ := ih child sameChild
      exact ⟨target,.cons found tail,actual⟩
  rintro ⟨first,one,last,tail,equivalent⟩
  obtain ⟨child,found,sameChild⟩ := paired_observations_give_actual_corresponding_child
    (across_nodes_keep_their_actual_successor_observations same) first one
  obtain ⟨target,path,sameEnd⟩ := walk tail child sameChild
  exact ⟨child,found,target,path,fun d => (sameEnd d).symm.trans ((equivalent d).trans (same d))⟩

theorem quotient_nonempty_return_is_invariant_under_every_equal_regular_presentation
    {a : Graph n} {b : Graph m} {i : Fin n} {j : Fin m} (agree : Across a b i j) :
    ReturnsUpToEquality a i ↔ ReturnsUpToEquality b j :=
  ⟨actual_nonempty_return_transfers_across_presentations agree,
    actual_nonempty_return_transfers_across_presentations (fun d => (agree d).symm)⟩

theorem checked_minimal_replays_agree_at_equal_regular_roots
    {a : Graph n} {b : Graph m} {i : Fin n} {j : Fin m} {p : Wire n k} {q : Wire m l}
    {left right : Bool}
    (agree : Across a b i j) (lOk : replay a i p = some left) (rOk : replay b j q = some right) :
    left = right := by
  have same := quotient_nonempty_return_is_invariant_under_every_equal_regular_presentation agree
  cases left <;> cases right
  · rfl
  · obtain ⟨l,ln⟩ := safe_replay_exact.mp lOk
    obtain ⟨r,ry⟩ := positive_replay_exact.mp rOk
    exact (ln ((quotient_cycle_iff_returns_up_to_equality l _).mpr
      (same.mpr ((quotient_cycle_iff_returns_up_to_equality r _).mp ry)))).elim
  · obtain ⟨l,ly⟩ := positive_replay_exact.mp lOk
    obtain ⟨r,rn⟩ := safe_replay_exact.mp rOk
    exact (rn ((quotient_cycle_iff_returns_up_to_equality r _).mpr
      (same.mp ((quotient_cycle_iff_returns_up_to_equality l _).mp ly)))).elim
  · rfl

end Yulang.QuotientObservation471


namespace Yulang.QuotientObservation471
open CommonRoleRegularGraph
open CommonRoleGraphBisimulation

def pairGraph (left : Graph n) (right : Graph m) : Graph (n + m) :=
  Fin.addCases (fun i => projectNode (Fin.castAdd m) (left i))
    (fun j => projectNode (Fin.natAdd n) (right j))

theorem pair_graph_is_closed (left : Graph n) (right : Graph m)
    (knownL : ∀ i, left i ≠ .unresolved) (knownR : ∀ i, right i ≠ .unresolved) :
    ∀ i, pairGraph left right i ≠ .unresolved := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro p
    simp only [pairGraph,Fin.addCases_left]
    cases here : left p <;> simp_all [projectNode]
  · intro p
    simp only [pairGraph,Fin.addCases_right]
    cases here : right p <;> simp_all [projectNode]

theorem pair_graph_preserves_left_observations (a : Graph n) (b : Graph m) :
    ∀ depth i, observe (pairGraph a b) depth (Fin.castAdd m i) = observe a depth i := by
  intro depth
  induction depth with
  | zero => intro; rfl
  | succ d old =>
    intro i
    cases h : a i <;> simp only [observe,pairGraph,Fin.addCases_left,h,projectNode,List.map_map]
    all_goals first
      | rfl
      | congr 1; apply List.map_congr_left; intro x _; exact old x

theorem pair_graph_preserves_right_observations (a : Graph n) (b : Graph m) :
    ∀ depth i, observe (pairGraph a b) depth (Fin.natAdd n i) = observe b depth i := by
  intro depth
  induction depth with
  | zero => intro; rfl
  | succ d old =>
    intro i
    cases h : b i <;> simp only [observe,pairGraph,Fin.addCases_right,h,projectNode,List.map_map]
    all_goals first
      | rfl
      | congr 1; apply List.map_congr_left; intro x _; exact old x

def checkAcross (a : Graph n) (b : Graph m) (i : Fin n) (j : Fin m) : Bool :=
  bisimilar (pairGraph a b) (Fin.castAdd m i) (Fin.natAdd n j)

theorem finite_across_check_is_exact_for_complete_graphs
    {a : Graph n} {b : Graph m} {i : Fin n} {j : Fin m}
    (left : ∀ i, a i ≠ .unresolved) (right : ∀ i, b i ≠ .unresolved) :
    checkAcross a b i j = true ↔ Across a b i j := by
  unfold checkAcross
  rw [bisimilar_iff_observations _ (pair_graph_is_closed a b left right) ..]
  unfold ObservationallyEqual Across
  simp only [pair_graph_preserves_left_observations,pair_graph_preserves_right_observations]

theorem checked_regular_presentations_give_the_same_quotient_bit
    {a : Graph n} {b : Graph m} {i : Fin n} {j : Fin m} {p : Wire n k} {q : Wire m l}
    {left right : Bool} (lOk : replay a i p = some left) (rOk : replay b j q = some right)
    (finite : checkAcross a b i j = true) : left = right := by
  have closedL : ∀ i, a i ≠ .unresolved := by
    cases left
    · exact (safe_replay_exact.mp lOk).1.1
    · exact (positive_replay_exact.mp lOk).1.1
  have closedR : ∀ i, b i ≠ .unresolved := by
    cases right
    · exact (safe_replay_exact.mp rOk).1.1
    · exact (positive_replay_exact.mp rOk).1.1
  exact checked_minimal_replays_agree_at_equal_regular_roots
    ((finite_across_check_is_exact_for_complete_graphs closedL closedR).mp finite) lOk rOk

end Yulang.QuotientObservation471

namespace Yulang.QuotientObservation471
open CommonRoleRegularGraph

theorem unrelated_unknowns_do_not_block_comparing_exact_closed_cones
    {a : Graph n} {b : Graph m} {i : Fin n} {j : Fin m}
    {w : ConeWire n p} {v : ConeWire m q} {x : Wire p k} {y : Wire q l}
    {left right : Bool}
    (lOk : replayCone a i w x = some left) (rOk : replayCone b j v y = some right) :
    checkAcross (cone w) (cone v) w.site v.site = true ↔ Across a b i j := by
  have l := (cone_replay_sound lOk).1
  have r := (cone_replay_sound rOk).1
  rw [finite_across_check_is_exact_for_complete_graphs l.2.2.1 r.2.2.1]
  have eqLeft := fun d => l.1 ▸ exact_cone_same_all_observations l d w.site
  have eqRight := fun d => r.1 ▸ exact_cone_same_all_observations r d v.site
  constructor
  · intro known d
    exact (eqLeft d).trans ((known d).trans (eqRight d).symm)
  · intro known d
    exact (eqLeft d).symm.trans ((known d).trans (eqRight d))

theorem exact_observation_at_each_real_site_is_independent_of_closed_cone_presentation
    {a : Graph n} {b : Graph m} {i : Fin n} {j : Fin m}
    {w : ConeWire n p} {v : ConeWire m q} {x : Wire p k} {y : Wire q l} {left right : Bool}
    (lOk : replayCone a i w x = some left) (rOk : replayCone b j v y = some right)
    (compare : checkAcross (cone w) (cone v) w.site v.site = true) : left = right := by
  have same := quotient_nonempty_return_is_invariant_under_every_equal_regular_presentation
    ((unrelated_unknowns_do_not_block_comparing_exact_closed_cones lOk rOk).mp compare)
  have l := (cone_replay_sound lOk).2
  have r := (cone_replay_sound rOk).2
  cases left <;> cases right
  · rfl
  · exact (Bool.false_ne_true (l.mpr (same.mpr (r.mp rfl)))).elim
  · exact (Bool.false_ne_true (r.mpr (same.mp (l.mp rfl)))).elim
  · rfl

end Yulang.QuotientObservation471

namespace Yulang.QuotientObservation471
open CommonRoleRegularGraph
open CommonRoleGraphBisimulation

def checkAcrossWitness (a : Graph n) (b : Graph m) (i : Fin n) (j : Fin m)
    (rel : Relation (n+m)) : Bool :=
  decide ((Fin.castAdd m i,Fin.natAdd n j) ∈ rel) && checkBisimulation (pairGraph a b) rel

theorem finite_relation_witness_preserves_the_regular_observation
    {a : Graph n} {b : Graph m} {i : Fin n} {j : Fin m} {rel}
    (checked : checkAcrossWitness a b i j rel = true) : Across a b i j := by
  obtain ⟨present,exact⟩ := Bool.and_eq_true_iff.mp checked
  have known := (check_bisimulation_exact ..).mp exact
  intro depth
  have agree := bisimulation_observations _ _ known depth _ _ (of_decide_eq_true present)
  simpa only [pair_graph_preserves_left_observations,pair_graph_preserves_right_observations] using agree

theorem each_equal_pair_of_closed_presentations_has_a_finite_witness
    {a : Graph n} {b : Graph m} {i : Fin n} {j : Fin m}
    (left : ∀ i, a i ≠ .unresolved) (right : ∀ i, b i ≠ .unresolved) :
    (∃ r, checkAcrossWitness a b i j r = true) ↔ Across a b i j := by
  constructor
  · rintro ⟨_,known⟩
    exact finite_relation_witness_preserves_the_regular_observation known
  · intro same
    have existsFull := (finite_across_check_is_exact_for_complete_graphs left right).mpr same
    change bisimilar (pairGraph a b) (Fin.castAdd m i) (Fin.natAdd n j) = true at existsFull
    obtain ⟨rel,_,inside,valid⟩ := (bisimilar_exact ..).mp existsFull
    exact ⟨rel,Bool.and_eq_true_iff.mpr ⟨decide_eq_true inside,(check_bisimulation_exact ..).mpr valid⟩⟩

end Yulang.QuotientObservation471

namespace Yulang.QuotientObservation471
open CommonRoleRegularGraph (Graph)

theorem exact_cones_with_a_checked_cross_relation_have_the_same_return_bit
    {a : Graph n} {b : Graph m} {i : Fin n} {j : Fin m}
    {w : ConeWire n p} {v : ConeWire m q} {x : Wire p k} {y : Wire q l} {left right : Bool}
    {rel : CommonRoleGraphBisimulation.Relation (p+q)}
    (leftRead : replayCone a i w x = some left) (rightRead : replayCone b j v y = some right)
    (correspondence : checkAcrossWitness (cone w) (cone v) w.site v.site rel = true) :
    left = right := by
  have witness := finite_relation_witness_preserves_the_regular_observation correspondence
  have yes := (finite_across_check_is_exact_for_complete_graphs
    (cone_replay_sound leftRead).1.2.2.1 (cone_replay_sound rightRead).1.2.2.1).mpr witness
  exact exact_observation_at_each_real_site_is_independent_of_closed_cone_presentation leftRead rightRead yes

end Yulang.QuotientObservation471
