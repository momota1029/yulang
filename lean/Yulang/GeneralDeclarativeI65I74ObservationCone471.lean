import Yulang.GeneralDeclarativeI65I74FiniteObservationQuotient471

namespace Yulang.QuotientObservation471
open CommonRoleRegularGraph
open CommonRoleGraphBisimulation
open FiniteWorklist (Path)

structure ConeWire (n m : Nat) where
  inclusion : Vector (Fin n) m
  graph : Vector (Node m) m
  site : Fin m

def embedded (w : ConeWire n m) (a : Fin m) : Fin n := w.inclusion.get a
def cone (w : ConeWire n m) : Graph m := w.graph.get

/-- A fully observed successor-closed subgraph. Every ordered successor
of a retained node is checked against the old graph, not just a cut's
observed subset. Unknown nodes outside the cone are irrelevant. -/
def ExactCone (g : Graph n) (root : Fin n) (w : ConeWire n m) : Prop :=
  embedded w w.site = root ∧
  (∀ i j, embedded w i = embedded w j → i = j) ∧
  (∀ i, cone w i ≠ .unresolved) ∧
  (∀ i, g (embedded w i) = projectNode (embedded w) (cone w i))

def checkCone (g : Graph n) (root : Fin n) (w : ConeWire n m) : Bool :=
  decide (embedded w w.site = root) &&
  (List.finRange m).all (fun i => (List.finRange m).all fun j =>
    decide (embedded w i ≠ embedded w j ∨ i = j)) &&
  (List.finRange m).all (fun i => decide (cone w i ≠ .unresolved)) &&
  (List.finRange m).all fun i =>
    decide (g (embedded w i) = projectNode (embedded w) (cone w i))

theorem checked_cone_exact {g : Graph n} {root : Fin n} {w : ConeWire n m} :
    checkCone g root w = true ↔ ExactCone g root w := by
  simp only [checkCone,ExactCone,Bool.and_eq_true,List.all_eq_true,List.mem_finRange,
    true_imp_iff,decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨r,injective⟩,closed⟩,adj⟩
    exact ⟨r,fun i j eq => (injective i j).resolve_left (fun nope => nope eq),closed,adj⟩
  · rintro ⟨r,injective,closed,adj⟩
    refine ⟨⟨⟨r,?_⟩,closed⟩,adj⟩
    intro i j
    by_cases same : embedded w i = embedded w j
    · exact .inr (injective _ _ same)
    · exact .inl same

theorem exact_cone_same_all_observations {g : Graph n} {root : Fin n} {w : ConeWire n m}
    (checked : ExactCone g root w) (depth : Nat) (i : Fin m) :
    observe g depth (embedded w i) = observe (cone w) depth i := by
  induction depth generalizing i with
  | zero => rfl
  | succ d ih =>
    cases observed : cone w i <;>
      simp only [observe,checked.2.2.2,observed,projectNode,List.map_map]
    all_goals first
      | rfl
      | congr 1; apply List.map_congr_left; intro x _; exact ih x

theorem cone_same_children {g : Graph n} {root : Fin n} {w : ConeWire n m}
    (checked : ExactCone g root w) (i : Fin m) :
    successors g (embedded w i) = (successors (cone w) i).map (embedded w) := by
  unfold successors
  rw [checked.2.2.2]
  cases cone w i <;> rfl

theorem cone_push_path {g : Graph n} {root : Fin n} {w : ConeWire n m}
    (checked : ExactCone g root w) {i j : Fin m}
    (walk : Path (successors (cone w)) i j) :
    Path (successors g) (embedded w i) (embedded w j) := by
  induction walk with
  | nil => exact .nil _
  | cons first _ tail =>
    refine .cons ?_ tail
    rw [cone_same_children checked]
    exact List.mem_map.mpr ⟨_,first,rfl⟩

theorem cone_pull_path {g : Graph n} {root : Fin n} {w : ConeWire n m}
    (checked : ExactCone g root w) {s t : Fin n}
    (walk : Path (successors g) s t) (i : Fin m) (atStart : embedded w i = s) :
    ∃ j, Path (successors (cone w)) i j ∧ embedded w j = t := by
  induction walk generalizing i with
  | nil => exact ⟨i,.nil _,atStart⟩
  | cons first trail ih =>
    rw [←atStart,cone_same_children checked] at first
    obtain ⟨other,child,ground⟩ := List.mem_map.mp first
    obtain ⟨last,rest,endAt⟩ := ih _ ground
    exact ⟨last,.cons child rest,endAt⟩

theorem cone_cycle_iff_ambient_at_the_actual_site {g : Graph n} {root : Fin n} {w : ConeWire n m}
    (checked : ExactCone g root w) :
    ReturnsUpToEquality (cone w) w.site ↔ ReturnsUpToEquality g root := by
  rw [←checked.1]
  constructor
  · rintro ⟨child,first,last,rest,close⟩
    refine ⟨embedded w child,?_,embedded w last,cone_push_path checked rest,?_⟩
    · rw [cone_same_children checked]
      exact List.mem_map.mpr ⟨_,first,rfl⟩
    · intro depth
      rw [exact_cone_same_all_observations checked,exact_cone_same_all_observations checked]
      exact close depth
  · rintro ⟨child,first,last,rest,close⟩
    rw [cone_same_children checked] at first
    obtain ⟨inside,childHere,ground⟩ := List.mem_map.mp first
    obtain ⟨endpoint,tail,actualEnd⟩ := cone_pull_path checked rest _ ground
    refine ⟨inside,childHere,endpoint,tail,?_⟩
    intro depth
    rw [←exact_cone_same_all_observations checked,←exact_cone_same_all_observations checked,actualEnd]
    exact close depth

def replayCone (g : Graph n) (i : Fin n) (scope : ConeWire n m) (w : Wire m k) : Option Bool :=
  if checkCone g i scope then replay (cone scope) scope.site w else none

theorem cone_replay_sound {g : Graph n} {i : Fin n} {scope : ConeWire n m} {w : Wire m k}
    {b} (ok : replayCone g i scope w = some b) :
    ExactCone g i scope ∧ (b = true ↔ ReturnsUpToEquality g i) := by
  by_cases checked : checkCone g i scope = true
  · have coneExact := checked_cone_exact.mp checked
    have same := cone_cycle_iff_ambient_at_the_actual_site coneExact
    refine ⟨coneExact,?_⟩
    unfold replayCone at ok
    rw [ite_eq_left checked] at ok
    cases b
    · have q := safe_replay_exact.mp ok
      simp [show ¬ReturnsUpToEquality g i from fun actual =>
        q.2 ((quotient_cycle_iff_returns_up_to_equality q.1 _).mpr (same.mpr actual))]
    · have q := positive_replay_exact.mp ok
      simp [same.mp ((quotient_cycle_iff_returns_up_to_equality q.1 _).mp q.2)]
  · simp [replayCone,checked] at ok

end Yulang.QuotientObservation471
namespace Yulang.QuotientObservation471
open CommonRoleRegularGraph
open CommonRoleGraphBisimulation
open FiniteWorklist (Path)

def ReachableClosed (g : Graph n) (root : Fin n) : Prop :=
  ∀ x, Path (successors g) root x → g x ≠ .unresolved

def reachableNames (g : Graph n) (root : Fin n) : List (Fin n) :=
  (List.finRange n).filter fun x => returnsTo g x root

theorem mem_reachable_names {g : Graph n} {root x} :
    x ∈ reachableNames g root ↔ Path (successors g) root x := by
  simp [reachableNames,returns_to_exact]

def coneIndex (g : Graph n) (root x : Fin n)
    (known : Path (successors g) root x) : Fin (reachableNames g root).length :=
  ⟨(reachableNames g root).idxOf x,List.idxOf_lt_length_iff.mpr (mem_reachable_names.mpr known)⟩

theorem cone_index_gets_old_point {g : Graph n} {root x} (known : Path (successors g) root x) :
    (reachableNames g root).get (coneIndex g root x known) = x :=
  List.getElem_idxOf (coneIndex g root x known).isLt

theorem path_at_cone_point {g : Graph n} {root} (a : Fin (reachableNames g root).length) :
    Path (successors g) root ((reachableNames g root).get a) :=
  mem_reachable_names.mp (List.get_mem _ a)

theorem reachable_child {g : Graph n} {root x child}
    (parent : Path (successors g) root x) (next : child ∈ successors g x) :
    Path (successors g) root child :=
  parent.append (.cons next (.nil _))

def insideNode (g : Graph n) (root x : Fin n) (known : Path (successors g) root x) :
    Node (reachableNames g root).length :=
  match hit : g x with
  | .unresolved => .unresolved
  | .scalar tag => .scalar tag
  | .structural tag nodes =>
    .structural tag (nodes.attach.map fun a =>
      coneIndex g root a.val (reachable_child known (by simpa [successors,hit] using a.property)))
  | .nominal tag nodes =>
    .nominal tag (nodes.attach.map fun a =>
      coneIndex g root a.val (reachable_child known (by simpa [successors,hit] using a.property)))

theorem inside_node_commutes {g : Graph n} {root x} (known : Path (successors g) root x) :
    projectNode ((reachableNames g root).get) (insideNode g root x known) = g x := by
  unfold insideNode
  split
  · rename_i h
    rw [h]
    rfl
  · rename_i _ h
    rw [h]
    rfl
  all_goals
    rename_i tag nodes atNode
    apply Eq.trans _ atNode.symm
    simp only [projectNode,List.map_map,Function.comp_def]
    congr 1
    calc
      _ = nodes.attach.map Subtype.val := by
        apply List.map_congr_left
        intro y _
        exact cone_index_gets_old_point _
      _ = nodes := List.attach_map_subtype_val _

def createCone (g : Graph n) (root : Fin n) : ConeWire n (reachableNames g root).length :=
  ⟨Vector.ofFn ((reachableNames g root).get),
    Vector.ofFn fun i => insideNode g root ((reachableNames g root).get i) (path_at_cone_point i),
    coneIndex g root root (.nil _)⟩

theorem created_cone_exact {g : Graph n} {root}
    (known : ReachableClosed g root) : ExactCone g root (createCone g root) := by
  have emb (j : Fin (reachableNames g root).length) :
      embedded (createCone g root) j = (reachableNames g root).get j :=
    Vector.getElem_ofFn j.isLt
  have coneAt (j : Fin (reachableNames g root).length) :
      cone (createCone g root) j =
        insideNode g root ((reachableNames g root).get j) (path_at_cone_point j) :=
    Vector.getElem_ofFn j.isLt
  refine ⟨(emb _).trans (cone_index_gets_old_point (.nil _)),?_,?_,?_⟩
  · intro i j eq
    rw [emb,emb] at eq
    apply Fin.ext
    have nd : (reachableNames g root).Nodup :=
      List.Pairwise.filter _ (List.nodup_finRange n)
    exact (List.Nodup.getElem_inj nd).mp eq
  · intro i
    rw [coneAt]
    have shaped := known _ (path_at_cone_point i)
    intro unknown
    have eq := inside_node_commutes (path_at_cone_point i)
    rw [unknown] at eq
    exact shaped eq.symm
  · intro i
    rw [emb,coneAt,show embedded (createCone g root) = (reachableNames g root).get from funext emb]
    exact (inside_node_commutes (path_at_cone_point i)).symm

theorem a_checked_closed_cone_requires_only_actual_reachable_closure
    {g : Graph n} {root : Fin n} :
    (∃ (m : Nat) (w : ConeWire n m), checkCone g root w = true) ↔ ReachableClosed g root := by
  constructor
  · rintro ⟨_,w,checked⟩ i path
    have valid := checked_cone_exact.mp checked
    obtain ⟨j,_,rfl⟩ := cone_pull_path valid path w.site valid.1
    rw [valid.2.2.2]
    have z := valid.2.2.1 j
    cases eq : cone w j <;> simp_all [projectNode]
  · intro closes
    exact ⟨_,createCone g root,checked_cone_exact.mpr (created_cone_exact closes)⟩

theorem exact_finite_cone_replay_exists {g : Graph n} {root : Fin n}
    (known : ReachableClosed g root) :
    ((∃ (m k : Nat) (w : ConeWire n m) (q : Wire m k), replayCone g root w q = some true) ↔
        ReturnsUpToEquality g root) ∧
    ((∃ (m k : Nat) (w : ConeWire n m) (q : Wire m k), replayCone g root w q = some false) ↔
        ¬ReturnsUpToEquality g root) := by
  let chosen := createCone g root
  have checked : ExactCone g root chosen := created_cone_exact known
  have yes := checked_cone_exact.mpr checked
  have exact := exists_exact_finite_replay checked.2.2.1 chosen.site
  have same := cone_cycle_iff_ambient_at_the_actual_site checked
  constructor
  · constructor
    · rintro ⟨_,_,w,q,z⟩
      exact (cone_replay_sound z).2.mp rfl
    · intro real
      obtain ⟨k,q,reproduced⟩ := exact.1.mpr (same.mpr real)
      exact ⟨_,k,chosen,q,by simp [replayCone,yes,reproduced]⟩
  · constructor
    · rintro ⟨_,_,w,q,z⟩
      exact fun real => Bool.false_ne_true ((cone_replay_sound z).2.mpr real)
    · intro safe
      obtain ⟨k,q,reproduced⟩ := exact.2.mpr (fun real => safe (same.mp real))
      exact ⟨_,k,chosen,q,by simp [replayCone,yes,reproduced]⟩

end Yulang.QuotientObservation471
