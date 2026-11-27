import Yulang.CommonRoleGraphBisimulation

namespace Yulang.QuotientObservation471
open CommonRoleRegularGraph
open CommonRoleGraphBisimulation

def projectNode (f : Fin n → Fin k) : Node n → Node k
  | .unresolved => .unresolved
  | .scalar tag => .scalar tag
  | .structural tag cs => .structural tag (cs.map f)
  | .nominal tag cs => .nominal tag (cs.map f)

/-- Finite, already observed constructor graphs. A class map is data,
not an inferred type assignment and not an edit to a graph. -/
structure Wire (n k : Nat) where
  classes : Vector (Fin k) n
  quotient : Vector (Node k) k

def classOf (w : Wire n k) (i : Fin n) : Fin k := w.classes.get i
def graphOf (w : Wire n k) : Graph k := w.quotient.get

def ExactPartition (g : Graph n) (w : Wire n k) : Prop :=
  (∀ i, g i ≠ .unresolved) ∧
  (∀ j, ∃ i, classOf w i = j) ∧
  (∀ i, graphOf w (classOf w i) = projectNode (classOf w) (g i)) ∧
  (∀ j l, ObservationallyEqual (graphOf w) j l → j = l)

/-- The small worklist checks after the quotient validation. This
abstract partition validator uses the existing finite relation enumeration
for minimality; it is exact, not a performance claim. -/
def checkPartition (g : Graph n) (w : Wire n k) : Bool :=
  (List.finRange n).all (fun i => decide (g i ≠ .unresolved)) &&
  (List.finRange k).all (fun j => (List.finRange n).any fun i => decide (classOf w i = j)) &&
  (List.finRange n).all (fun i => decide (graphOf w (classOf w i) = projectNode (classOf w) (g i))) &&
  (List.finRange k).all (fun j => (List.finRange k).all fun l =>
    decide (j = l) || !bisimilar (graphOf w) j l)

theorem covered_quotient_is_closed {g : Graph n} {w : Wire n k}
    (closed : ∀ i, g i ≠ .unresolved) (surjective : ∀ j, ∃ i, classOf w i = j)
    (commutes : ∀ i, graphOf w (classOf w i) = projectNode (classOf w) (g i)) :
    ∀ j, graphOf w j ≠ .unresolved := by
  intro j
  obtain ⟨i,rfl⟩ := surjective j
  rw [commutes]
  cases hit : g i <;> simp [projectNode]
  exact closed i hit

theorem partition_check_exact {g : Graph n} {w : Wire n k} :
    checkPartition g w = true ↔ ExactPartition g w := by
  simp only [checkPartition,Bool.and_eq_true,List.all_eq_true,List.any_eq_true,
    List.mem_finRange,true_imp_iff,true_and,decide_eq_true_eq,Bool.or_eq_true,Bool.not_eq_true',
    ExactPartition]
  constructor
  · rintro ⟨⟨⟨closed,covers⟩,map⟩,minimal⟩
    have qc := covered_quotient_is_closed closed covers map
    refine ⟨closed,covers,map,fun j l equivalent => ?_⟩
    rcases minimal j l with same | impossible
    · exact same
    · rw [(bisimilar_iff_observations _ qc ..).mpr equivalent] at impossible
      cases impossible
  · rintro ⟨closed,covers,map,minimal⟩
    have qc := covered_quotient_is_closed closed covers map
    refine ⟨⟨⟨closed,covers⟩,map⟩,fun j l => ?_⟩
    cases hit : bisimilar (graphOf w) j l
    · exact Or.inr rfl
    · exact .inl (minimal _ _ ((bisimilar_iff_observations _ qc ..).mp hit))

theorem projection_preserves_each_observation {g : Graph n} {w : Wire n k}
    (adj : ∀ i, graphOf w (classOf w i) = projectNode (classOf w) (g i)) :
    ∀ d i, observe (graphOf w) d (classOf w i) = observe g d i := by
  intro d
  induction d with
  | zero => intro; rfl
  | succ d ih =>
    intro i
    cases observed : g i <;> simp only [observe,adj,observed,projectNode,List.map_map]
    all_goals first
      | rfl
      | congr 1; apply List.map_congr_left; intro x _; exact ih x

theorem exact_classes_are_regular_observation_equality {g : Graph n} {w : Wire n k}
    (exact : ExactPartition g w) (i j : Fin n) :
    classOf w i = classOf w j ↔ ObservationallyEqual g i j := by
  have facts := projection_preserves_each_observation exact.2.2.1
  constructor
  · intro same d
    rw [←facts d i,←facts d j,same]
  · intro equiv
    exact exact.2.2.2 _ _ (by intro d; rw [facts,facts]; exact equiv d)

/-- A nonempty walk on the point's own class, not just reachability
of a different cyclic class. Nominal arguments are ordinary successors;
nominal declaration bodies are never followed. -/
def onCycle (g : Graph n) (i : Fin n) : Prop :=
  ∃ child ∈ successors g i, FiniteWorklist.Path (successors g) child i

def checkOnCycle (g : Graph n) (i : Fin n) : Bool :=
  (successors g i).any (returnsTo g i)

theorem on_cycle_exact (g : Graph n) (i : Fin n) :
    checkOnCycle g i = true ↔ onCycle g i := by
  simp [checkOnCycle,onCycle,List.any_eq_true,returns_to_exact]

def replay (g : Graph n) (i : Fin n) (w : Wire n k) : Option Bool :=
  if checkPartition g w then some (checkOnCycle (graphOf w) (classOf w i)) else none

theorem positive_replay_exact {g : Graph n} {w : Wire n k} {i : Fin n} :
    replay g i w = some true ↔
    ExactPartition g w ∧ onCycle (graphOf w) (classOf w i) := by
  by_cases valid : checkPartition g w = true
  · simp [replay,valid,partition_check_exact.mp valid,on_cycle_exact]
  · simp [replay,valid,show ¬ ExactPartition g w from fun h => valid (partition_check_exact.mpr h)]

theorem safe_replay_exact {g : Graph n} {w : Wire n k} {i : Fin n} :
    replay g i w = some false ↔
    ExactPartition g w ∧ ¬onCycle (graphOf w) (classOf w i) := by
  by_cases valid : checkPartition g w = true
  · simp [replay,valid,partition_check_exact.mp valid,←on_cycle_exact]
  · simp [replay,valid,show ¬ ExactPartition g w from fun h => valid (partition_check_exact.mpr h)]

end Yulang.QuotientObservation471
namespace Yulang.QuotientObservation471
open CommonRoleRegularGraph
open CommonRoleGraphBisimulation

def chosen (g : Graph n) (i : Fin n) : Fin n :=
  ((List.finRange n).find? (bisimilar g i)).getD i

theorem chosen_equal_observations {g : Graph n}
    (closed : ∀ i, g i ≠ .unresolved) (i : Fin n) :
    ObservationallyEqual g i (chosen g i) := by
  unfold chosen
  cases read : (List.finRange n).find? (bisimilar g i) with
  | none => intro; rfl
  | some v =>
    exact (bisimilar_iff_observations _ closed ..).mp (List.find?_some read)

theorem chosen_eq_of_equal {g : Graph n}
    (closed : ∀ i, g i ≠ .unresolved) {i j : Fin n}
    (same : ObservationallyEqual g i j) : chosen g i = chosen g j := by
  have pred : bisimilar g i = bisimilar g j := by
    funext s
    have iff : bisimilar g i s = true ↔ bisimilar g j s = true := by
      rw [bisimilar_iff_observations _ closed, bisimilar_iff_observations _ closed]
      exact ⟨fun a d => (same d).symm.trans (a d),fun a d => (same d).trans (a d)⟩
    cases hi : bisimilar g i s <;> cases hj : bisimilar g j s <;> simp_all
  have someFind : ∃ v, (List.finRange n).find? (bisimilar g i) = some v := by
    have found := (List.find?_isSome).mpr ⟨i,List.mem_finRange i,
      (bisimilar_iff_observations _ closed ..).mpr (fun _ => rfl)⟩
    cases test : (List.finRange n).find? (bisimilar g i)
    · simp [test] at found
    · exact ⟨_,rfl⟩
  obtain ⟨v,read⟩ := someFind
  have other : (List.finRange n).find? (bisimilar g j) = some v := pred ▸ read
  simp [chosen,read,other]

def representatives (g : Graph n) : List (Fin n) :=
  (List.finRange n).filter fun i => decide (chosen g i = i)

theorem chosen_is_represented {g : Graph n} (closed : ∀ i, g i ≠ .unresolved)
    (i : Fin n) : chosen g i ∈ representatives g := by
  simpa [representatives] using (chosen_eq_of_equal closed (chosen_equal_observations closed i)).symm

def quotientIndex (g : Graph n) (closed : ∀ i, g i ≠ .unresolved) (i : Fin n) :
    Fin (representatives g).length :=
  ⟨(representatives g).idxOf (chosen g i),List.idxOf_lt_length_iff.mpr (chosen_is_represented closed i)⟩

theorem at_index_is_chosen {g : Graph n} (closed : ∀ i, g i ≠ .unresolved) (i : Fin n) :
    (representatives g).get (quotientIndex g closed i) = chosen g i := by
  exact List.getElem_idxOf (quotientIndex g closed i).isLt

theorem representatives_nodup (g : Graph n) : (representatives g).Nodup :=
  List.Pairwise.filter _ (List.nodup_finRange n)

theorem representative_get_is_fixed (g : Graph n) (j : Fin (representatives g).length) :
    chosen g ((representatives g).get j) = (representatives g).get j := by
  have recorded := List.get_mem (representatives g) j
  simpa [representatives] using recorded

theorem index_of_representative {g : Graph n} (closed : ∀ i, g i ≠ .unresolved)
    (j : Fin (representatives g).length) :
    quotientIndex g closed ((representatives g).get j) = j := by
  apply Fin.ext
  apply (List.Nodup.getElem_inj (representatives_nodup g)).mp
  change (representatives g).get (quotientIndex g closed ((representatives g).get j)) =
    (representatives g).get j
  rw [at_index_is_chosen,representative_get_is_fixed]

theorem index_same_of_observations {g : Graph n} (closed : ∀ i, g i ≠ .unresolved)
    {i j : Fin n} (eq : ObservationallyEqual g i j) :
    quotientIndex g closed i = quotientIndex g closed j := by
  apply Fin.ext
  exact congrArg ((representatives g).idxOf) (chosen_eq_of_equal closed eq)

theorem mapping_equal_observations_at_one_step {g : Graph n} {f : Fin n → Fin k}
    (closed : ∀ i, g i ≠ .unresolved)
    (maps : ∀ a b, ObservationallyEqual g a b → f a = f b)
    {i j : Fin n} (eq : ObservationallyEqual g i j) :
    projectNode f (g i) = projectNode f (g j) := by
  obtain ⟨relation,_,member,stable⟩ := observations_bisimilar _ closed _ _ eq
  have used := stable (i,j) member
  have children {xs ys} (connected : childrenRelated relation xs ys) : xs.map f = ys.map f := by
    induction xs generalizing ys with
    | nil => cases ys <;> simp_all [childrenRelated]
    | cons first rest ih =>
      cases ys with
      | nil => exact False.elim connected
      | cons last tail =>
        have a := maps _ _ (fun d => bisimulation_observations _ _ stable d _ _ connected.1)
        have b := ih connected.2
        simp only [List.map_cons,a,b]
  change nodeRelated relation (i,j).1 (i,j).2 (g i) (g j) at used
  cases lhs : g i <;> cases rhs : g j <;> simp only [lhs,rhs,nodeRelated] at used
  all_goals try exact False.elim used
  all_goals try exact False.elim (closed i lhs)
  case scalar.scalar => simpa [projectNode] using used
  case structural.structural => simp [projectNode,used.1,children used.2]
  case nominal.nominal => simp [projectNode,used.1,children used.2]

def constructPartition (g : Graph n) (closed : ∀ i, g i ≠ .unresolved) :
    Wire n (representatives g).length :=
  ⟨Vector.ofFn (quotientIndex g closed),
    Vector.ofFn fun i => projectNode (quotientIndex g closed) (g ((representatives g).get i))⟩

theorem every_complete_graph_has_a_finite_partition {g : Graph n}
    (closed : ∀ i, g i ≠ .unresolved) :
    ExactPartition g (constructPartition g closed) := by
  have indices (i : Fin n) :
      classOf (constructPartition g closed) i = quotientIndex g closed i := by
    exact Vector.getElem_ofFn i.isLt
  have commutes (i : Fin n) :
      graphOf (constructPartition g closed) (classOf (constructPartition g closed) i) =
        projectNode (classOf (constructPartition g closed)) (g i) := by
    rw [indices]
    have eqfun : classOf (constructPartition g closed) = quotientIndex g closed := funext indices
    rw [eqfun]
    change (Vector.ofFn (fun j => projectNode (quotientIndex g closed) (g ((representatives g).get j))))[(quotientIndex g closed i).val] = _
    rw [Vector.getElem_ofFn]
    change projectNode (quotientIndex g closed) (g ((representatives g).get (quotientIndex g closed i))) = _
    rw [at_index_is_chosen]
    exact (mapping_equal_observations_at_one_step closed (fun _ _ => index_same_of_observations closed)
      (chosen_equal_observations closed i)).symm
  refine ⟨closed,fun j => ⟨(representatives g).get j,(indices _).trans (index_of_representative closed j)⟩,
    commutes,fun j l same => ?_⟩
  have resulting : ObservationallyEqual g ((representatives g).get j) ((representatives g).get l) := by
    intro depth
    have eval := projection_preserves_each_observation commutes depth
    rw [←eval,←eval,indices,indices,index_of_representative,index_of_representative]
    exact same depth
  exact (index_of_representative closed j).symm.trans
    ((index_same_of_observations closed resulting).trans (index_of_representative closed l))

end Yulang.QuotientObservation471
namespace Yulang.QuotientObservation471
open CommonRoleRegularGraph
open CommonRoleGraphBisimulation
open FiniteWorklist (Path)

theorem successors_after_minimization {g : Graph n} {w : Wire n k}
    (adj : ∀ i, graphOf w (classOf w i) = projectNode (classOf w) (g i))
    (i : Fin n) :
    successors (graphOf w) (classOf w i) = (successors g i).map (classOf w) := by
  unfold successors
  rw [adj]
  cases g i <;> rfl

theorem forward_path {g : Graph n} {w : Wire n k}
    (adj : ∀ i, graphOf w (classOf w i) = projectNode (classOf w) (g i))
    {i j : Fin n} (trail : Path (successors g) i j) :
    Path (successors (graphOf w)) (classOf w i) (classOf w j) := by
  induction trail with
  | nil _ => exact .nil _
  | cons step _ later =>
    refine .cons ?_ later
    rw [successors_after_minimization adj]
    exact List.mem_map.mpr ⟨_,step,rfl⟩

theorem pull_path {g : Graph n} {w : Wire n k}
    (adj : ∀ i, graphOf w (classOf w i) = projectNode (classOf w) (g i))
    {start finish : Fin k} (trail : Path (successors (graphOf w)) start finish)
    (i : Fin n) (origin : classOf w i = start) :
    ∃ j, Path (successors g) i j ∧ classOf w j = finish := by
  induction trail generalizing i with
  | nil here => exact ⟨i,.nil _,origin⟩
  | @cons mid source finish step later ih =>
    rw [←origin,successors_after_minimization adj] at step
    obtain ⟨j,visited,atMid⟩ := List.mem_map.mp step
    obtain ⟨t,tail,atEnd⟩ := ih _ atMid
    exact ⟨t,.cons visited tail,atEnd⟩

/-- Independent of any proposed quotient: a genuinely nonempty walk
ends at a point whose entire regular observation equals the start. -/
def ReturnsUpToEquality (g : Graph n) (i : Fin n) : Prop :=
  ∃ child ∈ successors g i,
    ∃ endpoint, Path (successors g) child endpoint ∧ ObservationallyEqual g endpoint i

theorem quotient_cycle_iff_returns_up_to_equality {g : Graph n} {w : Wire n k}
    (partition : ExactPartition g w) (i : Fin n) :
    onCycle (graphOf w) (classOf w i) ↔ ReturnsUpToEquality g i := by
  have adj := partition.2.2.1
  constructor
  · rintro ⟨next,edge,walk⟩
    rw [successors_after_minimization adj] at edge
    obtain ⟨child,seen,rfl⟩ := List.mem_map.mp edge
    obtain ⟨terminal,tail,ending⟩ := pull_path adj walk child rfl
    exact ⟨child,seen,terminal,tail,(exact_classes_are_regular_observation_equality partition ..).mp ending⟩
  · rintro ⟨child,seen,terminal,tail,ending⟩
    have close := (exact_classes_are_regular_observation_equality partition ..).mpr ending
    refine ⟨classOf w child,?_,close ▸ forward_path adj tail⟩
    rw [successors_after_minimization adj]
    exact List.mem_map.mpr ⟨child,seen,rfl⟩

theorem exists_exact_finite_replay {g : Graph n} (closed : ∀ i, g i ≠ .unresolved) (i : Fin n) :
    ((∃ (k : Nat) (w : Wire n k), replay g i w = some true) ↔ ReturnsUpToEquality g i) ∧
    ((∃ (k : Nat) (w : Wire n k), replay g i w = some false) ↔ ¬ ReturnsUpToEquality g i) := by
  have good := every_complete_graph_has_a_finite_partition closed
  have same := quotient_cycle_iff_returns_up_to_equality good i
  constructor
  · constructor
    · rintro ⟨_,w,h⟩
      obtain ⟨q,cycle⟩ := positive_replay_exact.mp h
      exact (quotient_cycle_iff_returns_up_to_equality q i).mp cycle
    · intro semantic
      exact ⟨_,constructPartition g closed,positive_replay_exact.mpr ⟨good,same.mpr semantic⟩⟩
  · constructor
    · rintro ⟨_,w,h⟩
      obtain ⟨q,safe⟩ := safe_replay_exact.mp h
      exact fun next => safe ((quotient_cycle_iff_returns_up_to_equality q i).mpr next)
    · intro escaping
      exact ⟨_,constructPartition g closed,safe_replay_exact.mpr ⟨good,fun bad => escaping (same.mp bad)⟩⟩

end Yulang.QuotientObservation471
