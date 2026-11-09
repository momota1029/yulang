import Yulang.CommonRoleAssociatedFeedback
import Yulang.CommonRoleFeedbackTrace

/-! Compute the finite update table and emission adapter from annotations on the
computed source closure. Annotations and fixed receivers remain inputs: this is
not parser lowering or general interval inference, nor full B4 exactness. -/
namespace Yulang.CommonRoleSourceAssociatedAdapter
open CommonRoleMaterializedDomain CommonRoleSourceWorklist
open CommonRoleOpenProducer (Registry)
open CommonRoleSettledConstraints (State)
open CommonRoleAssociatedStateFlow (Request Computed)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)

variable (registry : Registry) (root : SourceRequest n)

def entries (annotations : Node registry root → List (Request n)) :
    List (Node registry root × Request n) :=
  (nodes registry root).flatMap fun q => (annotations q).map fun r => (q, r)

def table (annotations : Node registry root → List (Request n))
    (i : Fin (entries registry root annotations).length) : Request n :=
  ((entries registry root annotations).get i).2

def emit (annotations : Node registry root → List (Request n))
    (q : Node registry root) : List (Fin (entries registry root annotations).length) :=
  (List.finRange _).filter fun i => decide (((entries registry root annotations).get i).1 = q)

/-- Soundness and completeness of enumerating source annotation occurrences. -/
theorem entries_exact (annotations : Node registry root → List (Request n))
    (q : Node registry root) (r : Request n) :
    (q, r) ∈ entries registry root annotations ↔ r ∈ annotations q := by
  simp only [entries, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨p, _, s, hs, hp, hr⟩
    subst p; subst s
    exact hs
  · intro h
    exact ⟨q, nodes_complete .., r, h, rfl, rfl⟩

/-- No separately supplied emit map can introduce a foreign source obligation. -/
theorem emitted_sound (annotations : Node registry root → List (Request n))
    (q : Node registry root) (i : Fin (entries registry root annotations).length)
    (h : i ∈ emit registry root annotations q) :
    table registry root annotations i ∈ annotations q := by
  have eq : ((entries registry root annotations).get i).1 = q := by
    exact of_decide_eq_true (List.mem_filter.mp h).2
  apply (entries_exact registry root annotations q _).mp
  rw [← eq]
  exact (entries registry root annotations).get_mem i

/-- Every annotated request is represented by an emitted finite identifier. -/
theorem emitted_complete (annotations : Node registry root → List (Request n))
    (q : Node registry root) (r : Request n) (h : r ∈ annotations q) :
    ∃ i, i ∈ emit registry root annotations q ∧ table registry root annotations i = r := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp ((entries_exact registry root annotations q r).mpr h)
  refine ⟨i, ?_, ?_⟩
  · apply List.mem_filter.mpr
    exact ⟨List.mem_finRange i, by rw [hi]; simp⟩
  · exact congrArg Prod.snd hi

theorem adapter_exact (annotations : Node registry root → List (Request n))
    (q : Node registry root) (r : Request n) :
    r ∈ annotations q ↔
      ∃ i, i ∈ emit registry root annotations q ∧ table registry root annotations i = r := by
  constructor
  · exact emitted_complete registry root annotations q r
  · rintro ⟨i, hi, rfl⟩
    exact emitted_sound registry root annotations q i hi

variable (env : Roles.AssocEnv) (roles : Roles.RoleDecls) (wf : Roles.WellFormed env.cores)

def finalState (seed : State n) (annotations : Node registry root → List (Request n)) : State n :=
  CommonRoleAssociatedFeedback.finalState env roles wf registry root seed
    (table registry root annotations) (emit registry root annotations)

/-- Real declaration equations for every finally reachable annotated request.
All registry, source, annotation, model, and Computed premises remain explicit. -/
theorem reachable_equation (seed : State n) (annotations : Node registry root → List (Request n))
    (assignment : Fin n → Comp Common.model)
    (models : All Common.model assignment (finalState registry root env roles wf seed annotations).atoms)
    (q : Node registry root)
    (reachable : Reach registry root (finalState registry root env roles wf seed annotations) q)
    (r : Request n) (member : r ∈ annotations q) (head : Inference.Base)
    (computed : Computed env roles wf r head) :
    Common.Equivalent (assignment r.output).1 (.base head) := by
  obtain ⟨i, emitted, hi⟩ := emitted_complete registry root annotations q r member
  subst r
  exact CommonRoleAssociatedFeedback.reachable_equation env roles wf registry root seed
    (table registry root annotations) (emit registry root annotations) assignment models
    q reachable i emitted head computed

theorem bounded (seed : State n) (annotations : Node registry root → List (Request n)) :
    (CommonRoleAssociatedFeedback.collected env roles wf registry root seed
      (table registry root annotations) (emit registry root annotations)).length ≤
      (entries registry root annotations).length :=
  (CommonRoleAssociatedFeedback.collected_bounded ..).2

/-- Every collected request came from an actually reachable annotated source at
some legal earlier state. This deliberately does not assert final reachability. -/
theorem collected_source_origin (seed : State n)
    (annotations : Node registry root → List (Request n))
    (i : Fin (entries registry root annotations).length)
    (member : i ∈ CommonRoleAssociatedFeedback.collected env roles wf registry root seed
      (table registry root annotations) (emit registry root annotations)) :
    ∃ seen q,
      CommonRoleFeedbackTrace.Trace registry root
        (CommonRoleAssociatedFeedback.decode env roles wf seed (table registry root annotations))
        (emit registry root annotations) [] seen ∧
      Reach registry root
        (CommonRoleAssociatedFeedback.decode env roles wf seed (table registry root annotations) seen) q ∧
      table registry root annotations i ∈ annotations q := by
  obtain ⟨seen, q, history, reach, emitted⟩ :=
    CommonRoleFeedbackTrace.collected_origin registry root
      (CommonRoleAssociatedFeedback.decode env roles wf seed (table registry root annotations))
      (emit registry root annotations) i member
  exact ⟨seen, q, history, reach, emitted_sound registry root annotations q i emitted⟩

end Yulang.CommonRoleSourceAssociatedAdapter
