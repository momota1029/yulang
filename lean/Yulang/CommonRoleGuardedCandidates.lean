import Yulang.CommonRoleSourceAssociatedAdapter
import Yulang.CommonRoleAssociatedDeclarationExact

/-! Candidate-preserving guarded metadata, not language candidate selection.
An explicit branch mask and observation state are inputs. Enabling incompatible
branches does not establish language typing. No feedback convergence, existence,
or B4 exactness is claimed. Int-only capture-bearing source fragment only. -/
namespace Yulang.CommonRoleGuardedCandidates
open CommonRoleSettledSyntax CommonRoleOpenProducer CommonRoleCaptureOrigin
open CommonRoleMaterializedDomain CommonRoleChildTemplates CommonRoleSourceTemplateClosure
open CommonRoleSourceWorklist (Node nodes nodes_complete rootNode)
open CommonRoleSettledConstraints (State)

/-- Each candidate is tested alone; an earlier competing hit cannot erase it. -/
def candidateNext (d : Declaration) (s : State n) (p : SourceRequest n) : List (SourceRequest n) :=
  match production [d] (p.eval s) with
  | none => []
  | some (chosen, _, _) => declarationChildren chosen p

def singleton (registry : Registry) (d : Declaration) (hd : d ∈ registry.declarations) : Registry :=
  ⟨[d], by intro x hx; simp only [List.mem_singleton] at hx; subst x; exact registry.checked d hd,
    by simp⟩

/-- Candidate edges have the same checked Paterson descent as first-hit edges. -/
theorem candidate_decreases (registry : Registry) (d : Declaration)
    (hd : d ∈ registry.declarations) (s : State n) (p c : SourceRequest n)
    (h : c ∈ candidateNext d s p) : sourceWeight c < sourceWeight p := by
  exact generated_decreases (singleton registry d hd) c p
    (CommonRoleSourceWorklist.actual_next_generated (singleton registry d hd) s p c h)

theorem candidate_in_structural (registry : Registry) (d : Declaration)
    (hd : d ∈ registry.declarations) (s : State n) (p c : SourceRequest n)
    (h : c ∈ candidateNext d s p) : c ∈ next registry p := by
  have dec := candidate_decreases registry d hd s p c h
  have sg := CommonRoleSourceWorklist.actual_next_generated (singleton registry d hd) s p c h
  have hs := generated_present (singleton registry d hd) c p sg
  have mem := (List.mem_filter.mp hs).1
  have cm : c ∈ declarationChildren d p := by simpa [next, singleton] using mem
  exact List.mem_filter.mpr ⟨List.mem_flatMap.mpr ⟨d, hd, cm⟩, by simpa using dec⟩

variable (registry : Registry) (root : SourceRequest n)
  (mask : SourceRequest n → Declaration → Bool) (s : State n)

def nextCandidates (p : SourceRequest n) : List (SourceRequest n) :=
  registry.declarations.flatMap fun d => if mask p d then candidateNext d s p else []

/-- Independent edge with explicit candidate identity and branch guard. -/
def Edge (p c : SourceRequest n) : Prop :=
  ∃ d ∈ registry.declarations, mask p d = true ∧ c ∈ candidateNext d s p

theorem next_exact (p c : SourceRequest n) :
    c ∈ nextCandidates registry mask s p ↔ Edge registry mask s p c := by
  simp only [nextCandidates, List.mem_flatMap, Edge]
  constructor
  · rintro ⟨d, hd, hc⟩
    split at hc
    · exact ⟨d, hd, by assumption, hc⟩
    · cases hc
  · rintro ⟨d, hd, hm, hc⟩
    exact ⟨d, hd, by simpa [hm] using hc⟩

theorem edge_closed (p : Node registry root) (c : SourceRequest n)
    (h : Edge registry mask s p.val c) : c ∈ closure registry root := by
  obtain ⟨d, hd, _, hc⟩ := h
  exact closure_complete registry root c (reach_trans registry root p.val c
    (closure_sound registry root p.val p.property)
    (.step (candidate_in_structural registry d hd s p.val c hc) .refl))

inductive Reach : Node registry root → Prop where
  | root : Reach (rootNode registry root)
  | step : Reach parent → Edge registry mask s parent.val child.val → Reach child

def rules : List (FiniteHorn.Rule (Node registry root)) :=
  ⟨[], rootNode registry root⟩ :: (nodes registry root).flatMap fun p =>
    ((nodes registry root).filter fun c => c.val ∈ nextCandidates registry mask s p.val).map
      (CommonRoleSourceWorklist.edgeRule p)

def collect : List (Node registry root) :=
  FiniteHorn.saturate (rules registry root mask s) (nodes registry root)

theorem rule_present (p c : Node registry root) (h : Edge registry mask s p.val c.val) :
    CommonRoleSourceWorklist.edgeRule p c ∈ rules registry root mask s := by
  apply List.mem_cons_of_mem
  apply List.mem_flatMap.mpr
  refine ⟨p, nodes_complete .., List.mem_map.mpr ⟨c, ?_, rfl⟩⟩
  exact List.mem_filter.mpr ⟨nodes_complete .., by simpa using (next_exact registry mask s p.val c.val).mpr h⟩

theorem derives_sound (q : Node registry root)
    (h : FiniteHorn.Derives (rules registry root mask s) q) : Reach registry root mask s q := by
  apply h.sound
  intro rule member premises
  rcases List.mem_cons.mp member with rfl | member
  · exact .root
  · obtain ⟨p, _, member⟩ := List.mem_flatMap.mp member
    obtain ⟨c, filtered, rfl⟩ := List.mem_map.mp member
    have edge : c.val ∈ nextCandidates registry mask s p.val := by
      simpa using (List.mem_filter.mp filtered).2
    exact .step (premises p (by simp [CommonRoleSourceWorklist.edgeRule]))
      ((next_exact registry mask s p.val c.val).mp edge)

theorem derives_complete (q : Node registry root) (h : Reach registry root mask s q) :
    FiniteHorn.Derives (rules registry root mask s) q := by
  induction h with
  | root => exact .applyRule _ List.mem_cons_self (by simp)
  | @step p c _ edge ih =>
    apply FiniteHorn.Derives.applyRule (CommonRoleSourceWorklist.edgeRule p c)
      (rule_present registry root mask s p c edge)
    simpa [CommonRoleSourceWorklist.edgeRule] using ih

/-- Exact all-enabled-candidate source closure; no closure/fuel premise supplied. -/
theorem collect_exact (q : Node registry root) :
    q ∈ collect registry root mask s ↔ Reach registry root mask s q := by
  rw [collect, FiniteHorn.saturate_exact _ _ (nodes_complete registry root)]
  exact ⟨derives_sound registry root mask s q, derives_complete registry root mask s q⟩

theorem collect_capacity :
    (collect registry root mask s).length ≤ (closure registry root).length := by
  simpa [collect, nodes] using FiniteHorn.saturate_length_le (rules registry root mask s)
    (nodes registry root) (nodes_complete registry root)

/-- All enabled candidates' children are visited, even if an earlier declaration
also matches. This does not commit candidate-specific equations globally. -/
theorem candidate_child_collected (p : Node registry root)
    (hp : p ∈ collect registry root mask s) (d : Declaration)
    (hd : d ∈ registry.declarations) (hm : mask p.val d = true)
    (c : SourceRequest n) (hc : c ∈ candidateNext d s p.val) :
    ∃ q ∈ collect registry root mask s, q.val = c := by
  let q : Node registry root := ⟨c, edge_closed registry root mask s p c ⟨d, hd, hm, hc⟩⟩
  exact ⟨q, (collect_exact registry root mask s q).mpr
    (.step ((collect_exact registry root mask s p).mp hp) ⟨d, hd, hm, hc⟩), rfl⟩
end Yulang.CommonRoleGuardedCandidates
