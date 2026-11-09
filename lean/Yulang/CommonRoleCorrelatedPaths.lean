import Yulang.CommonRoleGuardedEquations

/-! Full ancestor candidate histories, rather than merged source-node guards.
The supplied mask is history-sensitive. This is metadata exactness for the
int-only capture-bearing source fragment, not language candidate selection.
Histories distinguish candidate ancestry, not duplicate occurrence indices for
identical parent/candidate/child triples. No global sibling consistency is proved. -/
namespace Yulang.CommonRoleCorrelatedPaths
open CommonRoleSettledSyntax CommonRoleOpenProducer CommonRoleMaterializedDomain
open CommonRoleSourceWorklist (Node nodes nodes_complete rootNode)
open CommonRoleSettledConstraints (State)
open CommonRoleGuardedEquations (Candidate candidate candidate_exact candidate_children_exact)
open CommonRoleSourceTemplateClosure (declarationChildren)

variable (registry : Registry) (root : SourceRequest n)

abbrev History := List (Node registry root × Declaration)
abbrev Route := History registry root × Node registry root

def start : Route registry root := ([], rootNode registry root)
def extend (r : Route registry root) (d : Declaration) (c : Node registry root) : Route registry root :=
  ((r.2, d) :: r.1, c)

variable (mask : History registry root → Node registry root → Declaration → Bool)
  (observation : State n)

/-- Every guard is evaluated at its own complete ancestor history. -/
inductive Path : Route registry root → Prop where
  | root : Path (start registry root)
  | step : Path r → d ∈ registry.declarations → mask r.1 r.2 d = true →
      Candidate observation r.2.val d → c.val ∈ declarationChildren d r.2.val →
      Path (extend registry root r d c)

def children (r : Route registry root) : List (Route registry root) :=
  registry.declarations.flatMap fun d =>
    if mask r.1 r.2 d && candidate observation r.2.val d then
      ((nodes registry root).filter fun c => c.val ∈ declarationChildren d r.2.val).map
        (extend registry root r d)
    else []

theorem children_exact (r t : Route registry root) :
    t ∈ children registry root mask observation r ↔
      ∃ d ∈ registry.declarations, ∃ c : Node registry root,
        mask r.1 r.2 d = true ∧ Candidate observation r.2.val d ∧
        c.val ∈ declarationChildren d r.2.val ∧ t = extend registry root r d c := by
  simp only [children, List.mem_flatMap]
  constructor
  · rintro ⟨d, hd, ht⟩
    split at ht
    next h =>
      have hh : mask r.1 r.2 d = true ∧ candidate observation r.2.val d = true := by simpa only [Bool.and_eq_true] using h
      obtain ⟨c, hc, eq⟩ := List.mem_map.mp ht
      exact ⟨d, hd, c, hh.1, (candidate_exact ..).mp hh.2,
        of_decide_eq_true (List.mem_filter.mp hc).2, eq.symm⟩
    next => cases ht
  · rintro ⟨d, hd, c, hm, hh, hc, rfl⟩
    refine ⟨d, hd, ?_⟩
    have hb := (candidate_exact observation r.2.val d).mpr hh
    simp only [hm, hb, Bool.and_self, ↓reduceIte]
    exact List.mem_map.mpr ⟨c, List.mem_filter.mpr ⟨nodes_complete .., by simpa using hc⟩, rfl⟩

/-- Enumeration is structurally recursive in a derived upper bound. -/
def pathsUpTo : Nat → List (Route registry root)
  | 0 => [start registry root]
  | k + 1 => start registry root ::
      (pathsUpTo k).flatMap (children registry root mask observation)

theorem pathsUpTo_exact (fuel : Nat) (r : Route registry root) :
    r ∈ pathsUpTo registry root mask observation fuel ↔
      Path registry root mask observation r ∧ r.1.length ≤ fuel := by
  induction fuel generalizing r with
  | zero =>
    simp only [pathsUpTo, List.mem_singleton]
    constructor
    · rintro rfl; exact ⟨.root, Nat.le_refl 0⟩
    · rintro ⟨h, hl⟩
      cases h with
      | root => rfl
      | step _ _ _ _ _ => simp [extend] at hl
  | succ k ih =>
    simp only [pathsUpTo, List.mem_cons, List.mem_flatMap]
    constructor
    · rintro (rfl | ⟨p, hp, hr⟩)
      · exact ⟨.root, Nat.zero_le _⟩
      · obtain ⟨hpath, hlen⟩ := (ih p).mp hp
        obtain ⟨d, hd, c, hm, hh, hc, rfl⟩ := (children_exact ..).mp hr
        exact ⟨.step hpath hd hm hh hc, Nat.succ_le_succ hlen⟩
    · rintro ⟨h, hl⟩
      cases h with
      | root => exact Or.inl rfl
      | @step p d c hp hd hm hh hc =>
        right
        exact ⟨p, (ih p).mpr ⟨hp, Nat.le_of_succ_le_succ hl⟩,
          (children_exact ..).mpr ⟨d, hd, c, hm, hh, hc, rfl⟩⟩

/-- All path lengths are bounded by the original source measure, derived from
checked declarations. No external fuel, closure, or accessibility hypothesis. -/
theorem path_measure (r : Route registry root) (h : Path registry root mask observation r) :
    r.1.length + CommonRoleChildTemplates.sourceWeight r.2.val ≤
      CommonRoleChildTemplates.sourceWeight root := by
  induction h with
  | root => simp [start, CommonRoleSourceWorklist.rootNode]
  | @step r d c _ hd _ hh hc ih =>
    have dec := CommonRoleGuardedCandidates.candidate_decreases registry d hd observation r.2.val c.val
      ((candidate_children_exact observation r.2.val c.val d).mpr ⟨hh, hc⟩)
    simp only [extend, List.length_cons]
    omega

def collect : List (Route registry root) :=
  pathsUpTo registry root mask observation (CommonRoleChildTemplates.sourceWeight root)

/-- Exact collection with the internally computed Paterson bound. -/
theorem collect_exact (r : Route registry root) :
    r ∈ collect registry root mask observation ↔ Path registry root mask observation r := by
  rw [collect, pathsUpTo_exact]
  exact ⟨And.left, fun h => ⟨h, by have := path_measure registry root mask observation r h; omega⟩⟩

/-- A converged source node does not erase or identify its distinct histories. -/
theorem extend_history_injective (r t : Route registry root) (d e : Declaration)
    (c u : Node registry root) (h : extend registry root r d c = extend registry root t e u) :
    r = t ∧ d = e ∧ c = u := by
  simp only [extend, Prod.mk.injEq, List.cons.injEq] at h
  rcases h with ⟨⟨⟨hnode, hdecl⟩, hhist⟩, hchild⟩
  exact ⟨Prod.ext hhist hnode, hdecl, hchild⟩
end Yulang.CommonRoleCorrelatedPaths
