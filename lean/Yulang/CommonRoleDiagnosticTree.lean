import Yulang.CommonRoleStableGlobalModels

/-! Child-preserving diagnostic trees for the finite source fragment. Candidate
lists are evidence, not language classifications. Missing candidates stay visible
as leaves. Identical source occurrences use the existing node carrier. Exactness below is
membership-level, not an ordered or multiplicity-sensitive dictionary equality. -/
namespace Yulang.CommonRoleDiagnosticTree
open CommonRoleSettledSyntax CommonRoleOpenProducer CommonRoleMaterializedDomain
open CommonRoleCorrelatedPaths (Route extend)
open CommonRoleGlobalChoices (Table mask)
open CommonRoleSourceWorklist (Node)
open CommonRoleSettledConstraints (State)
open CommonRoleGuardedEquations (Candidate candidate candidate_exact)
open CommonRoleSourceTemplateClosure (declarationChildren)
open CommonRoleChildTemplates (sourceWeight)
variable (registry : Registry) (root : SourceRequest n)
inductive Tree where
  | node : Route registry root → List Declaration → List Tree → Tree

def Tree.route : Tree registry root → Route registry root
  | .node r _ _ => r

def Tree.candidates : Tree registry root → List Declaration
  | .node _ ds _ => ds

def Tree.children : Tree registry root → List (Tree registry root)
  | .node _ _ cs => cs

variable (table : Table registry root) (observation : State n)
def enabled (r : Route registry root) : List Declaration :=
  registry.declarations.filter fun d =>
    mask registry root table r.1 r.2 d && candidate observation r.2.val d

def Edge (r t : Route registry root) : Prop :=
  ∃ d ∈ registry.declarations, ∃ c : Node registry root,
    (r,d) ∈ table ∧ Candidate observation r.2.val d ∧
    c.val ∈ declarationChildren d r.2.val ∧ t = extend registry root r d c

def build : Nat → Route registry root → Tree registry root
  | 0, r => .node r (enabled registry root table observation r) []
  | k+1, r => .node r (enabled registry root table observation r)
      ((CommonRoleCorrelatedPaths.children registry root (mask registry root table) observation r).map
        (build k))

theorem build_route (fuel : Nat) (r : Route registry root) :
    (build registry root table observation fuel r).route = r := by cases fuel <;> rfl

theorem build_candidates (fuel : Nat) (r : Route registry root) (d : Declaration) :
    d ∈ (build registry root table observation fuel r).candidates ↔
      d ∈ registry.declarations ∧ (r,d) ∈ table ∧ Candidate observation r.2.val d := by
  cases fuel <;> simp [build, Tree.candidates, enabled, Bool.and_eq_true,
    CommonRoleGlobalChoices.mask_exact, candidate_exact]

theorem children_edge (r t : Route registry root) :
    t ∈ CommonRoleCorrelatedPaths.children registry root (mask registry root table) observation r ↔
      Edge registry root table observation r t := by
  rw [CommonRoleCorrelatedPaths.children_exact]
  simp only [Edge, CommonRoleGlobalChoices.mask_exact]

theorem edge_decreases (r t : Route registry root)
    (h : Edge registry root table observation r t) : sourceWeight t.2.val < sourceWeight r.2.val := by
  obtain ⟨d,hd,c,_,hc,hchild,rfl⟩ := h
  exact CommonRoleGuardedCandidates.candidate_decreases registry d hd observation r.2.val c.val
    ((CommonRoleGuardedEquations.candidate_children_exact observation r.2.val c.val d).mpr ⟨hc,hchild⟩)

/-- Independent recursive relation, with no fuel or builder in its statement. -/
inductive Represents : Tree registry root → Prop where
  | node (r : Route registry root) (ds : List Declaration) (cs : List (Tree registry root)) :
      (∀ d, d ∈ ds ↔ d ∈ registry.declarations ∧ (r,d) ∈ table ∧ Candidate observation r.2.val d) →
      (∀ t, (∃ c ∈ cs, c.route = t) ↔ Edge registry root table observation r t) →
      (∀ c ∈ cs, Represents c) → Represents (.node r ds cs)

/-- Internally derived Paterson budget suffices, even for partial tables. -/
theorem build_represents (fuel : Nat) (r : Route registry root)
    (bound : sourceWeight r.2.val ≤ fuel) :
    Represents registry root table observation (build registry root table observation fuel r) := by
  induction fuel generalizing r with
  | zero =>
    apply Represents.node
    · exact build_candidates registry root table observation 0 r
    · intro t
      constructor
      · rintro ⟨c,hc,_⟩; cases hc
      · intro h
        have := edge_decreases registry root table observation r t h
        omega
    · intro c hc; cases hc
  | succ k ih =>
    apply Represents.node
    · exact build_candidates registry root table observation (k+1) r
    · intro t
      simp only [List.mem_map]
      constructor
      · rintro ⟨c,⟨u,hu,rfl⟩,eq⟩
        rw [build_route] at eq
        subst t
        exact (children_edge registry root table observation r u).mp hu
      · intro h
        exact ⟨build registry root table observation k t,
          ⟨t,(children_edge registry root table observation r t).mpr h,rfl⟩,
          build_route registry root table observation k t⟩
    · intro c hc
      obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hc
      apply ih t
      have := edge_decreases registry root table observation r t
        ((children_edge registry root table observation r t).mp ht)
      omega

def diagnose : Tree registry root :=
  build registry root table observation (sourceWeight root) (CommonRoleCorrelatedPaths.start registry root)

theorem diagnose_represents : Represents registry root table observation (diagnose registry root table observation) := by
  apply build_represents
  exact Nat.le_refl _

/-- A route actually occurs in the recursively retained tree. -/
inductive Visit : Tree registry root → Route registry root → Prop where
  | here (t : Tree registry root) : Visit t t.route
  | child {t c : Tree registry root} {r : Route registry root} :
      c ∈ t.children → Visit c r → Visit t r

theorem visit_edge (tree : Tree registry root)
    (rep : Represents registry root table observation tree)
    (r t : Route registry root) (visit : Visit registry root tree r)
    (edge : Edge registry root table observation r t) : Visit registry root tree t := by
  induction visit with
  | here tree =>
    cases rep with
    | node r ds cs _ edges reps =>
      obtain ⟨c,hc,eq⟩ := (edges t).mpr edge
      exact .child hc (eq ▸ Visit.here c)
  | @child tree c r hc hv ih =>
    cases rep with
    | node a ds cs _ _ reps =>
      exact .child hc (ih (reps c hc) edge)

theorem visit_path (tree : Tree registry root)
    (rep : Represents registry root table observation tree)
    (rootPath : CommonRoleCorrelatedPaths.Path registry root (mask registry root table) observation tree.route)
    (r : Route registry root) (visit : Visit registry root tree r) :
    CommonRoleCorrelatedPaths.Path registry root (mask registry root table) observation r := by
  induction visit with
  | here => exact rootPath
  | @child tree c r hc hv ih =>
    cases rep with
    | node a ds cs _ edges reps =>
      have edge := (edges c.route).mp ⟨c,hc,rfl⟩
      obtain ⟨d,hd,u,ht,hcand,hchild,eq⟩ := edge
      apply ih (reps c hc)
      rw [eq]
      exact .step rootPath hd ((CommonRoleGlobalChoices.mask_exact registry root table a d).mpr ht)
        hcand hchild

/-- The tree contains exactly independently derivable routes, with no successful
child prerequisite. Thus unresolved child evidence is not erased. -/
theorem diagnose_visit_exact (r : Route registry root) :
    Visit registry root (diagnose registry root table observation) r ↔
      CommonRoleCorrelatedPaths.Path registry root (mask registry root table) observation r := by
  constructor
  · exact visit_path registry root table observation _ (diagnose_represents ..)
      (by simpa [diagnose, build_route] using
        (CommonRoleCorrelatedPaths.Path.root (registry := registry) (root := root)
          (mask := mask registry root table) (observation := observation))) r
  · intro hp
    induction hp with
    | root =>
      simpa [diagnose, build_route] using
        Visit.here (diagnose registry root table observation)
    | @step r d c hp hd hm hc hchild ih =>
      exact visit_edge registry root table observation _ (diagnose_represents ..) r _ ih
        ⟨d,hd,c,(CommonRoleGlobalChoices.mask_exact registry root table r d).mp hm,hc,hchild,rfl⟩

/-- Every visited route in a valid global certificate has a table choice. This
is certificate totality, not a final language selection. -/
theorem valid_tree_total (valid : CommonRoleGlobalChoices.Valid registry root observation table)
    (r : Route registry root) (visit : Visit registry root (diagnose registry root table observation) r) :
    ∃ d, (r,d) ∈ table :=
  valid.2.2 r ((diagnose_visit_exact registry root table observation r).mp visit)

/-- A missing child choice leaves its source obligation in the tree. The
statement assigns no error or final classification to that incomplete evidence. -/
theorem unresolved_child_retained (r : Route registry root) (d : Declaration)
    (parent : CommonRoleCorrelatedPaths.Path registry root (mask registry root table) observation r)
    (registered : d ∈ registry.declarations) (chosen : (r,d) ∈ table)
    (candidate : Candidate observation r.2.val d) (c : Node registry root)
    (child : c.val ∈ declarationChildren d r.2.val)
    (missing : ¬ ∃ e, (extend registry root r d c,e) ∈ table) :
    Visit registry root (diagnose registry root table observation) (extend registry root r d c) ∧
      ¬ ∃ e, (extend registry root r d c,e) ∈ table := by
  refine ⟨(diagnose_visit_exact registry root table observation _).mpr ?_,missing⟩
  exact .step parent registered ((CommonRoleGlobalChoices.mask_exact registry root table r d).mpr chosen)
    candidate child

/-- At each route in a searched self-output tree there is exactly one table
choice, and every annotation of that choice really resolves. This does not assert
that such a searched tree exists, or that it is a language-selected dictionary. -/
theorem searched_tree_complete
    (env : Roles.AssocEnv) (roles : Roles.RoleDecls) (wf : Roles.WellFormed env.cores)
    (annotations : Route registry root → Declaration → List (CommonRoleAssociatedStateFlow.Request n))
    (seed : State n)
    (found : table ∈ CommonRoleStableGlobalChoices.search registry root env roles wf annotations seed)
    (r : Route registry root)
    (visit : Visit registry root
      (diagnose registry root table (CommonRoleStableGlobalChoices.output registry root env roles wf annotations seed table)) r) :
    ∃ d, (r,d) ∈ table ∧ (∀ e, (r,e) ∈ table → e = d) ∧
      ∀ q ∈ annotations r d, ∃ head, CommonRoleAssociatedStateFlow.Computed env roles wf q head := by
  have st := ((CommonRoleStableGlobalChoices.search_exact registry root env roles wf annotations seed table).mp found).2
  obtain ⟨d,hd⟩ := valid_tree_total registry root table _ st.1 r visit
  refine ⟨d,hd,?_,?_⟩
  · intro e he
    exact st.1.2.1 r e d he hd
  · intro q hq
    exact CommonRoleStableGlobalChoices.resolved registry root env roles wf annotations seed table found r d hd q hq

/-- The associated output models are exactly the seed models satisfying every
chosen annotation indexed by every visited tree route and table choice.
Annotations remain external inputs, not serialized tree payloads. No disconnected
table entry contributes a hidden equation. -/
theorem searched_tree_models
    (env : Roles.AssocEnv) (roles : Roles.RoleDecls) (wf : Roles.WellFormed env.cores)
    (annotations : Route registry root → Declaration → List (CommonRoleAssociatedStateFlow.Request n))
    (seed : State n)
    (found : table ∈ CommonRoleStableGlobalChoices.search registry root env roles wf annotations seed)
    (assignment : Fin n → Core.PresenceGeneration.Comp Common.model) :
    PresenceNormalForm.All Common.model assignment
      (CommonRoleStableGlobalChoices.output registry root env roles wf annotations seed table).atoms ↔
    PresenceNormalForm.All Common.model assignment seed.atoms ∧
      ∀ r, Visit registry root
        (diagnose registry root table
          (CommonRoleStableGlobalChoices.output registry root env roles wf annotations seed table)) r →
        ∀ d, (r,d) ∈ table → ∀ q ∈ annotations r d, ∀ head,
          CommonRoleAssociatedStateFlow.Computed env roles wf q head →
            Common.Equivalent (assignment q.output).1 (.base head) := by
  have st := ((CommonRoleStableGlobalChoices.search_exact registry root env roles wf annotations seed table).mp found).2
  rw [CommonRoleStableGlobalModels.output_models registry root env roles wf annotations seed table st assignment]
  apply and_congr Iff.rfl
  constructor
  · intro h r _ d hd q hq head hh
    exact h r d hd q hq head hh
  · intro h r d hd q hq head hh
    exact h r ((diagnose_visit_exact registry root table _ r).mpr (st.1.1 r d hd).2.1)
      d hd q hq head hh

end Yulang.CommonRoleDiagnosticTree
