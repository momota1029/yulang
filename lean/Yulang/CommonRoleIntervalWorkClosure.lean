import Yulang.CommonRoleWhereSourceAllocation

/-! A finite work domain for the existing interval capture grammar. All accepted
candidate branches are retained as potential work, never conjoined as selected
constraints. Outside scans remain observable. Endpoints are fixed syntax here;
ordinary-state rematerialization and general saturation are not established. -/
namespace Yulang.CommonRoleIntervalWorkClosure
open CommonRoleStablePaterson (Declaration)
open CommonRoleIntervalPaterson (Goal child expand size)
open CommonRoleIntervalCapture (Bindings total)
open CommonRoleIntervalCandidates (Accepts inspect)
open CommonRoleWhereSourceModels (goalSources)
open CommonRoleWhereSourceAllocation (parentTable Included locate)
open CommonRoleSourceIdentity (Table Slot source)
open CommonRoleCanonicalSourceGraph (canonical)

abbrev Checked (registry : List Declaration) : Prop :=
  ∀ declaration ∈ registry, CommonRoleStablePaterson.check declaration = true

def childrenOf (declaration : Declaration) (goal : Goal) : List Goal :=
  match inspect declaration goal with
  | some (some bindings) => expand declaration (total bindings)
  | _ => []

def children (registry : List Declaration) (goal : Goal) : List Goal :=
  registry.flatMap fun declaration => childrenOf declaration goal

/-- A scanner result outside its supported grammar is retained, not rejected. -/
def outside (registry : List Declaration) (goal : Goal) : List Declaration :=
  registry.filter fun declaration => (inspect declaration goal).isNone

inductive Edge (registry : List Declaration) (goal : Goal) : Goal → Prop
  | generated (declaration : Declaration) (bindings : Bindings)
      (requirement : Nat × List CommonRoleCaptureNormalization.Form) :
      declaration ∈ registry → Accepts declaration goal bindings →
      requirement ∈ declaration.requirements →
      Edge registry goal (child requirement (total bindings))

theorem children_exact (registry : List Declaration) (goal target : Goal) :
    target ∈ children registry goal ↔ Edge registry goal target := by
  constructor
  · intro member
    obtain ⟨declaration, present, member⟩ := List.mem_flatMap.mp member
    cases found : inspect declaration goal with
    | none => simp [childrenOf, found] at member
    | some result =>
      cases result with
      | none => simp [childrenOf, found] at member
      | some bindings =>
        have expanded : target ∈ expand declaration (total bindings) := by
          simpa [childrenOf, found] using member
        obtain ⟨requirement, included, rfl⟩ := List.mem_map.mp expanded
        exact .generated declaration bindings requirement present
          ((CommonRoleIntervalCandidates.inspect_accepts_exact ..).mp found) included
  · intro edge
    cases edge with
    | generated declaration bindings requirement present accepted included =>
      apply List.mem_flatMap.mpr
      refine ⟨declaration, present, ?_⟩
      rw [childrenOf, (CommonRoleIntervalCandidates.inspect_accepts_exact ..).mpr accepted]
      exact List.mem_map.mpr ⟨requirement, included, rfl⟩

theorem outside_exact (registry : List Declaration) (goal : Goal) (declaration : Declaration) :
    declaration ∈ outside registry goal ↔
      declaration ∈ registry ∧ inspect declaration goal = none := by
  simp [outside, Option.isNone_iff_eq_none]

theorem edge_decreases (registry : List Declaration) (checked : Checked registry)
    (edge : Edge registry goal target) : size target.arguments < size goal.arguments := by
  cases edge with
  | generated declaration bindings requirement present accepted included =>
      exact CommonRoleIntervalCandidates.accepted_child_decreases declaration
        (checked declaration present) goal bindings accepted requirement included

theorem edge_sources (edge : Edge registry goal target) :
    Included (parentTable goal) (parentTable target) := by
  cases edge with
  | generated declaration bindings requirement _ accepted included =>
      exact CommonRoleWhereSourceModels.accepted_child_sources declaration goal bindings
        accepted requirement included

def closure (registry : List Declaration) (checked : Checked registry) (goal : Goal) : List Goal :=
  goal :: (children registry goal).attach.flatMap fun next => closure registry checked next.val
termination_by size goal.arguments
decreasing_by exact edge_decreases registry checked ((children_exact ..).mp next.property)

inductive Reach (registry : List Declaration) : Goal → Goal → Prop
  | refl : Reach registry goal goal
  | step : Edge registry goal next → Reach registry next target → Reach registry goal target

theorem closure_complete (registry : List Declaration) (checked : Checked registry)
    (reachable : Reach registry goal target) : target ∈ closure registry checked goal := by
  induction reachable with
  | refl => rw [closure]; exact List.mem_cons_self
  | @step goal next target edge _ ih =>
      rw [closure]
      apply List.mem_cons_of_mem
      have member := (children_exact registry goal next).mpr edge
      exact List.mem_flatMap.mpr ⟨⟨next, member⟩, List.mem_attach _ _, ih⟩

theorem closure_sound (registry : List Declaration) (checked : Checked registry)
    (goal target : Goal) (member : target ∈ closure registry checked goal) :
    Reach registry goal target := by
  rw [closure] at member
  rcases List.mem_cons.mp member with same | below
  · subst target; exact .refl
  · obtain ⟨next, _, member⟩ := List.mem_flatMap.mp below
    exact .step ((children_exact ..).mp next.property)
      (closure_sound registry checked next.val target member)
termination_by size goal.arguments
decreasing_by exact edge_decreases registry checked ((children_exact ..).mp next.property)

theorem closure_exact (registry : List Declaration) (checked : Checked registry)
    (goal target : Goal) : target ∈ closure registry checked goal ↔ Reach registry goal target :=
  ⟨closure_sound registry checked goal target, closure_complete registry checked⟩

theorem reach_trans (first : Reach registry goal middle) (last : Reach registry middle target) :
    Reach registry goal target := by
  induction first with
  | refl => exact last
  | step edge _ ih => exact .step edge (ih last)

theorem generated_closed (registry : List Declaration) (checked : Checked registry)
    (root goal target : Goal) (member : goal ∈ closure registry checked root)
    (edge : Edge registry goal target) : target ∈ closure registry checked root :=
  closure_complete registry checked (reach_trans (closure_sound registry checked root goal member)
    (.step edge .refl))

/-- Original ambient source names survive every actual recursive edge. -/
theorem reach_sources (reachable : Reach registry goal target) :
    Included (parentTable goal) (parentTable target) := by
  induction reachable with
  | refl => exact fun _ member => member
  | step edge _ ih => exact fun name member => edge_sources edge name (ih name member)

/-- All endpoint occurrences, with order and multiplicity retained. -/
def domain (registry : List Declaration) (checked : Checked registry) (root : Goal) : Table :=
  (closure registry checked root).flatMap parentTable

theorem domain_included (registry : List Declaration) (checked : Checked registry) (root : Goal) :
    Included (parentTable root) (domain registry checked root) := by
  intro name member
  obtain ⟨goal, present, used⟩ := List.mem_flatMap.mp member
  exact reach_sources (closure_sound registry checked root goal present) name used

/-- The complete computed recursive domain has canonical owners in the original
root, even with inconsistent endpoints or multiple potential candidates. -/
theorem domain_owners (registry : List Declaration) (checked : Checked registry) (root : Goal) :
    ∃ owners : List (Slot (parentTable root)),
      locate (parentTable root) (domain registry checked root) = some owners ∧
      owners.map (source (parentTable root)) = domain registry checked root ∧
      ∀ owner ∈ owners, canonical (parentTable root) owner = owner := by
  obtain ⟨owners, found⟩ := (CommonRoleWhereSourceAllocation.locate_exact ..).mpr
    (domain_included registry checked root)
  exact ⟨owners, found, CommonRoleWhereSourceAllocation.locate_sources _ _ _ found,
    CommonRoleWhereSourceAllocation.locate_canonical _ _ _ found⟩

/-- Connect the real candidate preparation entry, including its computed state
and finite allocation payload, to the recursively computed work domain. -/
theorem prepared_child_closed (registry : List Declaration) (checked : Checked registry)
    (root goal : Goal) (member : goal ∈ closure registry checked root)
    (declaration : Declaration) (present : declaration ∈ registry)
    (slots : Nat → α) (old : List (CommonRoleSourceIntervalBatches.Demand α))
    (bindingSource : Nat → Nat) (result : CommonRoleWhereSourceAllocation.Prepared α goal)
    (returned : CommonRoleWhereSourceAllocation.prepare slots old declaration goal bindingSource =
      some (some result)) (target : Goal) (generated : target ∈ result.candidate.children) :
    target ∈ closure registry checked root := by
  have original := ((CommonRoleWhereSourceAllocation.prepare_exact ..).mp returned).1
  cases found : inspect declaration goal with
  | none => simp [CommonRoleWhereSourceModels.run, found] at original
  | some answer =>
    cases answer with
    | none => simp [CommonRoleWhereSourceModels.run, found] at original
    | some bindings =>
      have same : result.candidate =
          ⟨bindings, CommonRoleWhereSourceModels.generatedState slots old declaration goal bindingSource bindings,
            expand declaration (total bindings)⟩ := by
        simpa [CommonRoleWhereSourceModels.run, found] using original.symm
      rw [same] at generated
      obtain ⟨requirement, included, rfl⟩ := List.mem_map.mp generated
      exact generated_closed registry checked root goal _ member
        (.generated declaration bindings requirement present
          ((CommonRoleIntervalCandidates.inspect_accepts_exact ..).mp found) included)

/-- Unsupported local scans anywhere in the domain remain inspectable. -/
def boundaries (registry : List Declaration) (checked : Checked registry) (root : Goal) :
    List (Goal × Declaration) :=
  (closure registry checked root).flatMap fun goal => (outside registry goal).map (goal, ·)

theorem boundaries_exact (registry : List Declaration) (checked : Checked registry)
    (root goal : Goal) (declaration : Declaration) :
    (goal, declaration) ∈ boundaries registry checked root ↔
      Reach registry root goal ∧ declaration ∈ registry ∧ inspect declaration goal = none := by
  simp only [boundaries, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨found, member, decl, outsideMember, same⟩
    cases same
    exact ⟨(closure_exact ..).mp member, (outside_exact ..).mp outsideMember⟩
  · rintro ⟨reachable, present, unsupported⟩
    exact ⟨goal, (closure_exact ..).mpr reachable, declaration,
      (outside_exact ..).mpr ⟨present, unsupported⟩, rfl⟩

/-- The public entry computes the declaration check; no stopping proof or fuel
is supplied by its caller. Failure means the existing checker rejected a member. -/
def compute (registry : List Declaration) (root : Goal) : Option (List Goal) :=
  if checked : registry.all CommonRoleStablePaterson.check = true then
    some (closure registry (List.all_eq_true.mp checked) root)
  else none

theorem compute_exact (registry : List Declaration) (root : Goal) (goals : List Goal) :
    compute registry root = some goals ↔
      ∃ checked : Checked registry, goals = closure registry checked root := by
  unfold compute
  split
  · rename_i checked
    constructor
    · intro same; exact ⟨List.all_eq_true.mp checked, Option.some.inj same.symm⟩
    · rintro ⟨_, rfl⟩; rfl
  · rename_i notChecked
    constructor
    · intro impossible; cases impossible
    · rintro ⟨checked, _⟩
      exact False.elim (notChecked (List.all_eq_true.mpr checked))

theorem compute_reach_exact (registry : List Declaration) (root target : Goal) :
    (∃ goals, compute registry root = some goals ∧ target ∈ goals) ↔
      Checked registry ∧ Reach registry root target := by
  constructor
  · rintro ⟨goals, returned, member⟩
    obtain ⟨checked, rfl⟩ := (compute_exact ..).mp returned
    exact ⟨checked, (closure_exact ..).mp member⟩
  · rintro ⟨checked, reachable⟩
    exact ⟨closure registry checked root, (compute_exact ..).mpr ⟨checked, rfl⟩,
      (closure_exact ..).mpr reachable⟩

/-- Each occurrence in the complete work domain reuses its computed original
owner. The entire graph snapshot is preserved for arbitrary cyclic graphs. -/
theorem domain_allocation (registry : List Declaration) (checked : Checked registry) (root : Goal) :
    ∃ owners, ∃ found : locate (parentTable root) (domain registry checked root) = some owners,
      ∀ i : Slot (domain registry checked root),
        CommonRoleCanonicalSourceGrowth.newRoot (parentTable root) (domain registry checked root) i =
          CommonRoleSourceIdentity.retain (parentTable root) (domain registry checked root)
            (CommonRoleWhereSourceAllocation.ownerAt _ _ owners found i) ∧
        ∀ (graph : CommonRoleRegularGraph.Graph (parentTable root).length)
          (role : Nat) (visible : List CommonRoleGraphInspection.VisibleHead),
          CommonRoleGraphInspection.inspectSnapshot
            (CommonRoleAllocatedGraph.allocate (parentTable root) (domain registry checked root) graph)
            role (CommonRoleCanonicalSourceGrowth.newRoot (parentTable root)
              (domain registry checked root) i) visible =
          CommonRoleAllocatedGraph.retainSnapshot (parentTable root) (domain registry checked root)
            (CommonRoleGraphInspection.inspectSnapshot graph role
              (CommonRoleWhereSourceAllocation.ownerAt _ _ owners found i) visible) := by
  obtain ⟨owners, found, _, _⟩ := domain_owners registry checked root
  exact ⟨owners, found, fun i => ⟨CommonRoleWhereSourceAllocation.allocated_root _ _ _ found i,
    fun graph role visible => CommonRoleWhereSourceAllocation.allocated_snapshot _ _ _ found i
      graph role visible⟩⟩

/-- Root endpoint names bound the domain, without bounding structural depth or
identifying distinct work goals that happen to use the same source name. -/
theorem domain_name_exact (registry : List Declaration) (checked : Checked registry)
    (root : Goal) (name : Nat) :
    name ∈ domain registry checked root ↔ name ∈ parentTable root := by
  constructor
  · exact domain_included registry checked root name
  · intro member
    exact List.mem_flatMap.mpr ⟨root, closure_complete registry checked .refl, member⟩

/-- Registry order and duplicate records change the traversal list, but not
its exact potential-work set. This is not selected-dictionary equivalence. -/
theorem reach_registry_ext (first last : List Declaration)
    (same : ∀ declaration, declaration ∈ first ↔ declaration ∈ last)
    (reachable : Reach first root goal) : Reach last root goal := by
  induction reachable with
  | refl => exact .refl
  | step edge _ ih =>
    cases edge with
    | generated declaration bindings requirement present accepted included =>
        exact .step (.generated declaration bindings requirement ((same declaration).mp present)
          accepted included) ih

theorem closure_registry_ext (first last : List Declaration)
    (firstChecked : Checked first) (lastChecked : Checked last)
    (same : ∀ declaration, declaration ∈ first ↔ declaration ∈ last) (root goal : Goal) :
    goal ∈ closure first firstChecked root ↔ goal ∈ closure last lastChecked root := by
  rw [closure_exact, closure_exact]
  exact ⟨reach_registry_ext first last same,
    reach_registry_ext last first (fun declaration => (same declaration).symm)⟩

end Yulang.CommonRoleIntervalWorkClosure
