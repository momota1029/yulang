import Yulang.CommonRoleRegisteredCaptureSources

/-! Structural occurrence addresses for arbitrary finite capture traces.
Roots remain explicit source-occurrence inputs; this does not prove a parser
boundary, reachability of arbitrary visits, associated feedback or saturation.
The entire finite trace is compiled before execution, not discovered online. -/
namespace Yulang.CommonRoleAddressedCaptureModels
open CommonRoleStablePaterson (Declaration)
open CommonRoleIntervalPaterson (Goal Substitution)
open CommonRoleIntervalCapture (Bindings)
open CommonRoleIntervalCandidates (Accepts)
open CommonRoleSourceIntervalBatches (Demand Models)
open CommonRoleCaptureBatchModels (HeadFits)
open CommonRoleWhereSourceModels (WhereFits)
open Core.PresenceGeneration (Comp)

/-- Original where positions distinguish even syntactically equal sibling goals.
Full declarations prevent accidental sharing from reused numeric labels. -/
structure Address where
  root : Nat
  path : List (Declaration × Nat)
  deriving DecidableEq, Repr

structure Invocation where
  address : Address
  declaration : Declaration
  deriving DecidableEq, Repr

def childAddress (parent : Invocation) (position : Nat) : Address :=
  ⟨parent.address.root, parent.address.path ++ [(parent.declaration, position)]⟩

/-- Endpoint substitution affects only the goal, never the structural address. -/
def children (parent : Invocation) (binding : Substitution) : List (Address × Goal) :=
  (CommonRoleIntervalPaterson.expand parent.declaration binding).zipIdx.map
    fun (goal, index) => (childAddress parent index, goal)

theorem children_goals (parent : Invocation) (binding : Substitution) :
    (children parent binding).map Prod.snd =
      CommonRoleIntervalPaterson.expand parent.declaration binding := by
  simpa only [children, List.map_map, Function.comp_def] using
    (List.zipIdx_map_fst 0 (CommonRoleIntervalPaterson.expand parent.declaration binding))

theorem child_address_exact (parent other : Invocation) (first last : Nat) :
    childAddress parent first = childAddress other last ↔ parent = other ∧ first = last := by
  cases parent with
  | mk p d =>
    cases other with
    | mk q e =>
      cases p with
      | mk r ps =>
        cases q with
        | mk s qs => simp [childAddress, and_assoc]

/-- Rebuilding a parent with any new endpoint substitution preserves every
original child address, in order and with multiplicity. -/
theorem children_addresses (parent : Invocation) (binding : Substitution) :
    (children parent binding).map Prod.fst =
      (List.range' 0 parent.declaration.requirements.length).map (childAddress parent) := by
  calc
    _ = ((CommonRoleIntervalPaterson.expand parent.declaration binding).zipIdx.map
        Prod.snd).map (childAddress parent) := by
      simp only [children, List.map_map, Function.comp_def]
    _ = _ := by rw [List.zipIdx_map_snd]; simp [CommonRoleIntervalPaterson.expand]

theorem children_regenerate (parent : Invocation) (first last : Substitution) :
    (children parent first).map Prod.fst = (children parent last).map Prod.fst := by
  rw [children_addresses, children_addresses]

/-- Every actual indexed child retains its position and its full original goal. -/
theorem children_at (parent : Invocation) (binding : Substitution) (index : Nat)
    (bound : index < parent.declaration.requirements.length) :
    (children parent binding)[index]? = some (childAddress parent index,
      CommonRoleIntervalPaterson.child parent.declaration.requirements[index] binding) := by
  simp [children, CommonRoleIntervalPaterson.expand, bound]

structure Visit where
  invocation : Invocation
  goal : Goal
  deriving DecidableEq, Repr

abbrev Table := List Invocation

def table (visits : List Visit) : Table := visits.map Visit.invocation

def compile (names : Table) (visit : Visit) : CommonRoleRegisteredCaptureSources.Visit :=
  ⟨names.idxOf visit.invocation, visit.invocation.declaration, visit.goal⟩

def follow (slots : Nat → α) (old : List (Demand α)) (visits : List Visit) :
    Option (CommonRoleRegisteredCaptureSources.State α) :=
  CommonRoleRegisteredCaptureSources.follow slots (CommonRoleRegisteredCaptureSources.start old) (visits.map (compile (table visits)))

/-- Numeric invocation identity is computed, not supplied by the caller. -/
theorem index_exact (names : Table) (first last : Invocation)
    (hf : first ∈ names) (hl : last ∈ names) :
    names.idxOf first = names.idxOf last ↔ first = last := by
  constructor
  · intro equal
    have a := List.getElem_idxOf (List.idxOf_lt_length_of_mem hf)
    have b := List.getElem_idxOf (List.idxOf_lt_length_of_mem hl)
    have same : names[names.idxOf first]'(List.idxOf_lt_length_of_mem hf) =
        names[names.idxOf last]'(List.idxOf_lt_length_of_mem hl) := by simp [equal]
    exact a.symm.trans (same.trans b)
  · rintro rfl; rfl

/-- Later visits cannot renumber an earlier invocation, including recaptures. -/
theorem compile_append (earlier later : List Visit) (visit : Visit)
    (member : visit ∈ earlier) :
    compile (table (earlier ++ later)) visit = compile (table earlier) visit := by
  have present : visit.invocation ∈ table earlier := List.mem_map.mpr ⟨visit, member, rfl⟩
  have names : table (earlier ++ later) = table earlier ++ table later := by simp [table]
  simp only [compile, names, List.idxOf_append, present, ite_true]

/-- All finite invocation indices are in the computed table, with no bound
supplied by the caller. -/
theorem compile_bounded (visits : List Visit) (visit : Visit) (member : visit ∈ visits) :
    (compile (table visits) visit).invocation < visits.length := by
  have bound := List.idxOf_lt_length_of_mem (List.mem_map.mpr ⟨visit, member, rfl⟩ :
    visit.invocation ∈ table visits)
  simpa [compile, table] using bound

theorem compiled_identity (visits : List Visit) (first last : Visit)
    (hf : first ∈ visits) (hl : last ∈ visits) :
    (compile (table visits) first).invocation = (compile (table visits) last).invocation ↔
      first.invocation = last.invocation :=
  index_exact _ _ _ (List.mem_map.mpr ⟨first, hf, rfl⟩) (List.mem_map.mpr ⟨last, hl, rfl⟩)

/-- A successful actual registered capture emits every original where child
with its structural address. Adding provenance creates no new failure. -/
def step (slots : Nat → α) (names : Table) (state : CommonRoleRegisteredCaptureSources.State α)
    (visit : Visit) : Option (Option (CommonRoleRegisteredCaptureSources.Result α × List (Address × Goal))) := do
  let answer ← CommonRoleRegisteredCaptureSources.run slots state
    (compile names visit).invocation visit.invocation.declaration visit.goal
  pure (answer.map fun result => (result,
    result.candidate.children.zipIdx.map fun (goal, index) =>
      (childAddress visit.invocation index, goal)))

theorem step_no_new_failure (slots : Nat → α) (names : Table)
    (state : CommonRoleRegisteredCaptureSources.State α) (visit : Visit) :
    (step slots names state visit).map (Option.map Prod.fst) =
      CommonRoleRegisteredCaptureSources.run slots state
        (compile names visit).invocation visit.invocation.declaration visit.goal := by
  cases result : CommonRoleRegisteredCaptureSources.run slots state
    (compile names visit).invocation visit.invocation.declaration visit.goal with
  | none => simp [step, result]
  | some answer => cases answer <;> simp [step, result]

theorem step_children (slots : Nat → α) (names : Table)
    (state : CommonRoleRegisteredCaptureSources.State α) (visit : Visit)
    (result : CommonRoleRegisteredCaptureSources.Result α) (tagged : List (Address × Goal))
    (returned : step slots names state visit = some (some (result, tagged))) :
    tagged = children visit.invocation (CommonRoleIntervalCapture.total result.candidate.bindings) := by
  cases inspected : CommonRoleIntervalCandidates.inspect visit.invocation.declaration visit.goal with
  | none => simp [step, CommonRoleRegisteredCaptureSources.run, inspected] at returned
  | some answer =>
    cases answer with
    | none => simp [step, CommonRoleRegisteredCaptureSources.run, inspected] at returned
    | some bindings =>
      have equal := returned
      simp only [step, CommonRoleRegisteredCaptureSources.run, inspected,
        Option.pure_def] at equal
      rcases equal with ⟨rfl, rfl⟩
      rfl

private theorem registry_follow_append (slots : Nat → α)
    (state : CommonRoleRegisteredCaptureSources.State α)
    (first last : List CommonRoleRegisteredCaptureSources.Visit) :
    CommonRoleRegisteredCaptureSources.follow slots state (first ++ last) =
      (CommonRoleRegisteredCaptureSources.follow slots state first).bind
        (fun after => CommonRoleRegisteredCaptureSources.follow slots after last) := by
  induction first generalizing state with
  | nil => rfl
  | cons visit rest ih =>
    simp only [List.cons_append, CommonRoleRegisteredCaptureSources.follow]
    cases stepped : CommonRoleRegisteredCaptureSources.run slots state
      visit.invocation visit.declaration visit.goal with
    | none => rfl
    | some answer =>
      cases answer with
      | none => rfl
      | some result => simpa using ih result.registry

/-- A completed prefix can be resumed without recomputing it or renumbering
its existing capture sources. The retained structural trace supplies the table. -/
theorem follow_append (slots : Nat → α) (old : List (Demand α))
    (earlier later : List Visit) :
    follow slots old (earlier ++ later) =
      (follow slots old earlier).bind fun state =>
        CommonRoleRegisteredCaptureSources.follow slots state
          (later.map (compile (table (earlier ++ later)))) := by
  have prefixSame : earlier.map (compile (table (earlier ++ later))) =
      earlier.map (compile (table earlier)) := by
    apply List.map_congr_left
    intro visit member
    exact compile_append earlier later visit member
  simp only [follow, List.map_append, registry_follow_append, prefixSame]

/-- Original shared-model semantics; no numeric registry, allocated name,
generated constraint, or executor appears in the judgment. -/
def Fits (slots : Nat → α) (assignment : α → Comp Common.model)
    (locals : Invocation → Nat → Common.Ty) (visits : List Visit) : Prop :=
  ∀ visit ∈ visits, ∃ bindings,
    Accepts visit.invocation.declaration visit.goal bindings ∧
    HeadFits (fun n => (assignment (slots n)).1) (locals visit.invocation)
      visit.invocation.declaration.head visit.goal.arguments ∧
    WhereFits (fun n => (assignment (slots n)).1) (locals visit.invocation)
      visit.invocation.declaration bindings

private theorem transport (slots : Nat → α) (assignment : α → Comp Common.model)
    (names : Table) (visits : List Visit) (numeric : CommonRoleRegisteredCaptureSources.Key → Common.Ty)
    (locals : Invocation → Nat → Common.Ty)
    (agrees : ∀ visit ∈ visits, ∀ binder,
      numeric (names.idxOf visit.invocation, binder) = locals visit.invocation binder) :
    CommonRoleRegisteredCaptureSources.VisitsFit slots assignment numeric (visits.map (compile names)) ↔
      Fits slots assignment locals visits := by
  induction visits with
  | nil => simp [CommonRoleRegisteredCaptureSources.VisitsFit, Fits]
  | cons visit rest ih =>
    have head : (fun n => numeric (names.idxOf visit.invocation, n)) = locals visit.invocation :=
      funext (agrees visit List.mem_cons_self)
    have tail := ih (fun v member => agrees v (List.mem_cons_of_mem _ member))
    simp only [List.map_cons, CommonRoleRegisteredCaptureSources.VisitsFit, compile, head, tail]
    simp only [Fits, List.forall_mem_cons]
    constructor
    · rintro ⟨bindings, accepted, head, children, tail⟩
      exact ⟨⟨bindings, accepted, head, children⟩, tail⟩
    · rintro ⟨⟨bindings, accepted, head, children⟩, tail⟩
      exact ⟨bindings, accepted, head, children, tail⟩

/-- A finite table yields both directions of original-model transport.
Unregistered inputs of the mathematical valuation are irrelevant. -/
theorem shared_models_exact (slots : Nat → α) (assignment : α → Comp Common.model)
    (visits : List Visit) :
    (∃ numeric, CommonRoleRegisteredCaptureSources.VisitsFit slots assignment numeric
      (visits.map (compile (table visits)))) ↔
      ∃ locals, Fits slots assignment locals visits := by
  constructor
  · rintro ⟨numeric, fits⟩
    exact ⟨fun invocation binder => numeric ((table visits).idxOf invocation, binder),
      (transport slots assignment (table visits) visits numeric _ (fun _ _ _ => rfl)).mp fits⟩
  · rintro ⟨locals, fits⟩
    let numeric : CommonRoleRegisteredCaptureSources.Key → Common.Ty := fun key =>
      match (table visits)[key.1]? with
      | none => .bottom
      | some invocation => locals invocation key.2
    refine ⟨numeric, (transport slots assignment (table visits) visits numeric locals ?_).mpr fits⟩
    intro visit member binder
    have present : visit.invocation ∈ table visits := List.mem_map.mpr ⟨visit, member, rfl⟩
    have found : (table visits)[(table visits).idxOf visit.invocation]? = some visit.invocation :=
      List.getElem?_eq_some_iff.mpr
        ⟨List.idxOf_lt_length_of_mem present, List.getElem_idxOf (List.idxOf_lt_length_of_mem present)⟩
    simp [numeric, found]

/-- General finite addressed-trace iff. No source map, successful-run,
consistency, common-model or child-dictionary hypothesis is supplied.
This is not the language-wide finite-work or saturation theorem. -/
theorem follow_models_exact (slots : Nat → α) (assignment : α → Comp Common.model)
    (old : List (Demand α)) (visits : List Visit) :
    (∃ after, follow slots old visits = some after ∧ Models assignment after.requests) ↔
      Models assignment old ∧ ∃ locals, Fits slots assignment locals visits := by
  unfold follow
  rw [CommonRoleRegisteredCaptureSources.follow_models_exact, shared_models_exact]

/-- Where conjunction does not depend on execution order. This claims equality
of model existence, not equality of emitted names, atom lists or dictionaries. -/
theorem reorder_models (slots : Nat → α) (assignment : α → Comp Common.model)
    (old : List (Demand α)) (first last : List Visit) (permuted : first.Perm last) :
    (∃ after, follow slots old first = some after ∧ Models assignment after.requests) ↔
    (∃ after, follow slots old last = some after ∧ Models assignment after.requests) := by
  simp only [follow_models_exact, Fits]
  have same : ∀ visit, visit ∈ first ↔ visit ∈ last := fun _ => permuted.mem_iff
  simp only [same]

/-- Repeating an unchanged finite pass adds no model restriction. Endpoint
refinement is deliberately not erased by this theorem. -/
theorem repeat_models (slots : Nat → α) (assignment : α → Comp Common.model)
    (old : List (Demand α)) (visits : List Visit) :
    (∃ after, follow slots old (visits ++ visits) = some after ∧ Models assignment after.requests) ↔
    (∃ after, follow slots old visits = some after ∧ Models assignment after.requests) := by
  simp only [follow_models_exact, Fits, List.mem_append, or_self]

end Yulang.CommonRoleAddressedCaptureModels
