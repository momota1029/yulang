import Yulang.CommonRoleDynamicIndexCheckedSource

/-! A consistent finite string fragment with explicit seeds and slot equalities.
The input syntax constructs an actual ordinary State. A concrete all-string
assignment discharges final-model existence, rather than requiring it from the
caller. Scope still does not imply that an unseeded receiver is reachable. Extra slot
equalities are model constraints, not a claim of complete evidence propagation. -/
namespace Yulang.CommonRoleDynamicIndexConsistentSource
open CommonRoleSourceIdentity (Table Slot)
open CommonRoleSettledConstraints (State)
open CommonRoleDynamicIndexSource (Requests)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)

/-- The model is explicit, including its empty effect component. -/
def stringAssignment : Fin n → Comp Common.model := fun _ => (.base .str, Common.rowEmpty)

def addEqualities (s : State n) : List (Fin n × Fin n) → State n
  | [] => s
  | (i,j) :: rest =>
    let t := addEqualities s rest
    let g := CommonRoleSourceIdentity.pair_grammar i j
    ⟨t.atoms ++ CommonRoleSourceIdentity.pairAtoms i j,
      t.child.append g.1, t.width.append g.2.1, t.rows.append g.2.2⟩

/-- Arbitrary seed occurrences and arbitrary type-equality links, no opaque
ordinary constraints. Effects are not equated by these links. -/
def input (seeds : List (Fin n)) (links : List (Fin n × Fin n)) : State n :=
  addEqualities (CommonRoleDynamicIndexClosure.record State.empty seeds) links

theorem addEqualities_models (s : State n) (links : List (Fin n × Fin n))
    (a : Fin n → Comp Common.model) :
    All Common.model a (addEqualities s links).atoms ↔
      All Common.model a s.atoms ∧
        ∀ e ∈ links, Common.Equivalent (a e.1).1 (a e.2).1 := by
  induction links with
  | nil => simp [addEqualities]
  | cons e rest ih =>
    rcases e with ⟨i,j⟩
    simp only [addEqualities, PresenceNormalForm.all_append,
      CommonRoleSourceIdentity.pair_exact, ih, List.mem_cons, forall_eq_or_imp]
    exact ⟨fun ⟨⟨h,hr⟩,he⟩ => ⟨h,he,hr⟩, fun ⟨h,he,hr⟩ => ⟨⟨h,hr⟩,he⟩⟩

theorem input_models (seeds : List (Fin n)) (links : List (Fin n × Fin n))
    (a : Fin n → Comp Common.model) :
    All Common.model a (input seeds links).atoms ↔
      (∀ i ∈ seeds, Common.Equivalent (a i).1 (.base .str)) ∧
      ∀ e ∈ links, Common.Equivalent (a e.1).1 (a e.2).1 := by
  simp only [input, addEqualities_models, CommonRoleDynamicIndexClosure.record_models]
  have h : All Common.model a (State.empty (n := n)).atoms := by intro atom h; cases h
  simp only [h, true_and]

theorem input_has_model (seeds : List (Fin n)) (links : List (Fin n × Fin n)) :
    All Common.model stringAssignment (input seeds links).atoms := by
  apply (input_models seeds links stringAssignment).mpr
  exact ⟨fun _ _ => Common.equivalent_refl _, fun _ _ => Common.equivalent_refl _⟩

/-- All finite graphs and seed/equality lists in this fragment have an output
model, even if the graph is cyclic or contains duplicate requests. -/
theorem output_has_model (table : Table) (seeds : List (Slot table))
    (links : List (Slot table × Slot table)) (requests : Requests) :
    All Common.model stringAssignment
      (CommonRoleDynamicIndexSource.output table (input seeds links) requests).atoms := by
  apply (CommonRoleDynamicIndexSource.output_models ..).mpr
  exact ⟨input_has_model seeds links,
    (fun _ _ _ => Common.equivalent_refl _), fun _ _ => Common.equivalent_refl _⟩

theorem output_consistent (table : Table) (seeds : List (Slot table))
    (links : List (Slot table × Slot table)) (requests : Requests) :
    CommonRoleOpenPropagation.consistent
      (CommonRoleDynamicIndexSource.output table (input seeds links) requests) = true :=
  (CommonRoleOpenPropagation.consistent_exact _).mpr
    ⟨stringAssignment, output_has_model table seeds links requests⟩

/-- Unlike the general trace theorem, this statement has no final-model premise.
Only seeds, source aliases, and enabled named Index edges occur in this trace. -/
theorem saturate_executes (table : Table) (seeds : List (Slot table))
    (links : List (Slot table × Slot table)) (requests : Requests) :
    CommonRoleDynamicIndexSourceExecution.Executed table (input seeds links) requests
      (CommonRoleDynamicIndexSource.saturate table
        (CommonRoleSourceIdentity.extend table (input seeds links)) requests) :=
  CommonRoleDynamicIndexSourceExecution.saturate_executes table (input seeds links)
    requests stringAssignment (output_has_model table seeds links requests)

theorem checked_success_iff (table : Table) (seeds : List (Slot table))
    (links : List (Slot table × Slot table)) (requests : Requests) :
    (∃ out, CommonRoleDynamicIndexCheckedSource.run table (input seeds links) requests = .ok out ∧
      out.Models) ↔ CommonRoleDynamicIndexSource.WellScoped table requests := by
  constructor
  · rintro ⟨out, hr, _⟩
    exact ((CommonRoleDynamicIndexCheckedSource.run_ok_iff ..).mp hr).1
  · intro hs
    exact ⟨_, (CommonRoleDynamicIndexCheckedSource.run_ok_iff ..).mpr ⟨hs,rfl⟩,
      stringAssignment, output_has_model table seeds links requests⟩

/-- Any receiver proved reachable from the actual seed state can execute its
real checked producer at the output, with consistency certified constructively. -/
theorem reachable_checked_step (table : Table) (seeds : List (Slot table))
    (links : List (Slot table × Slot table)) (requests : Requests) (i j : Slot table)
    (hi : CommonRoleDynamicIndexSource.Derived table
      (CommonRoleSourceIdentity.extend table (input seeds links)) requests i) :
    CommonRoleOrdinaryKnownness.checkedProduceIndex
      (CommonRoleDynamicIndexSource.output table (input seeds links) requests) i j =
      some (CommonRoleCandidateStateFrontier.extend
        (CommonRoleDynamicIndexSource.output table (input seeds links) requests) j .str) := by
  apply (CommonRoleOrdinaryKnownness.checked_exact ..).mpr
  constructor
  · apply CommonRoleDynamicIndexClosure.actual_index_step
      (CommonRoleSourceIdentity.extend table (input seeds links))
      (CommonRoleDynamicIndexSource.edges table requests) i j
      ((CommonRoleDynamicIndexSource.derived_exact ..).mpr hi) stringAssignment
    exact output_has_model table seeds links requests
  · refine ⟨stringAssignment, (CommonRoleCandidateStateFrontier.extend_exact ..).mpr ?_⟩
    exact ⟨output_has_model table seeds links requests, Common.equivalent_refl _⟩

/-- Shared source 10 has two occurrences. Its seed activates both named edges. -/
theorem shared_chain_reachable :
    CommonRoleDynamicIndexSource.Derived [10,10,20,30]
      (CommonRoleSourceIdentity.extend [10,10,20,30]
        (input [0] [(0,1)])) [(10,20),(20,30)] 3 := by
  apply (CommonRoleDynamicIndexSource.saturate_exact ..).mp
  decide

/-- The downstream real checked producer succeeds without an external model. -/
theorem shared_chain_checked :
    let out := CommonRoleDynamicIndexSource.output [10,10,20,30]
      (input [0] [(0,1)]) [(10,20),(20,30)]
    CommonRoleOrdinaryKnownness.checkedProduceIndex out 2 3 =
      some (CommonRoleCandidateStateFrontier.extend out 3 .str) := by
  apply reachable_checked_step
  apply (CommonRoleDynamicIndexSource.saturate_exact ..).mp
  decide

/-- Consistency and scope do not manufacture evidence for a receiver. -/
theorem unseeded_still_pending :
    CommonRoleOrdinaryKnownness.produceIndex
      (CommonRoleDynamicIndexSource.output [10,20] (input [] []) [(10,20)]) 0 1 = none := by
  decide

end Yulang.CommonRoleDynamicIndexConsistentSource
