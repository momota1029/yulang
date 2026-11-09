import Yulang.CommonRoleDynamicIndexResidualResume

/-! Residual continuation under arbitrary finite batches of string seeds, slot
equalities, and named obligations. The source table is fixed and each update
list is supplied finitely. This restriction is an implementation/proof fragment,
not a language rejection rule or general generated-child termination theorem. -/
namespace Yulang.CommonRoleDynamicIndexResidualBatches
open CommonRoleSourceIdentity (Table Slot)
open CommonRoleDynamicIndexSource (Requests WellScoped)
open CommonRoleDynamicIndexEqualitySource (Links)
open CommonRoleDynamicIndexSourceSemantics (SourceModel ForcesString)
open CommonRoleDynamicIndexResidualSource (Packet Models build)
open CommonRoleDynamicIndexResidualResume (retainedSeeds pendingNames)
open CommonRoleDynamicIndexCheckedSource (missing missing_nil_iff)
open Core.PresenceGeneration (Comp)

structure Problem (table : Table) where
  seeds : List (Slot table)
  links : Links table
  requests : Requests

/-- Independent conjunction of the original source clauses. -/
def Satisfies (table : Table) (p : Problem table) (a : Slot table → Comp Common.model) :=
  SourceModel table p.seeds p.links p.requests a

def append (table : Table) (p q : Problem table) : Problem table :=
  ⟨p.seeds ++ q.seeds, p.links ++ q.links, p.requests ++ q.requests⟩

/-- Every batch contributes all its equalities and conditional requests. -/
theorem append_models (table : Table) (p q : Problem table)
    (a : Slot table → Comp Common.model) :
    Satisfies table (append table p q) a ↔ Satisfies table p a ∧ Satisfies table q a := by
  constructor
  · intro h
    exact ⟨⟨fun i hi => h.seeds i (List.mem_append_left _ hi),
      fun e he => h.equalities e (List.mem_append_left _ he), h.aliases,
      fun i j hr hs => h.requests i j (List.mem_append_left _ hr) hs⟩,
      ⟨fun i hi => h.seeds i (List.mem_append_right _ hi),
      fun e he => h.equalities e (List.mem_append_right _ he), h.aliases,
      fun i j hr hs => h.requests i j (List.mem_append_right _ hr) hs⟩⟩
  · rintro ⟨hp,hq⟩
    refine ⟨?_, ?_, hp.aliases, ?_⟩
    · intro i hi
      rcases List.mem_append.mp hi with hi | hi
      · exact hp.seeds i hi
      · exact hq.seeds i hi
    · intro e he
      rcases List.mem_append.mp he with he | he
      · exact hp.equalities e he
      · exact hq.equalities e he
    · intro i j hr hs
      rcases List.mem_append.mp hr with hr | hr
      · exact hp.requests i j hr hs
      · exact hq.requests i j hr hs

/-- Keep derived facts and drop only requests whose targets are already retained. -/
def compact (table : Table) (p : Problem table) : Problem table :=
  ⟨retainedSeeds table p.seeds [] p.links p.requests, p.links,
    pendingNames table p.seeds p.links p.requests⟩

theorem compact_models (table : Table) (p : Problem table)
    (a : Slot table → Comp Common.model) :
    Satisfies table (compact table p) a ↔ Satisfies table p a := by
  simpa only [Satisfies, compact, List.append_nil] using
    CommonRoleDynamicIndexResidualResume.retained_source_exact
      table p.seeds [] p.links p.requests a

def advance (table : Table) (p update : Problem table) : Problem table :=
  append table (compact table p) update

theorem advance_models (table : Table) (p update : Problem table)
    (a : Slot table → Comp Common.model) :
    Satisfies table (advance table p update) a ↔
      Satisfies table (append table p update) a := by
  simp only [advance, append_models, compact_models]

/-- Number of update rounds is arbitrary but finite. The existing driver closes
all finite receiver feedback inside each round before discarding discharged work. -/
def advanceMany (table : Table) (p : Problem table) : List (Problem table) → Problem table
  | [] => p
  | update :: rest => advanceMany table (advance table p update) rest

def appendMany (table : Table) (p : Problem table) : List (Problem table) → Problem table
  | [] => p
  | update :: rest => appendMany table (append table p update) rest

theorem appendMany_models (table : Table) (updates : List (Problem table))
    (p : Problem table) (a : Slot table → Comp Common.model) :
    Satisfies table (appendMany table p updates) a ↔
      Satisfies table p a ∧ ∀ u ∈ updates, Satisfies table u a := by
  induction updates generalizing p with
  | nil => simp [appendMany]
  | cons u rest ih =>
    simp only [appendMany, ih, append_models, List.mem_cons, forall_eq_or_imp]
    exact and_assoc

/-- Main full-model theorem: every original batch is preserved after arbitrary
finite repeated residual compaction. No model or acyclicity premise is supplied. -/
theorem advanceMany_models (table : Table) (updates : List (Problem table))
    (p : Problem table) (a : Slot table → Comp Common.model) :
    Satisfies table (advanceMany table p updates) a ↔
      Satisfies table (appendMany table p updates) a := by
  induction updates generalizing p with
  | nil => rfl
  | cons u rest ih =>
    simp only [advanceMany, appendMany, ih, appendMany_models, advance_models]

def solve (table : Table) (p : Problem table) (updates : List (Problem table)) : Packet table :=
  let final := advanceMany table p updates
  build table final.seeds final.links final.requests

theorem solve_models_exact (table : Table) (p : Problem table)
    (updates : List (Problem table)) (a : Slot table → Comp Common.model) :
    Models table (solve table p updates) a ↔
      Satisfies table (appendMany table p updates) a := by
  rw [solve, CommonRoleDynamicIndexResidualSource.build_models_exact]
  exact advanceMany_models ..

/-- Checked execution after all rounds uses exactly the original accumulated
source models, including later equality constraints and newly supplied requests. -/
theorem solve_checked_exact (table : Table) (p : Problem table)
    (updates : List (Problem table)) (i j : Slot table) :
    (∃ out, CommonRoleOrdinaryKnownness.checkedProduceIndex
      (solve table p updates).state i j = some out) ↔
    ∀ a, Satisfies table (appendMany table p updates) a →
      Common.Equivalent (a i).1 (.base .str) := by
  change (∃ out, CommonRoleOrdinaryKnownness.checkedProduceIndex
    (CommonRoleDynamicIndexEqualitySource.output table
      (advanceMany table p updates).seeds (advanceMany table p updates).links
      (advanceMany table p updates).requests) i j = some out) ↔ _
  rw [CommonRoleDynamicIndexSourceSemantics.checked_source_exact]
  constructor
  · intro h a ha
    exact h a ((advanceMany_models table updates p a).mpr ha)
  · intro h a ha
    exact h a ((advanceMany_models table updates p a).mp ha)

theorem solve_pending_exact (table : Table) (p : Problem table)
    (updates : List (Problem table)) (i j : Slot table) :
    CommonRoleOrdinaryKnownness.checkedProduceIndex (solve table p updates).state i j = none ↔
      ∃ a b : Slot table → Comp Common.model,
        Satisfies table (appendMany table p updates) a ∧
        Satisfies table (appendMany table p updates) b ∧
        ¬ Common.Equivalent (a i).1 (b i).1 := by
  change _ ↔ ∃ a b, SourceModel table _ _ _ a ∧ SourceModel table _ _ _ b ∧ _
  rw [CommonRoleDynamicIndexSourceSemantics.source_underdetermined_iff]
  constructor
  · intro hn hf
    obtain ⟨out, ho⟩ := (solve_checked_exact table p updates i j).mpr hf
    rw [hn] at ho
    cases ho
  · intro hn
    cases h : CommonRoleOrdinaryKnownness.checkedProduceIndex (solve table p updates).state i j with
    | none => rfl
    | some out => exact False.elim (hn ((solve_checked_exact ..).mp ⟨out,h⟩))

/-- Validate all original endpoints, including ones compacted out of the working
problem. This is an adapter diagnostic, not a final language rejection category. -/
def run (table : Table) (p : Problem table) (updates : List (Problem table)) :
    Except Requests (Packet table) :=
  let absent := missing table (appendMany table p updates).requests
  if absent = [] then .ok (solve table p updates) else .error absent

theorem run_ok_iff (table : Table) (p : Problem table) (updates : List (Problem table))
    (packet : Packet table) :
    run table p updates = .ok packet ↔
      WellScoped table (appendMany table p updates).requests ∧ packet = solve table p updates := by
  unfold run
  dsimp only
  split
  · rename_i h
    simp only [Except.ok.injEq]
    exact ⟨fun he => ⟨(missing_nil_iff ..).mp h, he.symm⟩, fun he => he.2.symm⟩
  · rename_i h
    constructor
    · intro he; cases he
    · intro he; exact False.elim (h ((missing_nil_iff ..).mpr he.1))

/-- Successful scope validation needs no externally assumed satisfiability. -/
theorem run_success_iff (table : Table) (p : Problem table) (updates : List (Problem table)) :
    (∃ packet, run table p updates = .ok packet) ↔
      WellScoped table (appendMany table p updates).requests := by
  constructor
  · rintro ⟨packet,h⟩
    exact ((run_ok_iff ..).mp h).1
  · intro h
    exact ⟨solve table p updates, (run_ok_iff ..).mpr ⟨h,rfl⟩⟩

theorem run_models_exact (table : Table) (p : Problem table) (updates : List (Problem table))
    (packet : Packet table) (h : run table p updates = .ok packet)
    (a : Slot table → Comp Common.model) :
    Models table packet a ↔
      Satisfies table p a ∧ ∀ u ∈ updates, Satisfies table u a := by
  rw [((run_ok_iff ..).mp h).2, solve_models_exact, appendMany_models]

/-- A concrete all-string assignment witnesses consistency of every successful
result; unconstrained effect rows are not equated by the slot type links. -/
theorem run_has_model (table : Table) (p : Problem table) (updates : List (Problem table))
    (packet : Packet table) (h : run table p updates = .ok packet) :
    Models table packet CommonRoleDynamicIndexConsistentSource.stringAssignment := by
  rw [((run_ok_iff ..).mp h).2, solve_models_exact]
  exact CommonRoleDynamicIndexSourceSemantics.string_source_model ..

/-- Refinement order does not affect complete packet models; neither list order
nor the concrete diagnostics/atoms are asserted to have identical serialization. -/
theorem update_order_models (table : Table) (p : Problem table)
    (left right : List (Problem table)) (same : ∀ u, u ∈ left ↔ u ∈ right)
    (a : Slot table → Comp Common.model) :
    Models table (solve table p left) a ↔ Models table (solve table p right) a := by
  simp only [solve_models_exact, appendMany_models]
  constructor
  · rintro ⟨hp,hs⟩
    exact ⟨hp,fun u hu => hs u ((same u).mpr hu)⟩
  · rintro ⟨hp,hs⟩
    exact ⟨hp,fun u hu => hs u ((same u).mp hu)⟩

/-- A late equality activates an old pending request; a subsequent new request
then consumes that result. Both are genuine updates to the previous fragment. -/
theorem equality_then_new_obligation :
    let p : Problem [10,20,30,40] := ⟨[0], [], [(20,30)]⟩
    let first : Problem [10,20,30,40] := ⟨[], [(0,1)], []⟩
    let second : Problem [10,20,30,40] := ⟨[], [], [(30,40)]⟩
    (build [10,20,30,40] p.seeds p.links p.requests).pending = [(1,2)] ∧
    (solve [10,20,30,40] p [first,second]).pending = [] ∧
    ∃ out, CommonRoleOrdinaryKnownness.checkedProduceIndex
      (solve [10,20,30,40] p [first,second]).state 3 0 = some out := by
  refine ⟨by decide, by decide, ?_⟩
  apply (solve_checked_exact ..).mpr
  apply (CommonRoleDynamicIndexSourceSemantics.source_forces_iff ..).mpr
  apply (CommonRoleDynamicIndexEqualitySource.saturate_exact ..).mp
  decide

/-- Compaction cannot hide absent names, even after all represented work closes. -/
theorem missing_requests_survive_validation :
    run [10,20] ⟨[0], [], [(10,99)]⟩ [⟨[],[(0,1)],[(98,20)]⟩] =
      .error [(10,99),(98,20)] := by rfl

end Yulang.CommonRoleDynamicIndexResidualBatches
