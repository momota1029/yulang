import Yulang.CommonRoleDynamicIndexResidualFrontier
import Yulang.CommonRoleMaterializedDomain

/-! Original batch/request provenance for the finite string/equality fragment.
Unlike the canonical residual pair list, this diagnostic preserves source request
order and multiplicity, including names absent from the slot table. Waiting/ready
are internal observations, not the language four-way classification or dictionaries.
The finite fixed carrier and supplied batches remain proof-fragment restrictions. -/
namespace Yulang.CommonRoleDynamicIndexOccurrenceDiagnostics
open CommonRoleSourceIdentity (Table Slot source)
open CommonRoleDynamicIndexResidualBatches
open CommonRoleDynamicIndexResidualSource (Packet pairs pairs_exact)
open CommonRoleDynamicIndexResidualFrontier
open CommonRoleDynamicIndexSourceSemantics (ForcesString)

structure RequestDiagnostic (table : Table) where
  request : Nat × Nat
  endpoints : List ((Slot table × Slot table) × Bool)
  deriving DecidableEq

/-- Every occurrence retains its name, even when no endpoint pair represents it.
The Boolean marks an actually pending pair; false does not claim a dictionary. -/
def inspect (table : Table) (packet : Packet table) (r : Nat × Nat) : RequestDiagnostic table :=
  ⟨r, (pairs table [r]).map fun ij => (ij, decide (ij ∈ packet.pending))⟩

/-- One node per original batch, then one node per original request occurrence.
The final compacted packet supplies observations, never the provenance skeleton. -/
def diagnose (table : Table) (p : Problem table) (updates : List (Problem table)) :
    List (List (RequestDiagnostic table)) :=
  (p :: updates).map fun batch => batch.requests.map (inspect table (solve table p updates))

/-- Exact source order and multiplicity are retained through all compactions. -/
theorem original_order (table : Table) (p : Problem table) (updates : List (Problem table)) :
    (diagnose table p updates).map (List.map RequestDiagnostic.request) =
      (p :: updates).map Problem.requests := by
  simp [diagnose, inspect, List.map_map, Function.comp_def]

/-- Aliased names retain all distinct endpoint pairs, not just one representative. -/
theorem inspect_endpoints (table : Table) (packet : Packet table) (r : Nat × Nat) :
    (inspect table packet r).endpoints.map Prod.fst = pairs table [r] := by
  simp [inspect, List.map_map, Function.comp_def]

/-- Missing endpoints are visible as an empty list under the retained source name.
This records scope failure without assigning a language rejection classification. -/
theorem inspect_missing (table : Table) (packet : Packet table) (r : Nat × Nat) :
    (inspect table packet r).endpoints = [] ↔
      ¬ ∃ i j : Slot table, source table i = r.1 ∧ source table j = r.2 := by
  simp only [inspect, List.map_eq_nil_iff]
  constructor
  · intro empty ⟨i,j,hi,hj⟩
    have mem : (i,j) ∈ pairs table [r] := (pairs_exact ..).mpr (by simp [hi,hj])
    simp [empty] at mem
  · intro missing
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro ij hm
    have names := (pairs_exact table [r] ij.1 ij.2).mp hm
    have eq : (source table ij.1, source table ij.2) = r := by simpa using names
    exact missing ⟨ij.1,ij.2,congrArg Prod.fst eq,congrArg Prod.snd eq⟩

/-- Independent source meaning of the waiting bit, with all source models
quantified. Ready means forced string in this fragment, not chosen impl evidence. -/
def Meaning (table : Table) (original : Problem table) (i : Slot table) (waiting : Bool) : Prop :=
  if waiting then
    ¬ ForcesString table original.seeds original.links original.requests i
  else ForcesString table original.seeds original.links original.requests i

/-- Every represented original occurrence has precisely its independent meaning.
No consistency, closure, acyclicity, or model oracle is a premise. -/
theorem inspect_exact (table : Table) (p : Problem table) (updates : List (Problem table))
    (r : Nat × Nat) (hr : r ∈ (appendMany table p updates).requests)
    (i j : Slot table) (waiting : Bool) :
    ((i,j),waiting) ∈ (inspect table (solve table p updates) r).endpoints ↔
      source table i = r.1 ∧ source table j = r.2 ∧
        Meaning table (appendMany table p updates) i waiting := by
  classical
  have membership : ((i,j),waiting) ∈ (inspect table (solve table p updates) r).endpoints ↔
      (source table i, source table j) = r ∧
      decide ((i,j) ∈ (solve table p updates).pending) = waiting := by
    simp only [inspect, List.mem_map]
    constructor
    · rintro ⟨ij,hij,eq⟩
      have slots : ij = (i,j) := congrArg Prod.fst eq
      subst ij
      exact ⟨by simpa using (pairs_exact table [r] i j).mp hij, congrArg Prod.snd eq⟩
    · rintro ⟨names,bit⟩
      exact ⟨(i,j),(pairs_exact ..).mpr (by simp [names]),by simp [bit]⟩
  rw [membership]
  by_cases names : (source table i, source table j) = r
  · have requested : (source table i, source table j) ∈ (appendMany table p updates).requests := by
      simpa [names] using hr
    have pending := solve_residual_exact table p updates i j
    simp only [requested, true_and] at pending
    have first := congrArg Prod.fst names
    have second := congrArg Prod.snd names
    cases waiting <;> simp_all [Meaning]
  · have separate : ¬ (source table i = r.1 ∧ source table j = r.2) := by
      simpa only [Prod.ext_iff] using names
    simp only [names, false_and]
    exact iff_of_false (by trivial) (fun h => separate ⟨h.1,h.2.1⟩)

/-- A source-level request meaning does not refer to the solver, compaction,
pending list, or diagnostic constructor. It retains the supplied request name. -/
def RequestMeaning (table : Table) (original : Problem table) (r : Nat × Nat)
    (node : RequestDiagnostic table) : Prop :=
  node.request = r ∧ ∀ i j waiting,
    ((i,j),waiting) ∈ node.endpoints ↔
      source table i = r.1 ∧ source table j = r.2 ∧ Meaning table original i waiting

/-- Independent nested occurrence correspondence. All₂ retains batch and
request order and multiplicity; leaf meaning uses only original source models. -/
def Represents (table : Table) (original : Problem table) (batches : List (Problem table))
    (diagnostic : List (List (RequestDiagnostic table))) : Prop :=
  CommonRoleOutermostResolver.All₂ (fun batch row => CommonRoleOutermostResolver.All₂ (RequestMeaning table original) batch.requests row)
    batches diagnostic

/-- The complete diagnostic satisfies the independent occurrence relation for
all finite inputs, including absent names, aliases, cycles, and repeated requests.
No successful scope check or supplied semantic witness is required. -/
theorem diagnose_represents (table : Table) (p : Problem table) (updates : List (Problem table)) :
    Represents table (appendMany table p updates) (p :: updates) (diagnose table p updates) := by
  have request_rows (rs : List (Nat × Nat))
      (included : ∀ r ∈ rs, r ∈ (appendMany table p updates).requests) :
      CommonRoleOutermostResolver.All₂ (RequestMeaning table (appendMany table p updates)) rs
        (rs.map (inspect table (solve table p updates))) := by
    induction rs with
    | nil => exact .nil
    | cons r rest ih =>
      apply CommonRoleOutermostResolver.All₂.cons
      · exact ⟨rfl, inspect_exact table p updates r (included r (by simp))⟩
      · exact ih (fun q hq => included q (by simp [hq]))
  have rows (batches : List (Problem table))
      (included : ∀ batch ∈ batches, ∀ r ∈ batch.requests,
        r ∈ (appendMany table p updates).requests) :
      CommonRoleOutermostResolver.All₂ (fun batch row =>
        CommonRoleOutermostResolver.All₂ (RequestMeaning table (appendMany table p updates)) batch.requests row)
        batches (batches.map fun batch => batch.requests.map (inspect table (solve table p updates))) := by
    induction batches with
    | nil => exact .nil
    | cons batch rest ih =>
      exact .cons (request_rows batch.requests (included batch (by simp)))
        (ih (fun q hq => included q (by simp [hq])))
  apply rows
  intro batch hb r hr
  apply (appendMany_requests table updates p r).mpr
  rcases List.mem_cons.mp hb with h | h
  · subst batch; exact .inl hr
  · exact .inr ⟨batch,h,hr⟩

/-- Every original batch occurrence gets a diagnostic node, even if missing or
unresolved. Equal repeated requests keep repeated entries by original_order. -/
theorem original_retained (table : Table) (p : Problem table) (updates : List (Problem table))
    (batch : Problem table) (hb : batch ∈ p :: updates) (r : Nat × Nat)
    (hr : r ∈ batch.requests) :
    ∃ row ∈ diagnose table p updates,
      inspect table (solve table p updates) r ∈ row := by
  exact ⟨batch.requests.map (inspect table (solve table p updates)),
    List.mem_map.mpr ⟨batch,hb,rfl⟩, List.mem_map.mpr ⟨r,hr,rfl⟩⟩

/-- The leaf waiting bit is also exactly the actual checked producer's failure,
for represented original obligations. -/
theorem inspect_checked (table : Table) (p : Problem table) (updates : List (Problem table))
    (r : Nat × Nat) (hr : r ∈ (appendMany table p updates).requests)
    (i j : Slot table) :
    ((i,j),true) ∈ (inspect table (solve table p updates) r).endpoints ↔
      source table i = r.1 ∧ source table j = r.2 ∧
      CommonRoleOrdinaryKnownness.checkedProduceIndex (solve table p updates).state i j = none := by
  rw [inspect_exact table p updates r hr i j true]
  simp only [Meaning, ↓reduceIte]
  have pending := solve_residual_checked table p updates i j
  have meaning := solve_residual_exact table p updates i j
  by_cases names : source table i = r.1 ∧ source table j = r.2
  · have requested : (source table i, source table j) ∈ (appendMany table p updates).requests := by
      simpa [names.1,names.2] using hr
    simp only [requested, true_and] at pending meaning
    exact and_congr Iff.rfl (and_congr Iff.rfl (meaning.symm.trans pending))
  · constructor <;> intro h <;> exact False.elim (names ⟨h.1,h.2.1⟩)

/-- Reordering update batches leaves every request diagnostic literally equal.
The outer batch order intentionally remains the original source order. -/
theorem update_order_inspect (table : Table) (p : Problem table)
    (left right : List (Problem table)) (same : ∀ u, u ∈ left ↔ u ∈ right)
    (r : Nat × Nat) :
    inspect table (solve table p left) r = inspect table (solve table p right) r := by
  simp only [inspect, update_order_pending_list table p left right same]

/-- Incremental observations equal observations from the full original rebuild. -/
theorem inspect_rebuild (table : Table) (p : Problem table) (updates : List (Problem table))
    (r : Nat × Nat) :
    inspect table (solve table p updates) r =
      inspect table (CommonRoleDynamicIndexResidualSource.build table
        (appendMany table p updates).seeds (appendMany table p updates).links
        (appendMany table p updates).requests) r := by
  simp only [inspect, solve_pending_rebuild]

/-- A repeated original request survives as two diagnostics; a missing name stays
visible, while an unresolved represented request remains waiting. -/
theorem repeated_and_missing :
    let p : Problem [10,20] := ⟨[],[],[(10,20),(10,20),(10,99)]⟩
    diagnose [10,20] p [] =
      [[⟨(10,20),[((0,1),true)]⟩, ⟨(10,20),[((0,1),true)]⟩, ⟨(10,99),[]⟩]] := by
  decide

/-- Boundary: the legacy tree endpoint decoder loses a known string observation.
This theorem explains why the new diagnostic cannot claim to close that adapter. -/
theorem legacy_endpoint_erases_string (s : CommonRoleSettledConstraints.State n) (i : Fin n)
    (known : CommonRoleOrdinaryKnownness.materialize s.atoms i = some Roles.Examples.str) :
    (CommonRoleMaterializedDomain.Endpoint.slot i).eval s = .unknown := by
  simp [CommonRoleMaterializedDomain.Endpoint.eval, known, Roles.Examples.str, Roles.Examples.int]

end Yulang.CommonRoleDynamicIndexOccurrenceDiagnostics
