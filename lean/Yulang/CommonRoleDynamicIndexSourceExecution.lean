import Yulang.CommonRoleDynamicIndexSource

/-! Interpret the compiled source schedule without treating alias edges as
role invocations. Aliases only record a consequence of source identity;
named Index edges use the actual checked declaration producer. -/
namespace Yulang.CommonRoleDynamicIndexSourceExecution
open CommonRoleSourceIdentity (Table Slot source Coherent)
open CommonRoleSettledConstraints (State)
open CommonRoleOrdinaryKnownness (Evidence)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)
open CommonRoleDynamicIndexSource (Requests edges)
open CommonRoleDynamicIndexClosure (record)

def initial (table : Table) (s : State table.length) := CommonRoleSourceIdentity.extend table s

/-- An alias move adds no models and removes none, provided the receiver has
already been recorded. This result needs no consistency assumption. -/
theorem alias_models (table : Table) (s : State table.length) (xs : List (Slot table))
    (i j : Slot table) (same : source table i = source table j) (hi : i ∈ xs)
    (a : Slot table → Comp Common.model) :
    All Common.model a (record (initial table s) (j :: xs)).atoms ↔
      All Common.model a (record (initial table s) xs).atoms := by
  rw [record, CommonRoleCandidateStateFrontier.extend_exact]
  constructor
  · exact And.left
  · intro hm
    have h := (CommonRoleDynamicIndexClosure.record_models _ xs a).mp hm
    have hc := ((CommonRoleSourceIdentity.extend_exact table s a).mp h.1).2
    exact ⟨hm, Common.equivalent_trans (Common.equivalent_symm (hc i j same)) (h.2 i hi)⟩

inductive Executed (table : Table) (s : State table.length) (requests : Requests) :
    List (Slot table) → Prop where
  | nil : Executed table s requests []
  | seed : Executed table s requests xs → Evidence (initial table s).atoms i .str →
      Executed table s requests (i :: xs)
  | alias : Executed table s requests xs → source table i = source table j → i ∈ xs →
      (∀ a, All Common.model a (record (initial table s) (j :: xs)).atoms ↔
        All Common.model a (record (initial table s) xs).atoms) →
      Executed table s requests (j :: xs)
  | index : Executed table s requests xs → (source table i,source table j) ∈ requests →
      CommonRoleOrdinaryKnownness.produceIndex (record (initial table s) xs) i j =
        some (record (initial table s) (j :: xs)) → Executed table s requests (j :: xs)

/-- Every compiled trace can be executed. Only the actual receiver read uses
the explicit final-model premise; it is not an existence theorem for that model. -/
theorem trace_executes (table : Table) (s : State table.length) (requests : Requests)
    (xs : List (Slot table))
    (h : CommonRoleDynamicIndexClosure.Trace (initial table s) (edges table requests) xs)
    (a : Slot table → Comp Common.model)
    (hm : All Common.model a (CommonRoleDynamicIndexSource.output table s requests).atoms) :
    Executed table s requests xs := by
  have all := (CommonRoleDynamicIndexClosure.output_models (initial table s)
    (edges table requests) a).mp hm
  induction h with
  | nil => exact .nil
  | seed _ he ih => exact .seed ih he
  | @index xs i j hx he hi ih =>
    rcases (CommonRoleDynamicIndexSource.edges_exact table requests i j).mp he with hs | hr
    · exact .alias ih hs hi (alias_models table s xs i j hs hi)
    · apply Executed.index ih hr
      apply CommonRoleOrdinaryKnownness.index_from_detected_str
      apply CommonRoleDynamicIndexClosure.detects_recorded (initial table s) xs i hi a
      exact (CommonRoleDynamicIndexClosure.record_models _ xs a).mpr ⟨all.1, fun k hk =>
        all.2 k (CommonRoleDynamicIndexClosure.trace_derived _ _ xs hx k hk)⟩

theorem saturate_executes (table : Table) (s : State table.length) (requests : Requests)
    (a : Slot table → Comp Common.model)
    (hm : All Common.model a (CommonRoleDynamicIndexSource.output table s requests).atoms) :
    Executed table s requests
      (CommonRoleDynamicIndexSource.saturate table (initial table s) requests) :=
  trace_executes table s requests _ (CommonRoleDynamicIndexClosure.saturate_trace ..) a hm

/-- Re-saturating the final output has the same fact membership. This concerns
the compiled graph and does not identify duplicate atoms or list order. -/
theorem output_fixed (table : Table) (s : State table.length) (requests : Requests)
    (i : Slot table) :
    i ∈ CommonRoleDynamicIndexSource.saturate table
      (CommonRoleDynamicIndexSource.output table s requests) requests ↔
    i ∈ CommonRoleDynamicIndexSource.saturate table (initial table s) requests :=
  CommonRoleDynamicIndexClosure.saturate_output_fixed ..

end Yulang.CommonRoleDynamicIndexSourceExecution
