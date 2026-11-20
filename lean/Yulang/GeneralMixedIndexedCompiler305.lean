import Yulang.GeneralMixedIndexedDiagnosticLocal305

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralMixedIndexedCompiler305
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State)
open GeneralMixedIndexedFrame305 (IndexedView reverse)
open GeneralMixedDiagnosticSlice304 (Semantics)
open GeneralMixedDiagnosticHead304 (boundary8)
open GeneralMixedIndexedDiagnosticHeads305
open GeneralMixedIndexedDiagnosticOutputs305 (output_iff sharing_iff merged_iff)
open GeneralRebaseDiagnosticData268 (Inputs Valid SurvivorSound)
open GeneralMixedDiagnosticCompiler304 (reflect_map)
open GeneralRebasePartialClassification267 (Verdict)
variable {roles : Roles.RoleDecls} {a b : State roles}

theorem survivor_forward (rel : IndexedView a b) (r : Registry) (root : Occurrence roles)
    (v : Verdict (Nat × List (Occurrence roles))) (prior : SurvivorSound (boundary8 roles) r a root v) :
    SurvivorSound (boundary8 roles) r b root v := by
  cases v with
  | none => exact fun k cs found => prior k cs ((survivor_iff rel r root k cs).mpr found)
  | unique payload =>
    obtain ⟨k,cs⟩ := payload
    exact (unique_iff rel r root k cs).mp prior
  | ambiguous first last =>
    obtain ⟨k,cs⟩ := first
    obtain ⟨j,ds⟩ := last
    exact ⟨prior.1,(survivor_iff rel r root k cs).mp prior.2.1,
      (survivor_iff rel r root j ds).mp prior.2.2⟩
  | deferred => trivial

theorem valid_forward (rel : IndexedView a b) (slices : Semantics a b) (r : Registry)
    (root : Occurrence roles) (x : Inputs (Occurrence roles))
    (prior : Valid (boundary8 roles) r a root x) : Valid (boundary8 roles) r b root x :=
  ⟨reflect_map (pending_iff rel r root) _ prior.rootPending,
    reflect_map (root_k2_iff rel r root) _ prior.rootK2,
    reflect_map (candidate_k2_iff rel r root) _ prior.candidateK2,
    reflect_map (inspection_iff rel r root) _ prior.inspection,
    survivor_forward rel r root _ prior.survivors,
    fun k => reflect_map (output_iff rel r root k) _ (prior.outputConflict k),
    reflect_map (merged_iff rel slices root) _ prior.mergedConflict,
    reflect_map (sharing_iff rel r root) _ prior.sharingConflict⟩

theorem valid_iff (rel : IndexedView a b) (slices : Semantics a b) (r : Registry)
    (root : Occurrence roles) (x : Inputs (Occurrence roles)) :
    Valid (boundary8 roles) r a root x ↔ Valid (boundary8 roles) r b root x :=
  ⟨valid_forward rel slices r root x,valid_forward (reverse rel) slices.symm r root x⟩

end Yulang.GeneralMixedIndexedCompiler305
