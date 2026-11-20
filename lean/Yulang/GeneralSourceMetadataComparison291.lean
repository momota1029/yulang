import Yulang.GeneralSourceMetadataFresh291

/-! Decide old Metadata from attached finite source descriptions. Unlike a
local stamp, this compares every possible value of this encoding by using
its explicit defaults and a witnessed residual. -/
namespace Yulang.GeneralSourceMetadataComparison291
open GeneralSourceMetadataRows291
open GeneralSourceMetadataExport291 (exportPair Attached completed_check_iff)
open GeneralSourceMetadataFresh291 (freshKey different_table_at_fresh equal_table_implies_same_code)
open GeneralDeclarations (Registry)
open GeneralNominalCandidates (Context Metadata)
open GeneralObservedMetadataScope290 (certify)

structure Linked (s t : Source) (r : Registry) (ctx : Context) : Prop where
  declaredCorrect : r.constructors = constructors s
  snapshotCorrect : ctx.state.constructors = constructors t
  interpretationCorrect : ctx.interpretation = interpretation t

inductive Result where
  | fallbackMismatch (witness : Nat)
  | compared (code : GeneralObservedMetadataScope290.Result)
  deriving DecidableEq, Repr

def compare (s t : Source) (scope : List Nat) : Result :=
  if s.fallback = t.fallback then
    .compared (certify ((exportPair s t).extended scope) (constructors s) (interpretation t)
      (constructors t) (interpretation t))
  else .fallbackMismatch (freshKey s t)

theorem no_metadata_if_different {s t : Source} {r : Registry} {ctx : Context}
    (link : Linked s t r ctx) (unequal : s.fallback ≠ t.fallback) : ¬ Metadata r ctx := by
  intro valid
  have exactTable := congrFun valid.1 (freshKey s t)
  rw [link.declaredCorrect,link.snapshotCorrect] at exactTable
  exact different_table_at_fresh s t unequal exactTable

theorem exact_linked_metadata {s t : Source} {r : Registry} {ctx : Context}
    (link : Linked s t r ctx) (scope : List Nat) :
    compare s t scope = .compared .good ↔ Metadata r ctx := by
  unfold compare
  by_cases common : s.fallback = t.fallback
  · rw [ite_eq_left common]
    have attached : Attached s t r ctx :=
      ⟨common,link.declaredCorrect,link.snapshotCorrect,link.interpretationCorrect⟩
    have equivalence := completed_check_iff attached scope
    rw [link.declaredCorrect,link.snapshotCorrect,link.interpretationCorrect] at equivalence
    exact ⟨fun valid => equivalence.mpr (Result.compared.inj valid),
      fun valid => congrArg Result.compared (equivalence.mp valid)⟩
  · rw [ite_eq_right common]
    constructor
    · intro impossible; cases impossible
    · intro valid; exact (no_metadata_if_different link common valid).elim

theorem concrete_disagreement (s t : Source) (scope : List Nat) (key : Nat)
    (bad : compare s t scope = .fallbackMismatch key) : constructors s key ≠ constructors t key := by
  unfold compare at bad
  by_cases matched : s.fallback = t.fallback
  · rw [ite_eq_left matched] at bad
    cases bad
  · rw [ite_eq_right matched] at bad
    cases Result.fallbackMismatch.inj bad
    exact different_table_at_fresh s t matched

end Yulang.GeneralSourceMetadataComparison291
