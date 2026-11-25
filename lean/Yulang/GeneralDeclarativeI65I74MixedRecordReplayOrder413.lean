import Yulang.GeneralDeclarativeI65I74MixedRecordCoherence413

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.MixedRecord413
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open RecordK2412 (checkCycleAt412)
open Checker408 (Problem Result)

theorem exact_full_replay_guard413 (p : Problem) (w : MixedWire) (o : VerifiedOuter p)
    (root : rootRead413 p w.root = some o) :
    (replayMixed413 p w).isSome =
      ((decide (2 ≤ (visible p.state.core p.root).length) &&
        decide (((visible p.state.core p.root).map Declaration.id).Nodup)) &&
      decide (foldedFlags413 o.actual (visible p.state.core p.root) = .oneOpening) &&
      checkCycleAt412 p.state.core.current.ordinary o.actual.site w.path) := by
  rw [← full_scan_flags_exact413]
  unfold replayMixed413
  rw [root]
  by_cases count : 2 ≤ (visible p.state.core p.root).length
  · by_cases distinct : ((visible p.state.core p.root).map Declaration.id).Nodup
    · cases scanned : scanAll413 o.actual (visible p.state.core p.root) with
      | none => simp [count,distinct,scanned,shapeFlag413]
      | some description =>
        cases description with
        | plain => simp [count,distinct,scanned,shapeFlag413]
        | mixed tape =>
          cases cycle : checkCycleAt412 p.state.core.current.ordinary o.actual.site w.path <;>
            simp [count,distinct,scanned,shapeFlag413,cycle]
    · simp [count,distinct]
  · simp [count]

theorem fold_row_flags_from_same_reads413 {s q t r}
    (a : ActualOuterRecord s q) (b : ActualOuterRecord t r) (rows : List Declaration)
    (matchRows : ∀ row ∈ rows, rowFlag413 a row = rowFlag413 b row) :
    foldedFlags413 a rows = foldedFlags413 b rows := by
  induction rows with
  | nil => rfl
  | cons row rest next =>
    simp only [foldedFlags413]
    rw [matchRows _ List.mem_cons_self, next (fun d known => matchRows d (List.mem_cons_of_mem _ known))]

/-- End-to-end (rather than just the list fold): whenever the two
inputs read the same metadata per original declaration and verify
the same real field cycle, reordering the complete visible list
leaves the checked verdict unchanged. The checker still retains
each input's own ordinal in its evidence. This does not require
the two original Problem states to be literally identical. -/
theorem check_is_order_independent_for_same_source_reads413
    (p q : Problem) (r : Result) (w u : MixedWire)
    (a : VerifiedOuter p) (b : VerifiedOuter q)
    (readP : rootRead413 p w.root = some a) (readQ : rootRead413 q u.root = some b)
    (permutation : (visible p.state.core p.root).Perm (visible q.state.core q.root))
    (metadata : ∀ row ∈ visible p.state.core p.root, rowFlag413 a.actual row = rowFlag413 b.actual row)
    (cycle : checkCycleAt412 p.state.core.current.ordinary a.actual.site w.path =
      checkCycleAt412 q.state.core.current.ordinary b.actual.site u.path) :
    check p r (.mixedHead w) = check q r (.mixedHead u) := by
  have sameFlags := (fold_row_flags_from_same_reads413 a.actual b.actual _ metadata).trans
    (folded_flags_independent_of_order413 b.actual permutation)
  have sameIds := (permutation.map Declaration.id).nodup_iff
  have sameDistinct :
      decide (((visible p.state.core p.root).map Declaration.id).Nodup) =
        decide (((visible q.state.core q.root).map Declaration.id).Nodup) :=
    Bool.eq_iff_iff.mpr (by simpa using sameIds)
  simp only [check,exact_full_replay_guard413 p w a readP,exact_full_replay_guard413 q u b readQ]
  rw [permutation.length_eq,sameDistinct,sameFlags,cycle]

end Yulang.GeneralDeclarativeI65.I72.MixedRecord413
