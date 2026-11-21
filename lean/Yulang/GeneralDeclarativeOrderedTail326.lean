import Yulang.GeneralDeclarativeOrderedRecord326

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeOrderedTail326
open CommonRoleCanonicalRows (Row normalize selected residual normalize_unique)
open GeneralDeclarativeOrderedRecord326 (order exact_order lookup_unique to_permutation)
open GeneralDeclarativeRecordResidual323 (withTail permute_fields)
open GeneralDeclarativeRecordHead323 (selected_nodup)
open GeneralDeclarativeFreshTail326 (Closed tailRow extended materialize)
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeEqualities322 (Derives)
open GeneralDeclarativeEntailment320 (Entails)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans)

theorem known_labels {row : Row α} {keys : List Nat}
    (separate : (row.map Prod.fst).Nodup)
    (present : ∀ key ∈ keys, key ∈ row.map Prod.fst) :
    ∃ printed, order row keys = some printed := by
  induction keys with
  | nil => exact ⟨[],rfl⟩
  | cons key rest ih =>
    obtain ⟨⟨k,e⟩,found,same⟩ := List.mem_map.mp (present key List.mem_cons_self)
    change k = key at same
    subst k
    obtain ⟨tail,read⟩ := ih (fun k h => present k (List.mem_cons_of_mem _ h))
    exact ⟨(key,e)::tail,by simp [order,lookup_unique separate found,read]⟩

theorem read_iff {row : Row α} {keys : List Nat} (separate : (row.map Prod.fst).Nodup) :
    (∃ printed, order row keys = some printed) ↔ ∀ key ∈ keys, key ∈ row.map Prod.fst := by
  constructor
  · rintro ⟨printed,known⟩ key used
    obtain ⟨labels,rows⟩ := exact_order separate known
    rw [← labels] at used
    obtain ⟨entry,there,rfl⟩ := List.mem_map.mp used
    exact List.mem_map.mpr ⟨entry,((rows entry).mp there).1,rfl⟩
  · exact known_labels separate

/-- A concrete closed spine can be read in declaration order, after
first-field normalization and actual subtraction of the written labels.
The new tail stands for the same residual even if written order differs
from the ordinary source row order. Missing labels are not invented. -/
theorem actual_decl_order {s : State} (kept : List Nat) (raw : Row Expr)
    (labelOrder : keys.Nodup) (read : order (normalize raw) keys = some printed)
    (terminalKnown : Closed terminal)
    (visibleActual : Derives s (.variable root) (withTail raw terminal)) :
    Entails (extended s kept root raw keys terminal)
      ⟨root,withTail printed (.variable (tailRow s kept root raw keys terminal).left)⟩ := by
  intro m valid
  have bySource := materialize kept raw keys terminalKnown visibleActual m valid
  have layout := to_permutation labelOrder read
  have d := selected_nodup (normalize raw) keys (normalize_unique raw)
  exact eqv_trans bySource (permute_fields m _ layout d)

end Yulang.GeneralDeclarativeOrderedTail326
