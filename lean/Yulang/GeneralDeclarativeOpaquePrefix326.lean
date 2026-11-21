import Yulang.GeneralDeclarativeOrderedTail326
import Yulang.GeneralDeclarativeForwardHead325

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeOpaquePrefix326
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeEqualities322 (Derives entails)
open GeneralDeclarativeEntailment320 (Entails model_append)
open GeneralDeclarativeVisibleRecord326 (visible_spine)
open GeneralDeclarativeRecordResidual323 (withTail reconstruct_with_terminal prefix_congr permute_fields)
open GeneralDeclarativeFreshTail326 (tailRow extended model_projection)
open GeneralDeclarativeOrderedRecord326 (order to_permutation)
open GeneralDeclarativeRecordHead323 (selected_nodup)
open CommonRoleCanonicalRows (Row normalize normalize_unique selected)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans eqv_symm)
open GeneralDeclarativeTermWalk322 (Walk Binds)
open GeneralDeclarativeCompileLists321 (Result)
open GeneralDeclarativeNFHead324 (fact)
open GeneralDeclarationPatterns (normalize)

/-- Reorder explicitly known fields while preserving the identical
opaque terminal term. This is a reconstruction identity, not a
complete-label test, a deletion inside the terminal, or authority to
observe any constructor from the new tail name. -/
theorem reconstruct_visible {s : State} (kept : List Nat) (raw : Row Expr)
    (labelOrder : keys.Nodup)
    (read : order (CommonRoleCanonicalRows.normalize raw) keys = some printed)
    (ordinary : Derives s (.variable root) (withTail raw terminal)) :
    Entails (extended s kept root raw keys terminal)
      ⟨root,withTail printed (.variable (tailRow s kept root raw keys terminal).left)⟩ := by
  intro m valid
  have opened := entails ordinary m ((model_append m).mp valid).1
  have residual := valid.2 _ (List.mem_append_right _ List.mem_cons_self)
  change GeneralDeclarativeRepeatedActual323.eqAt m
    (.variable (tailRow s kept root raw keys terminal).left)
    (withTail (CommonRoleCanonicalRows.residual keys (CommonRoleCanonicalRows.normalize raw)) terminal) at residual
  have selectedOrder := to_permutation labelOrder read
  have unique := selected_nodup (CommonRoleCanonicalRows.normalize raw) keys (normalize_unique raw)
  exact eqv_trans opened (eqv_trans (visible_spine m _ _) (eqv_trans
    (reconstruct_with_terminal m (CommonRoleCanonicalRows.normalize raw) keys _ (normalize_unique raw))
    (eqv_trans (prefix_congr m _ (eqv_symm residual)) (permute_fields m _ selectedOrder unique))))

theorem visible_head {s : State} (kept : List Nat) (raw : Row Expr) (arg : Capture)
    (labelOrder : keys.Nodup)
    (read : order (CommonRoleCanonicalRows.normalize raw) keys = some printed)
    (ordinary : Derives s (.variable arg.center) (withTail raw terminal))
    (source : translate c i (normalize pat) = some code)
    (walk : Walk .actual (withTail printed (.variable (tailRow s kept arg.center raw keys terminal).left))
      code links)
    (captures : Binds (extended s kept arg.center raw keys terminal) cap links) :
    Result (extended s kept arg.center raw keys terminal) (fact c i cap arg pat) :=
  GeneralDeclarativeForwardHead325.by_walk source
    (reconstruct_visible kept raw labelOrder read ordinary) walk captures

/-- When every visible field is written, the residual is exactly the old
opaque terminal expression; not a new width/exact-empty constant. -/
theorem no_visible_residue {s : State} (kept : List Nat) (raw : Row Expr) (root : Nat)
    (allWritten : ∀ pair ∈ CommonRoleCanonicalRows.normalize raw, pair.1 ∈ keys) :
    (tailRow s kept root raw keys terminal).right = terminal := by
  have empty : CommonRoleCanonicalRows.residual keys (CommonRoleCanonicalRows.normalize raw) = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro e stored
    have present := List.mem_filter.mp stored
    have taken := allWritten e present.1
    simp at present
    exact present.2 taken
  change withTail (CommonRoleCanonicalRows.residual keys (CommonRoleCanonicalRows.normalize raw)) terminal = terminal
  rw [empty]
  rfl

end Yulang.GeneralDeclarativeOpaquePrefix326
