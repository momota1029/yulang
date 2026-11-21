import Yulang.GeneralDeclarativeVisibleRecord326
import Yulang.GeneralDeclarativeRecordProducer325

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeFreshTail326
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeRecordResidual323 (withTail prefix_congr reconstruct_with_terminal)
open GeneralDeclarativeVisibleRecord326 (visible_spine)
open GeneralDeclarativeFootprint321 (stateNames preserves_models)
open GeneralDeclarativeTraceNames321 (names)
open GeneralDeclarativeNewNames321 (after supply old_plus_extra)
open GeneralDeclarativeEntailment320 (Entails appendFacts model_append)
open GeneralDeclarativeEqualities322 (Derives entails)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans eqv_symm)
open CommonRoleCanonicalRows (Row residual normalize selected normalize_unique)

inductive Closed : Expr → Prop where
  | width : Closed (.primitive .emptyRecord [])
  | exact : Closed (.primitive .exactEmpty [])

def rhs (raw : Row Expr) (taken : List Nat) (terminal : Expr) : Expr :=
  withTail (residual taken (normalize raw)) terminal

def protect (kept : List Nat) (root : Nat) (raw : Row Expr) (terminal : Expr) : List Nat :=
  root :: (kept ++ names (withTail raw terminal))

def tailRow (s : State) (kept : List Nat) (root : Nat) (raw : Row Expr) (taken : List Nat)
    (terminal : Expr) : Equation :=
  let body := rhs raw taken terminal
  ⟨after ((stateNames s ++ protect kept root raw terminal) ++ [body].flatMap names),body⟩

def extended (s : State) (kept : List Nat) (root : Nat) (raw : Row Expr) (taken : List Nat)
    (terminal : Expr) : State :=
  appendFacts s [tailRow s kept root raw taken terminal]

theorem model_projection (s : State) (kept : List Nat) (root : Nat) (raw : Row Expr)
    (taken : List Nat) (terminal : Expr) (m : Assignment) :
    Models s m ↔ ∃ new, Models (extended s kept root raw taken terminal) new ∧
      ∀ n ∈ stateNames s ++ protect kept root raw terminal, new n = m n := by
  constructor
  · intro fits
    obtain ⟨proved,unchanged⟩ := old_plus_extra s (protect kept root raw terminal) [rhs raw taken terminal] m fits
    exact ⟨_,proved,unchanged⟩
  · rintro ⟨n,fits,keptNames⟩
    exact (preserves_models s (fun name appears => keptNames name (List.mem_append_left _ appears))).mp
      ((model_append n).mp fits).1

/-- Subtract only the written labels from the fully visible closed
spine. The fresh residual name is definitionally exact for either
confirmed terminal style; an unresolved terminal is not accepted here. -/
theorem materialize {s : State} (kept : List Nat) (raw : Row Expr) (written : List Nat)
    (known : Closed terminal) (observed : Derives s (.variable root) (withTail raw terminal)) :
    Entails (extended s kept root raw written terminal)
      ⟨root,withTail (selected written (normalize raw))
        (.variable (tailRow s kept root raw written terminal).left)⟩ := by
  cases known <;>
    intro m valid
  all_goals
    have old := ((model_append m).mp valid).1
    have seen := entails observed m old
    have remainder := valid.2 _ (List.mem_append_right _ List.mem_cons_self)
    exact eqv_trans seen (eqv_trans (visible_spine m _ _) (eqv_trans
      (reconstruct_with_terminal m (normalize raw) written _ (normalize_unique raw))
      (prefix_congr m _ (eqv_symm remainder))))

end Yulang.GeneralDeclarativeFreshTail326
