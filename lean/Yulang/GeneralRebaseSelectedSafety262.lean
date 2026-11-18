import Yulang.GeneralRebaseSelectedFailure262
import Yulang.GeneralRebaseSemanticObserver262
import Yulang.GeneralRebaseQuadraticBudget262

namespace Yulang.GeneralRebaseSelectedSafety262
open GeneralNominalCenters GeneralRebaseStep258
open GeneralSourceState (Output)
open GeneralRebaseSelectedSettle262 (Current run)
open GeneralRebaseObservedPlan262 (observe)
open GeneralRebaseSemanticObserver262 (LayoutCompatible)

theorem no_outside (fixed : Plan roles) (owner : Nat) (pool : List Output)
 (inspect) (roots) (plans) (layout : LayoutCompatible fixed owner pool roots plans)
 (coverage : ∀ state, GeneralRebaseChildRequestPool262.Covered (inspect state) pool)
 (state : Current fixed owner pool) (missing : List Fact) :
 run fixed owner pool inspect roots plans state ≠ .error (.outside missing) := by
 intro failed
 obtain ⟨current,_,_,diagnostic⟩ := GeneralRebaseSelectedFailure262.error_path fixed owner pool inspect roots plans
   state (.outside missing) failed
 have closed : GeneralRebaseClosedObserver259.Closed (observe fixed owner pool inspect roots plans) := by
   rw [GeneralRebaseSemanticObserver262.observe_eq fixed owner pool inspect roots plans layout]
   exact GeneralRebaseCandidateDriver261.closed _ _ _ _
     (GeneralRebaseDynamicSource262.covered fixed owner pool inspect roots coverage)
 exact GeneralRebaseClosedObserver259.next_no_error _ closed current missing diagnostic.2

/-- Every selected-only execution either succeeds or locates a translation
error at a genuinely reached finite-rebase state. No global Ready premise and
no satisfiability or source-language rejection claim are made. -/
theorem outcome (fixed : Plan roles) (owner : Nat) (pool : List Output)
 (inspect) (roots) (plans) (layout : LayoutCompatible fixed owner pool roots plans)
 (coverage : ∀ state, GeneralRebaseChildRequestPool262.Covered (inspect state) pool)
 (before : Current fixed owner pool) :
 (∃ after history, run fixed owner pool inspect roots plans before = .ok after ∧
   GeneralRebaseSelectedSettle262.Trace fixed owner pool inspect roots plans history before after ∧
   history.length ≤ pool.length + pool.length * pool.length) ∨
 (∃ reason current steps, run fixed owner pool inspect roots plans before = .error (.selected reason) ∧
   GeneralRebaseBudget258.Runs (observe fixed owner pool inspect roots plans) steps before current ∧
   steps ≤ pool.length + pool.length * pool.length ∧ reason.root ∈ roots current ∧
   GeneralRebaseClassCheck261.check (plans current reason.root)
     (GeneralRebaseExecutableRequests262.requests (inspect current) reason.root) = .error reason.reason) := by
 cases result : run fixed owner pool inspect roots plans before with
 | ok after =>
   obtain ⟨history,trace⟩ := GeneralRebaseSelectedSettle262.successful_trace fixed owner pool inspect roots plans before after result
   exact Or.inl ⟨after,history,rfl,trace,GeneralRebaseQuadraticBudget262.run_bound fixed owner pool _
     (GeneralRebaseSelectedSettle262.to_runs fixed owner pool inspect roots plans trace)⟩
 | error failure =>
   cases failure with
   | outside missing => exact False.elim (no_outside fixed owner pool inspect roots plans layout coverage before missing result)
   | selected reason =>
     obtain ⟨current,steps,path,_,selected,diagnostic⟩ := GeneralRebaseSelectedFailure262.selected_provenance
       fixed owner pool inspect roots plans before reason result
     exact Or.inr ⟨reason,current,steps,rfl,path,GeneralRebaseQuadraticBudget262.run_bound fixed owner pool _ path,
       selected,diagnostic⟩
end Yulang.GeneralRebaseSelectedSafety262
