import Yulang.GeneralNominalValueDepth
import Yulang.GeneralNominalBudgetObservation

/-! Certified observation-only changes do not increase support depth. The
finite closure includes both refresh and descriptor replacement. Installations
and merges change the dependency journal and are deliberately not covered. -/
namespace Yulang.GeneralNominalValueObservation
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalValueSupport GeneralNominalValueDepth

variable {roles : Roles.RoleDecls}

open GeneralNominalBudgetObservation (SameJournal view_journal view_trans discharge_transport waiting_transport)

theorem proper_transport (same : SameJournal before after)
    (path : ProperWaiting before producer child) : ProperWaiting after producer child := by
  obtain ⟨parent,first,waiting,edge,unresolved,rest⟩ := path
  exact ⟨parent,first,waiting_transport same waiting,same.edges ▸ edge,
    fun done => unresolved (discharge_transport same.symm done),waiting_transport same rest⟩

/-- The pre-view guard already quantifies over every later certified view. -/
theorem need_before (state : Tracked roles) (view : View state.current after)
    (needed : Need registry {state with current := after} producer focus identity test) :
    Need registry state producer focus identity test := by
  cases needed with
  | head old => exact .head (GeneralNominalBudgetObservation.need_before state view old)
  | value proper observed more index path test available =>
    exact .value (proper_transport (view_journal view).symm proper) observed (view_trans view more) index path test available
  | retained proper observed more site member same position origin recorded source realizes path test available =>
    exact .retained (proper_transport (view_journal view).symm proper) observed (view_trans view more) site member same position origin recorded source realizes path test available

theorem depth_nonincreasing (state : Tracked roles) (view : View state.current after)
    (known : AtDepth registry state depth producer) :
    AtDepth registry {state with current := after} depth producer := by
  have journal := view_journal view
  induction depth generalizing producer with
  | zero => exact discharge_transport journal known
  | succ depth ih =>
    rcases known with done | heads
    · exact Or.inl (discharge_transport journal done)
    · refine Or.inr ?_
      intro child path unresolved identity test needed
      have oldPath := waiting_transport journal.symm path
      have oldOpen : ¬ Discharged state.current child := fun done => unresolved (discharge_transport journal done)
      obtain ⟨support,entailed,smaller⟩ := heads child oldPath oldOpen identity test (need_before state view needed)
      exact ⟨support,entailed,fun dependency member => ih (smaller dependency member)⟩

theorem grounded_preserved (state : Tracked roles) (view : View state.current after)
    (grounded : Grounded registry state producer) : Grounded registry {state with current := after} producer := by
  obtain ⟨depth,known⟩ := grounded_depth grounded
  exact depth_grounded (depth_nonincreasing state view known)

/-- In particular both currently implemented observation update constructors
preserve every prior depth certificate, without a source-size premise. -/
theorem refresh_depth (state : Tracked roles) (context : GeneralNominalCandidates.Context)
    (certificate : GeneralNominalFeedbackSteps.Refresh state.current context)
    (known : AtDepth registry state depth producer) :
    AtDepth registry {state with current := regenerate state.current context} depth producer :=
  depth_nonincreasing state (.refresh .current certificate) known

theorem revision_depth (state : Tracked roles) (revision : GeneralNominalReobservationSteps.Revision state.current)
    (certificate : GeneralNominalReobservationSteps.Certified revision)
    (known : AtDepth registry state depth producer) :
    AtDepth registry {state with current := revision.result} depth producer :=
  depth_nonincreasing state (.reobserve revision .current certificate) known

theorem head_depth_nonincreasing (state : Tracked roles) (view : View state.current after)
    (known : HeadDepth registry state depth identity test) :
    HeadDepth registry {state with current := after} depth identity test := by
  obtain ⟨support,head,producers⟩ := known
  exact ⟨support,head,fun producer member => depth_nonincreasing state view (producers producer member)⟩

end Yulang.GeneralNominalValueObservation
