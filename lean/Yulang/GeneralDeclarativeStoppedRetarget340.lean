import Yulang.GeneralDeclarativeStoppedLeaf340
import Yulang.GeneralRebaseDepthHaltSelection285
import Yulang.GeneralNominalVersionedMixedCommon235

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 31000
set_option maxHeartbeats 12500000
namespace Yulang.GeneralDeclarativeStoppedRetarget340
open GeneralDictionaryOutputDepth252 (registry sourceRegistry roles root declaration model initial initial_source source_checked)
open GeneralDictionaryOutputDepthInstall252 (installed)
open GeneralRebaseDepthScalar285 (refreshed target actual_followup)
open GeneralRebaseDepthCommit285 (finalPlan classes committed)
open GeneralRebaseDepthHalt285 (halted)
open GeneralRebaseDepthHaltEvidence285 (final_frame final_ready final_children)
open GeneralRebaseDepthHaltSelection285 (unique selected after_model)
open GeneralNominalVersionedMixedKernel234 (Installable)
open GeneralNominalVersionedJournal232 (Models Effect)
open GeneralNominalVersionedEvidence231 (Evidence)
open GeneralNominalCenteredHeadOutputs (requests)
open GeneralDeclarativeStoppedLeaf340 (same_model_leaf current_outputs projected_outputs)
open GeneralDeclarativeStoppedProjection340 (project append)
open GeneralStoppedProjectedTrace335 (current)
open GeneralDeclarativeStoppedOrder339 (compileRequests)
open GeneralDeclarativeHead320 (Equation)
open GeneralSourceState (Output)
open GeneralNominalCommonBridge (Assignment)

noncomputable def candidate : Effect roles :=
  ⟨registry,refreshed.core,finalPlan,final_frame,final_children.symm ▸ unique,final_ready⟩

theorem reach :
    B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) sourceRegistry root refreshed :=
  ⟨initial,initial_source,actual_followup⟩

theorem choose_prior :
    GeneralNominalCycleSteps.ChoiceCompatible refreshed.core.erased.current finalPlan.packet := by
  intro prior inJournal _
  change prior ∈ [GeneralDictionaryOutputDepth252.plan.packet] at inJournal
  cases List.mem_singleton.mp inJournal
  rfl

theorem installable : Installable registry refreshed candidate :=
  (GeneralNominalVersionedMixedCommon235.source_installable_iff ⟨rfl,source_checked⟩ reach selected
    (effect := candidate) rfl rfl).mpr ⟨choose_prior,model,after_model,(committed.1 model after_model).1,classes model after_model⟩

theorem initial_zero_unknown : ¬ GeneralNominalState.Known GeneralDictionaryOutputDepth252.snapshot 0 := by
  rintro ⟨slot,loc,head | ⟨desc,recorded⟩⟩
  · exact head rfl
  · change slot.val = 0 at loc
    have same : slot = (0 : Fin 4) := Fin.ext loc
    cases same
    cases recorded

theorem recorded_source_distinct :
    candidate.plan.packet.context ≠ GeneralDictionaryOutputDepth252.plan.packet.context := by
  intro eq
  change target = GeneralDictionaryOutputDepth252.context at eq
  have eqState : target.state = GeneralDictionaryOutputDepth252.snapshot := congrArg GeneralNominalCandidates.Context.state eq
  exact initial_zero_unknown (by rw [← eqState]; exact GeneralRebaseDepthScalar285.new_zero)

theorem current_plan_not_retained : ∀ e ∈ refreshed.effects, e.plan ≠ candidate.plan := by
  intro e present same
  change e ∈ [GeneralDictionaryOutputDepthInstall252.effect] at present
  cases List.mem_singleton.mp present
  exact recorded_source_distinct (congrArg (fun p => p.packet.context) same.symm)

abbrev exactOut : Output := ⟨0,3⟩
noncomputable def row : Equation := ⟨3,.nominal 0 [.nominal 0 [.variable (finalPlan.binder 0)]]⟩

theorem only_site_requests {s : GeneralNominalCenteredSteps.State roles}
    {focus : GeneralSourceDictionaries.Occurrence roles} {site : GeneralNominalDemandMerging.Site roles}
    (known : s.erased.current.sites = [site])
    (linked : GeneralNominalSaturationState.Alias s.erased.current focus.identity site.occurrence.identity) :
    requests s focus = site.occurrence.demand.outputs := by
  unfold requests
  rw [known]
  simp [linked]

theorem exact_requests : requests refreshed.core root = [exactOut] := by
  exact only_site_requests GeneralRebaseDepthCommit285.raw_sites (.refl _)

theorem exact_packet : compileRequests finalPlan (requests refreshed.core root) = some [row] := by rw [exact_requests]; rfl

/-- Actual reached selected halt with a request-bearing record. The
current retargeted plan is not the historical installed plan. The
un-journaled *current plan* nonetheless carries the exact fixed
target 3 in every same raw model. -/
theorem exact_stopped_current (m : Assignment) (fit : Models refreshed m) :
    Evidence registry refreshed.core m root (.node 0 []) ∧
      GeneralDeclarativeEntailment320.Holds m row ∧ row.left = 3 := by
  obtain ⟨rows,which,_,_,every⟩ := current_outputs halted .root installable m fit
  have equal : rows = [row] := Option.some.inj (which.symm.trans exact_packet)
  subst rows
  exact ⟨same_model_leaf halted .root installable final_children m fit,
    every _ List.mem_cons_self,rfl⟩

theorem projected : ∃ view, project (current refreshed) = some view := by
  have has : (project (current refreshed)).isSome = true := by decide +kernel
  cases h : project (current refreshed) with
  | none => rw [h] at has; cases has
  | some view => exact ⟨view,rfl⟩

theorem output_with_actual_view : ∃ v, project (current refreshed) = some v ∧
    ∀ m, Models refreshed m → GeneralDeclarativeStoppedProjection340.Models (append v [row]) m := by
  obtain ⟨v,ok⟩ := projected
  refine ⟨v,ok,?_⟩
  intro m fits
  obtain ⟨rows,printed,_,read⟩ := projected_outputs halted .root installable ok m fits
  cases Option.some.inj (printed.symm.trans exact_packet)
  exact read

end Yulang.GeneralDeclarativeStoppedRetarget340
