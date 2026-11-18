import Yulang.GeneralRebaseStableMergeFinish261
namespace Yulang.GeneralRebaseSourceSnapshot261
open GeneralNominalCenters GeneralRebaseStep258
open GeneralSourceState (Output)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalCommonBridge (Assignment)

/-- Executable finite request overapproximation of one existing source
snapshot. No alias decision and no unfolding of private types is needed. -/
def candidates (source : GeneralNominalCenteredSteps.State roles) : List Output :=
 source.erased.current.sites.flatMap fun site => site.occurrence.demand.outputs

theorem covered (source : GeneralNominalCenteredSteps.State roles) (root : Occurrence roles) :
 ∀ output ∈ GeneralNominalCenteredHeadOutputs.requests source root, output ∈ candidates source := by
 intro output included
 obtain ⟨site,member,_,within⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp included
 exact List.mem_flatMap.mpr ⟨site,member,within⟩

noncomputable def select (source : GeneralNominalCenteredSteps.State roles) (plan : Plan roles) (owner : Nat)
 (roots : State (GeneralRebaseStableClass261.facts plan owner (candidates source)) → List (Occurrence roles))
 (state : State (GeneralRebaseStableClass261.facts plan owner (candidates source))) :=
 (roots state).map (GeneralNominalCenteredHeadOutputs.requests source)

theorem all_covered (source : GeneralNominalCenteredSteps.State roles) (plan : Plan roles) (owner : Nat) (roots) :
 GeneralRebaseCandidateDriver261.Covered plan owner (candidates source) (select source plan owner roots) := by
 intro state outputs member
 obtain ⟨root,_,rfl⟩ := List.mem_map.mp member
 exact covered source root

theorem completion (source : GeneralNominalCenteredSteps.State roles) (plan : Plan roles) (owner : Nat) (roots)
 (state : State (GeneralRebaseStableClass261.facts plan owner (candidates source))) :
 ∃ final steps, GeneralRebaseSettle259.settle
 (GeneralRebaseCandidateDriver261.observe plan owner (candidates source) (select source plan owner roots)) state = .ok final ∧
 GeneralRebaseBudget258.Runs (GeneralRebaseCandidateDriver261.observe plan owner (candidates source) (select source plan owner roots)) steps state final ∧
 steps ≤ state.remaining.length ∧
 (∀ after, ¬ Step (GeneralRebaseCandidateDriver261.observe plan owner (candidates source) (select source plan owner roots)) final after) :=
 GeneralRebaseCandidateDriver261.completion _ _ _ _ (all_covered source plan owner roots) state

/-- Every successful write has the exact current-snapshot ClassEffects of an
actually selected root. Frame/Prepared and packet correctness are not assumed
or concluded by this constraint-table theorem. -/
theorem step_actual (base : Assignment → Prop) (source : GeneralNominalCenteredSteps.State roles)
 (plan : Plan roles) (owner : Nat) (roots)
 (before after : State (GeneralRebaseStableClass261.facts plan owner (candidates source)))
 (step : Step (GeneralRebaseCandidateDriver261.observe plan owner (candidates source) (select source plan owner roots)) before after) :
 ∃ root ∈ roots before, ∀ assignment,
 GeneralRebaseStableClass261.Models base plan owner after assignment ↔
 GeneralRebaseStableClass261.Models base plan owner before assignment ∧
 GeneralNominalVersionedEffects231.ClassEffects source root plan assignment := by
 obtain ⟨proposal,member,rfl,_⟩ := step
 obtain ⟨outputs,selected,rfl⟩ := List.mem_map.mp member
 obtain ⟨root,included,rfl⟩ := List.mem_map.mp selected
 exact ⟨root,included,fun assignment => GeneralRebaseStableClass261.actual_write base plan owner source root
   (candidates source) (covered source root) before assignment⟩

/-- Initializing a new basis at each snapshot is not a proof that one basis
covers a changing source trace. This module intentionally freezes source. -/
theorem initial_models (base : Assignment → Prop) (source : GeneralNominalCenteredSteps.State roles)
 (plan : Plan roles) (owner : Nat) (assignment : Assignment) :
 GeneralRebaseStableClass261.Models base plan owner (initial (GeneralRebaseStableClass261.facts plan owner (candidates source))) assignment ↔
 base assignment := GeneralRebaseFactSemantics259.initial_exact ..
end Yulang.GeneralRebaseSourceSnapshot261
