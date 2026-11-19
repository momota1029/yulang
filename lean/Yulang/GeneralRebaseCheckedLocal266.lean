import Yulang.GeneralRebaseCheckedProjection266
import Yulang.GeneralRebaseSourceInstallProjection264
import Yulang.GeneralRebaseAffectedMerge264

namespace Yulang.GeneralRebaseCheckedLocal266
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalCenters (Site)
open GeneralNominalVersionedJournal232 (State Effect)
open GeneralNominalVersionedMixedKernel234 (Installable)
open GeneralRebaseStep258 (Fact)
open GeneralRebaseCheckedProjection266 (checked_square)
open GeneralRebaseCheckedWrite259 (commit)
open GeneralRebaseLiveProjection264 (liveFacts facts project)
open GeneralRebaseMultiSelection263 (ofPlan proposal)
open GeneralSourceState (Output)

abbrev FiniteBasis (owners : List Nat) (pool : List Output) :=
 GeneralRebaseUniversalBasis263.basis owners pool

theorem install_proposal_in_live (registry : Registry)
 (checked : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Checked registry)
 (root : Occurrence roles) (state : State roles)
 (reachable : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state)
 (effect : Effect roles)
 (enabled : Installable (GeneralNominalCenteredHeadAllocEncoding.registry registry) state effect) :
 proposal state.core (ofPlan effect.plan) ⊆ liveFacts (GeneralNominalVersionedInstall232.install state effect) := by
 intro fact proposed
 apply (GeneralRebaseSourceInstallProjection264.liveFacts_exact registry checked root state reachable effect enabled fact).mpr
 exact Or.inl ((GeneralRebaseSourceInstallProjection264.current_proposal registry checked root state reachable effect enabled fact).mpr proposed)

theorem checked_install (registry : Registry)
 (checked : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Checked registry)
 (root : Occurrence roles) (state : State roles)
 (reachable : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state)
 (effect : Effect roles)
 (enabled : Installable (GeneralNominalCenteredHeadAllocEncoding.registry registry) state effect)
 (owners : List Nat) (pool : List Output)
 (closed : liveFacts (GeneralNominalVersionedInstall232.install state effect) ⊆ FiniteBasis owners pool) :
 let before := project owners pool state
 let after := project owners pool (GeneralNominalVersionedInstall232.install state effect)
 commit before (proposal state.core (ofPlan effect.plan)) =
 .ok (if after.remaining = before.remaining then none else some after) :=
 checked_square _ _ _ (GeneralRebaseSourceInstallProjection264.project_install_current registry checked root state reachable effect enabled owners pool)
   (fun _ member => closed (install_proposal_in_live registry checked root state reachable effect enabled member))

def affectedProposal (state : State roles) (first last : Site roles) : List Fact :=
 facts (GeneralNominalVersionedAdministrative232.merge state first last).core
    (GeneralRebaseAffectedMerge264.plans state first last)

theorem merge_proposal_in_live (state : State roles) (first last : Site roles) :
 affectedProposal state first last ⊆
   liveFacts (GeneralNominalVersionedAdministrative232.merge state first last) := by
 intro fact member
 exact (GeneralRebaseAffectedMerge264.liveFacts_split state first last fact).mpr (Or.inr member)

theorem checked_merge (state : State roles) (first last : Site roles)
 (owners : List Nat) (pool : List Output)
 (closed : liveFacts (GeneralNominalVersionedAdministrative232.merge state first last) ⊆ FiniteBasis owners pool) :
 let before := project owners pool state
 let after := project owners pool (GeneralNominalVersionedAdministrative232.merge state first last)
 commit before (affectedProposal state first last) =
 .ok (if after.remaining = before.remaining then none else some after) :=
 checked_square _ _ _ (GeneralRebaseAffectedMerge264.project_merge owners pool state first last)
  (fun _ member => closed (merge_proposal_in_live state first last member))

end Yulang.GeneralRebaseCheckedLocal266
