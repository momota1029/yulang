import Yulang.GeneralRebaseCandidateChecks267

namespace Yulang.GeneralRebaseCandidatePrepared267
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalCenters (Plan)
open GeneralNominalVersionedJournal232 (State Effect)
open GeneralNominalVersionedCandidates231 (inputs Prepared HeadModels)
open GeneralNominalRecursiveCandidates (Metadata arguments report)
open GeneralNominalRecursiveInspection (bindings Finished)
open GeneralRebaseCandidateChecks267 (linked linked_exact allKnown allKnown_exact fresh fresh_exact finished finished_exact)
open GeneralRebaseCandidatePlan267 (DeclChecked Shell)
open GeneralRebaseEnumeratePlans267 (plans plans_exact includes_install)

def preflight (plan : Plan roles) : Bool :=
 let packet := plan.packet
 let focus := packet.site.occurrence
 let context := packet.context
 let observed := report context packet.declaration packet.bounds
 linked context.state (inputs focus).demand &&
  (fresh context.state packet.registry focus.identity (bindings context.state observed) &&
   finished observed)

theorem preflight_exact (plan : Plan roles) :
 preflight plan = true ↔
 GeneralNominalState.Linked plan.packet.context.state (inputs plan.packet.site.occurrence).demand ∧
 GeneralNominalVersionedAllocation231.Fresh plan.packet.context.state plan.packet.registry
   plan.packet.site.occurrence.identity (bindings plan.packet.context.state (report plan.packet.context plan.packet.declaration plan.packet.bounds)) ∧
 Finished (report plan.packet.context plan.packet.declaration plan.packet.bounds) := by
 simp only [preflight,Bool.and_eq_true,linked_exact,fresh_exact,finished_exact]

def headCondition (plan : Plan roles) : Prop :=
 ∃ model, HeadModels plan.packet.registry plan.packet.context plan.packet.site.occurrence plan.packet.declaration plan.packet.bounds model

theorem prepared_iff (registry : Registry) (state : State roles) (root : Occurrence roles)
 (plan : Plan roles) (shell : Shell registry state root plan) :
 Prepared registry state.core.erased.current.context plan.packet.site.occurrence plan.packet.declaration ↔
 Metadata registry state.core.erased.current.context ∧ preflight plan = true ∧ headCondition plan := by
 rw [preflight_exact,headCondition,←shell.registry_eq,←shell.context_eq]
 constructor
 · rintro ⟨metadata,linked,bounds,found,fresh,finished,model,holds⟩
   have same := Option.some.inj (found.symm.trans shell.located)
   subst bounds
   exact ⟨metadata,⟨linked,fresh,finished⟩,model,holds⟩
 · rintro ⟨metadata,⟨linked,fresh,finished⟩,model,holds⟩
   exact ⟨metadata,linked,plan.packet.bounds,shell.located,fresh,finished,model,holds⟩

def readyPlans (registry : Registry) (state : State roles) (root : Occurrence roles)
 (checked : DeclChecked registry roles) : List (Plan roles) :=
 (plans registry state root checked).filter fun plan =>
  allKnown state.core.erased.current.context.state (inputs plan.packet.site.occurrence).demand && preflight plan

theorem ready_exact (registry : Registry) (state : State roles) (root : Occurrence roles)
 (checked : DeclChecked registry roles) (plan : Plan roles) :
 plan ∈ readyPlans registry state root checked ↔
 Shell registry state root plan ∧
 ¬ GeneralNominalState.RootPending state.core.erased.current.context.state (inputs plan.packet.site.occurrence).demand ∧
 preflight plan = true := by
 simp only [readyPlans,List.mem_filter,plans_exact,Bool.and_eq_true,allKnown_exact]

theorem includes_real_install (registry : Registry) (state : State roles) (root : Occurrence roles)
 (checked : DeclChecked registry roles) (effect : Effect roles)
 (generated : GeneralNominalSaturationState.Generated state.core.erased.current root effect.plan.packet.site.occurrence)
 (guard : GeneralNominalVersionedMixedKernel234.Installable registry state effect) :
 effect.plan ∈ readyPlans registry state root checked := by
 have shell := (plans_exact ..).mp (includes_install registry state root checked effect generated guard)
 have prepared := effect.frame.prepared
 have notPending := effect.unique.1.1
 rw [guard.registry_eq,guard.snapshot_eq] at prepared
 rw [guard.snapshot_eq] at notPending
 exact (ready_exact ..).mpr ⟨shell,notPending,((prepared_iff registry state root effect.plan shell).mp prepared).2.1⟩

end Yulang.GeneralRebaseCandidatePrepared267
