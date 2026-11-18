import Yulang.GeneralRebaseUniversalSource263
import Yulang.GeneralNominalVersionedMixedPlanLedger235
namespace Yulang.Cycle263InitialBoundary
open GeneralRebaseUniversalObserver263
open GeneralRebaseMultiSource263 (selected)

theorem initial_selected_empty (registry : GeneralDeclarations.Registry)
 (root : GeneralSourceDictionaries.Occurrence roles) (start : GeneralNominalVersionedJournal232.State roles)
 (source : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Initial registry root start) :
 selected start = [] := by
 obtain ⟨legacy,_,rfl⟩ := source
 rfl

/-- A registered-only selector does not discover the first prospective Plan.
This identifies an open source-machine bridge, not a language rejection rule. -/
theorem initial_inspector_noop (registry : GeneralDeclarations.Registry)
 (root : GeneralSourceDictionaries.Occurrence roles) (start : GeneralNominalVersionedJournal232.State roles)
 (source : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Initial registry root start)
 (owners : List Nat) (pool : List GeneralSourceState.Output)
 (inspect : Current owners pool → GeneralNominalVersionedJournal232.State roles)
 (before : Current owners pool) (at_initial : inspect before = start) :
 run owners pool (fun state => (inspect state).core) (fun state => selected (inspect state)) before = .ok before := by
 have empty : selected (inspect before) = [] := at_initial ▸ initial_selected_empty registry root start source
 have validation : validate owners pool (fun state => (inspect state).core) (fun state => selected (inspect state)) before = .ok () := by
  simp [validate,empty,GeneralRebaseMultiSelection263.check]
 have terminal : GeneralRebaseScheduler259.next (observe owners pool (fun state => (inspect state).core)
   (fun state => selected (inspect state))) before = .ok none := by
  simp [GeneralRebaseScheduler259.next,observe,empty,GeneralRebaseScheduler259.scan]
 unfold run
 rw [GeneralRebaseValidatedDriver263.run,validation,terminal]
theorem selected_is_committed
 {registry : GeneralDeclarations.Registry} {root : GeneralSourceDictionaries.Occurrence roles}
 {state : GeneralNominalVersionedJournal232.State roles}
 (path : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state)
 (entry : GeneralRebaseMultiSelection263.Selection roles) (member : entry ∈ selected state) :
 GeneralNominalVersionedInstallStep232.Committed state entry.plan := by
 obtain ⟨plan,registered,rfl⟩ := List.mem_map.mp member
 exact GeneralNominalVersionedMixedPlanLedger235.reachable_plan_committed path registered

theorem selected_cannot_be_novel
 {registry : GeneralDeclarations.Registry} {root : GeneralSourceDictionaries.Occurrence roles}
 {state : GeneralNominalVersionedJournal232.State roles}
 (path : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state)
 (entry : GeneralRebaseMultiSelection263.Selection roles) (member : entry ∈ selected state) :
 ¬ (¬ GeneralNominalVersionedInstallStep232.Committed state entry.plan) :=
 fun novel => novel (selected_is_committed path entry member)
#print axioms selected_is_committed
#print axioms selected_cannot_be_novel
#print axioms initial_selected_empty
#print axioms initial_inspector_noop
end Yulang.Cycle263InitialBoundary
