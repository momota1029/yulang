import Yulang.GeneralRebaseUniversalObserver263
import Yulang.GeneralRebaseMultiSource263

namespace Yulang.GeneralRebaseUniversalSource263
open GeneralRebaseStep258
open GeneralSourceState (Output)
open GeneralRebaseUniversalObserver263
open GeneralRebaseMultiSource263 (selected)

/-- Actual source formation supplies a Plan-free finite address basis for all
registered-plan observations. The snapshot inspector remains an explicit input. -/
theorem source_closed (registry : GeneralDeclarations.Registry) (root : GeneralSourceDictionaries.Occurrence roles)
 (start : GeneralNominalVersionedJournal232.State roles)
 (source : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Initial registry root start) :
 ∃ owners : List Nat, ∃ pool : List Output,
 ∀ (inspect : Current owners pool → GeneralNominalVersionedJournal232.State roles),
 (∀ state, B4Target.Steps ((GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Step registry root) start (inspect state)) →
 GeneralRebaseClosedObserver259.Closed
   (observe owners pool (fun state => (inspect state).core) (fun state => selected (inspect state))) := by
 obtain ⟨owners,pool,bounds⟩ := GeneralRebaseMultiSource263.source_bounds registry root start source
 refine ⟨owners,pool,?_⟩
 intro inspect reachable
 exact closed owners pool (fun state => (inspect state).core) (fun state => selected (inspect state))
   (fun state => (bounds (inspect state) (reachable state)).1)
   (fun state => (bounds (inspect state) (reachable state)).2)

/-- No external representative Plans, layout agreement, desired semantics or
all-state readiness is assumed. Outcome is success or an internal body diagnostic,
not SAT or source-language acceptance/rejection. This is not an old-Step simulation. -/
theorem source_outcome (registry : GeneralDeclarations.Registry) (root : GeneralSourceDictionaries.Occurrence roles)
 (start : GeneralNominalVersionedJournal232.State roles)
 (source : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Initial registry root start) :
 ∃ owners : List Nat, ∃ pool : List Output,
 ∀ (inspect : Current owners pool → GeneralNominalVersionedJournal232.State roles),
 (∀ state, B4Target.Steps ((GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Step registry root) start (inspect state)) →
 ∀ before,
 (∃ after history, run owners pool (fun state => (inspect state).core) (fun state => selected (inspect state)) before = .ok after ∧
   GeneralRebaseValidatedDriver263.Trace
     (observe owners pool (fun state => (inspect state).core) (fun state => selected (inspect state)))
     (validate owners pool (fun state => (inspect state).core) (fun state => selected (inspect state))) history before after ∧
   history.length ≤ owners.length * (pool.length + pool.length * pool.length)) ∨
 (∃ reason current steps, run owners pool (fun state => (inspect state).core) (fun state => selected (inspect state)) before =
     .error (.validation reason) ∧
   GeneralRebaseBudget258.Runs
     (observe owners pool (fun state => (inspect state).core) (fun state => selected (inspect state))) steps before current ∧
   steps ≤ owners.length * (pool.length + pool.length * pool.length) ∧ reason.selected ∈ selected (inspect current) ∧
   GeneralRebaseClassCheck261.check reason.selected.plan
     (GeneralRebaseMultiSelection263.requests (inspect current).core reason.selected) = .error reason.reason) := by
 obtain ⟨owners,pool,bounds⟩ := GeneralRebaseMultiSource263.source_bounds registry root start source
 refine ⟨owners,pool,?_⟩
 intro inspect reachable before
 exact outcome owners pool (fun state => (inspect state).core) (fun state => selected (inspect state))
   (fun state => (bounds (inspect state) (reachable state)).1)
   (fun state => (bounds (inspect state) (reachable state)).2) before
end Yulang.GeneralRebaseUniversalSource263
