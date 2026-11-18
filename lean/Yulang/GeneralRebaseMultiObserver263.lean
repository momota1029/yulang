import Yulang.GeneralRebaseOwnerTable263
import Yulang.GeneralRebaseMultiSelection263
import Yulang.GeneralRebaseNormalizedBody263
import Yulang.GeneralRebasePlanSemantic262
import Yulang.GeneralRebaseChildRequestPool262
import Yulang.GeneralRebaseClosedObserver259

namespace Yulang.GeneralRebaseMultiObserver263
open GeneralNominalCenters GeneralRebaseStep258
open GeneralSourceState (Output)
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseMultiSelection263 (Selection proposal)
open GeneralRebaseOwnerTable263 (basis Models)

abbrev Current (owners : List Nat) (representative : Nat → Plan roles) (pool : List Output) :=
 State (basis owners representative pool)

def observe (owners : List Nat) (representative : Nat → Plan roles) (pool : List Output)
 (inspect : Current owners representative pool → GeneralNominalCenteredSteps.State roles)
 (select : Current owners representative pool → List (Selection roles)) : Observer (basis owners representative pool) :=
 fun state => (select state).map (proposal (inspect state))

def Listed (owners : List Nat) (representative : Nat → Plan roles) (pool : List Output)
 (select : Current owners representative pool → List (Selection roles)) : Prop :=
 ∀ state selected, selected ∈ select state → selected.owner ∈ owners

def LayoutCompatible (owners : List Nat) (representative : Nat → Plan roles) (pool : List Output)
 (select : Current owners representative pool → List (Selection roles)) : Prop :=
 ∀ state selected, selected ∈ select state →
 GeneralRebasePlanSemantic262.Layout (representative selected.owner) selected.plan

/-- Normalized body support, not a premise asserting the desired ClassEffects
conclusion. Actual source head/model producers must still supply this condition. -/
def BaseCompatible (base : Assignment → Prop) (owners : List Nat) (representative : Nat → Plan roles)
 (pool : List Output) (select : Current owners representative pool → List (Selection roles)) : Prop :=
 ∀ state selected, selected ∈ select state → ∀ assignment, base assignment →
 GeneralRebaseNormalizedBody263.Compatible (representative selected.owner) selected.plan assignment

theorem closed (owners : List Nat) (representative : Nat → Plan roles) (pool : List Output)
 (inspect : Current owners representative pool → GeneralNominalCenteredSteps.State roles)
 (select : Current owners representative pool → List (Selection roles)) (listed : Listed owners representative pool select)
 (layout : LayoutCompatible owners representative pool select)
 (coverage : ∀ state, GeneralRebaseChildRequestPool262.Covered (inspect state) pool) :
 GeneralRebaseClosedObserver259.Closed (observe owners representative pool inspect select) := by
 intro state proposed member
 obtain ⟨selected,selectedMem,rfl⟩ := List.mem_map.mp member
 unfold proposal
 rw [← GeneralRebasePlanSemantic262.facts_eq (representative selected.owner) selected.plan
   (layout state selected selectedMem) selected.owner]
 apply GeneralRebaseOwnerTable263.proposal_covered owners representative pool selected.owner (listed state selected selectedMem)
 intro output requested
 apply GeneralRebaseChildRequestPool262.requests_covered (inspect state) pool (coverage state) selected.root output
 simpa only [GeneralRebaseMultiSelection263.requests,GeneralRebaseExecutableRequests262.requests_eq] using requested

theorem completion (owners : List Nat) (representative : Nat → Plan roles) (pool : List Output)
 (inspect : Current owners representative pool → GeneralNominalCenteredSteps.State roles)
 (select : Current owners representative pool → List (Selection roles)) (listed : Listed owners representative pool select)
 (layout : LayoutCompatible owners representative pool select)
 (coverage : ∀ state, GeneralRebaseChildRequestPool262.Covered (inspect state) pool)
 (before : Current owners representative pool) :
 ∃ after steps, GeneralRebaseSettle259.settle (observe owners representative pool inspect select) before = .ok after ∧
 GeneralRebaseBudget258.Runs (observe owners representative pool inspect select) steps before after ∧
 steps ≤ owners.length * (pool.length + pool.length * pool.length) ∧
 (∀ next, ¬ Step (observe owners representative pool inspect select) after next) := by
 obtain ⟨after,steps,success,path,_,terminal⟩ := GeneralRebaseClosedObserver259.completion _
   (closed owners representative pool inspect select listed layout coverage) before
 exact ⟨after,steps,success,path,GeneralRebaseOwnerTable263.run_bound owners representative pool _ path,terminal⟩

theorem write_actual (base : Assignment → Prop) (owners : List Nat) (representative : Nat → Plan roles)
 (pool : List Output) (inspect : Current owners representative pool → GeneralNominalCenteredSteps.State roles)
 (select : Current owners representative pool → List (Selection roles)) (listed : Listed owners representative pool select)
 (layout : LayoutCompatible owners representative pool select)
 (compatible : BaseCompatible base owners representative pool select)
 (coverage : ∀ state, GeneralRebaseChildRequestPool262.Covered (inspect state) pool)
 (before : Current owners representative pool) (selected : Selection roles) (chosen : selected ∈ select before)
 (assignment : Assignment) :
 Models base owners representative (write before (proposal (inspect before) selected)) assignment ↔
 Models base owners representative before assignment ∧
 GeneralNominalVersionedEffects231.ClassEffects (inspect before) selected.root selected.plan assignment := by
 unfold proposal GeneralRebaseMultiSelection263.requests
 rw [← GeneralRebasePlanSemantic262.facts_eq (representative selected.owner) selected.plan
   (layout before selected chosen) selected.owner, GeneralRebaseExecutableRequests262.requests_eq]
 rw [GeneralRebaseOwnerTable263.actual_write base owners representative pool selected.owner (listed before selected chosen)
   (inspect before) selected.root (GeneralRebaseChildRequestPool262.requests_covered _ _ (coverage before) selected.root)]
 constructor
 · rintro ⟨prior,effect⟩
   exact ⟨prior,(GeneralRebaseNormalizedBody263.class_effects _ _ assignment
     (compatible before selected chosen assignment prior.1) (inspect before) selected.root).mp effect⟩
 · rintro ⟨prior,effect⟩
   exact ⟨prior,(GeneralRebaseNormalizedBody263.class_effects _ _ assignment
     (compatible before selected chosen assignment prior.1) (inspect before) selected.root).mpr effect⟩

theorem step_actual (base : Assignment → Prop) (owners : List Nat) (representative : Nat → Plan roles)
 (pool : List Output) (inspect : Current owners representative pool → GeneralNominalCenteredSteps.State roles)
 (select : Current owners representative pool → List (Selection roles)) (listed : Listed owners representative pool select)
 (layout : LayoutCompatible owners representative pool select)
 (compatible : BaseCompatible base owners representative pool select)
 (coverage : ∀ state, GeneralRebaseChildRequestPool262.Covered (inspect state) pool)
 (before after : Current owners representative pool)
 (step : Step (observe owners representative pool inspect select) before after) :
 ∃ selected ∈ select before, ∀ assignment,
 Models base owners representative after assignment ↔ Models base owners representative before assignment ∧
 GeneralNominalVersionedEffects231.ClassEffects (inspect before) selected.root selected.plan assignment := by
 obtain ⟨proposed,member,rfl,_⟩ := step
 obtain ⟨selected,chosen,rfl⟩ := List.mem_map.mp member
 exact ⟨selected,chosen,write_actual base owners representative pool inspect select listed layout compatible coverage before selected chosen⟩
end Yulang.GeneralRebaseMultiObserver263
