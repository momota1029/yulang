import Yulang.GeneralRebaseUniversalMeaning263
import Yulang.GeneralRebaseMultiTrace263

namespace Yulang.GeneralRebaseUniversalTrace263
open GeneralNominalCenters GeneralRebaseStep258
open GeneralSourceState (Output)
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseMultiSelection263 (Selection proposal)
open GeneralRebaseUniversalObserver263 (Current observe validate run)
open GeneralRebaseUniversalMeaning263 (Models)
abbrev Event := GeneralRebaseMultiTrace263.Event

def BaseCompatible (base : Assignment → Prop) (owners : List Nat) (pool : List Output)
 (representative : Nat → Plan roles) (select : Current owners pool → List (Selection roles)) : Prop :=
 ∀ state entry, entry ∈ select state → ∀ assignment, base assignment →
 GeneralRebaseNormalizedBody263.Compatible (representative entry.owner) entry.plan assignment

inductive Trace (owners : List Nat) (pool : List Output)
 (inspect : Current owners pool → GeneralNominalCenteredSteps.State roles)
 (select : Current owners pool → List (Selection roles)) :
 List (Event roles) → Current owners pool → Current owners pool → Prop where
 | nil (state) : Trace owners pool inspect select [] state state
 | next {selected rest before middle after} : selected ∈ select before →
   middle = write before (proposal (inspect before) selected) → middle.remaining ≠ before.remaining →
   Trace owners pool inspect select rest middle after →
   Trace owners pool inspect select (⟨inspect before,selected⟩ :: rest) before after

theorem to_runs (owners : List Nat) (pool : List Output)
 (inspect : Current owners pool → GeneralNominalCenteredSteps.State roles)
 (select : Current owners pool → List (Selection roles))
 {history before after} (trace : Trace owners pool inspect select history before after) :
 GeneralRebaseBudget258.Runs (observe owners pool inspect select) history.length before after := by
 induction trace with
 | nil state => exact .nil state
 | next chosen same progress _ ih => exact .next ⟨_,List.mem_map.mpr ⟨_,chosen,rfl⟩,same,progress⟩ ih

theorem models_exact (base : Assignment → Prop) (owners : List Nat) (pool : List Output)
 (representative : Nat → Plan roles)
 (inspect : Current owners pool → GeneralNominalCenteredSteps.State roles)
 (select : Current owners pool → List (Selection roles))
 (listed : ∀ state entry, entry ∈ select state → entry.owner ∈ owners)
 (compatible : BaseCompatible base owners pool representative select)
 (coverage : ∀ state, GeneralRebaseChildRequestPool262.Covered (inspect state) pool)
 {history before after} (trace : Trace owners pool inspect select history before after) :
 ∀ assignment, Models base owners representative after assignment ↔ Models base owners representative before assignment ∧
 ∀ event ∈ history, GeneralNominalVersionedEffects231.ClassEffects event.source event.selected.root event.selected.plan assignment := by
 induction trace with
 | nil state => intro assignment; simp
 | @next selected rest before middle after chosen same _ _ ih =>
   intro assignment
   rw [ih,same,GeneralRebaseUniversalMeaning263.actual_write base owners representative pool selected.owner
     (listed before selected chosen) (inspect before) selected.root selected.plan (coverage before)
     (compatible before selected chosen) before assignment]
   simp only [List.mem_cons,forall_eq_or_imp]
   exact and_assoc

theorem from_checked (owners : List Nat) (pool : List Output)
 (inspect : Current owners pool → GeneralNominalCenteredSteps.State roles)
 (select : Current owners pool → List (Selection roles)) {states before after}
 (checked : GeneralRebaseValidatedDriver263.Trace (observe owners pool inspect select)
   (validate owners pool inspect select) states before after) :
 ∃ events : List (Event roles), events.length = states.length ∧ Trace owners pool inspect select events before after ∧
 ∀ event ∈ events, GeneralNominalCenteredHeadMatEffects.Ready event.source event.selected.root event.selected.plan := by
 induction checked with
 | done => exact ⟨[],rfl,.nil _,by simp⟩
 | @next before middle final history ready advanced _ ih =>
   have step := GeneralRebaseScheduler259.next_step _ before middle advanced
   obtain ⟨proposed,member,same,progress⟩ := step
   obtain ⟨selected,chosen,rfl⟩ := List.mem_map.mp member
   obtain ⟨events,length,trace,readyEvents⟩ := ih
   refine ⟨⟨inspect before,selected⟩ :: events,by simp [length],.next chosen same progress trace,?_⟩
   intro event member
   rcases List.mem_cons.mp member with rfl | member
   · have one := (GeneralRebaseMultiSelection263.check_exact ..).mp ready selected chosen
     have success := (GeneralRebaseClassCheck261.check_exact ..).mpr one
     rw [GeneralRebaseMultiSelection263.requests,GeneralRebaseExecutableRequests262.requests_eq] at success
     exact (GeneralRebaseClassCheck261.actual_ready ..).mp success
   · exact readyEvents event member

theorem certificate (base : Assignment → Prop) (owners : List Nat) (pool : List Output)
 (representative : Nat → Plan roles)
 (inspect : Current owners pool → GeneralNominalCenteredSteps.State roles)
 (select : Current owners pool → List (Selection roles))
 (listed : ∀ state entry, entry ∈ select state → entry.owner ∈ owners)
 (compatible : BaseCompatible base owners pool representative select)
 (coverage : ∀ state, GeneralRebaseChildRequestPool262.Covered (inspect state) pool)
 (before after : Current owners pool) (success : run owners pool inspect select before = .ok after) :
 ∃ events : List (Event roles), Trace owners pool inspect select events before after ∧
 events.length ≤ owners.length * (pool.length + pool.length * pool.length) ∧
 (∀ event ∈ events, GeneralNominalCenteredHeadMatEffects.Ready event.source event.selected.root event.selected.plan) ∧
 GeneralRebaseMultiSelection263.Ready (inspect after) (select after) ∧
 (∀ next, ¬ Step (observe owners pool inspect select) after next) ∧
 (∀ assignment, Models base owners representative after assignment ↔ Models base owners representative before assignment ∧
   ∀ event ∈ events, GeneralNominalVersionedEffects231.ClassEffects event.source event.selected.root event.selected.plan assignment) := by
 obtain ⟨states,checked,_,bound,_,readyFinal,terminal⟩ :=
   GeneralRebaseUniversalObserver263.certificate owners pool inspect select before after success
 obtain ⟨events,length,trace,readyEvents⟩ := from_checked owners pool inspect select checked
 exact ⟨events,trace,by simpa [length] using bound,readyEvents,readyFinal,terminal,
   models_exact base owners pool representative inspect select listed compatible coverage trace⟩
end Yulang.GeneralRebaseUniversalTrace263
