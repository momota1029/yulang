import Yulang.GeneralRebaseMultiRun263

namespace Yulang.GeneralRebaseMultiTrace263
open GeneralNominalCenters GeneralRebaseStep258
open GeneralSourceState (Output)
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseMultiSelection263 (Selection proposal)
open GeneralRebaseMultiObserver263
open GeneralRebaseOwnerTable263 (Models)

structure Event (roles : Roles.RoleDecls) where
 source : GeneralNominalCenteredSteps.State roles
 selected : Selection roles

/-- Exact per-round snapshots and selected owner/root/Plan; a proof history,
not an unbounded journal added to the executable finite state. -/
inductive Trace (owners : List Nat) (representative : Nat → Plan roles) (pool : List Output)
 (inspect : Current owners representative pool → GeneralNominalCenteredSteps.State roles)
 (select : Current owners representative pool → List (Selection roles)) :
 List (Event roles) → Current owners representative pool → Current owners representative pool → Prop where
 | nil (state) : Trace owners representative pool inspect select [] state state
 | next {selected rest before middle after} : selected ∈ select before →
   middle = write before (proposal (inspect before) selected) → middle.remaining ≠ before.remaining →
   Trace owners representative pool inspect select rest middle after →
   Trace owners representative pool inspect select (⟨inspect before,selected⟩ :: rest) before after

theorem to_runs (owners : List Nat) (representative : Nat → Plan roles) (pool : List Output)
 (inspect : Current owners representative pool → GeneralNominalCenteredSteps.State roles)
 (select : Current owners representative pool → List (Selection roles)) {history before after} (trace : Trace owners representative pool inspect select history before after) :
 GeneralRebaseBudget258.Runs (observe owners representative pool inspect select) history.length before after := by
 induction trace with
 | nil state => exact .nil state
 | next chosen same progress _ ih => exact .next ⟨_,List.mem_map.mpr ⟨_,chosen,rfl⟩,same,progress⟩ ih

theorem models_exact (base : Assignment → Prop) (owners : List Nat) (representative : Nat → Plan roles)
 (pool : List Output) (inspect : Current owners representative pool → GeneralNominalCenteredSteps.State roles)
 (select : Current owners representative pool → List (Selection roles)) (listed : Listed owners representative pool select)
 (layout : LayoutCompatible owners representative pool select)
 (compatible : BaseCompatible base owners representative pool select)
 (coverage : ∀ state, GeneralRebaseChildRequestPool262.Covered (inspect state) pool)
 {history before after} (trace : Trace owners representative pool inspect select history before after) :
 ∀ assignment, Models base owners representative after assignment ↔ Models base owners representative before assignment ∧
 ∀ event ∈ history, GeneralNominalVersionedEffects231.ClassEffects event.source event.selected.root event.selected.plan assignment := by
 induction trace with
 | nil state => intro assignment; simp
 | @next selected rest before middle after chosen same _ _ ih =>
   intro assignment
   rw [ih,same,write_actual base owners representative pool inspect select listed layout compatible coverage before selected chosen assignment]
   simp only [List.mem_cons,forall_eq_or_imp]
   exact and_assoc

theorem from_checked (owners : List Nat) (representative : Nat → Plan roles) (pool : List Output)
 (inspect : Current owners representative pool → GeneralNominalCenteredSteps.State roles)
 (select : Current owners representative pool → List (Selection roles)) {states before after}
 (checked : GeneralRebaseValidatedDriver263.Trace (observe owners representative pool inspect select)
   (GeneralRebaseMultiRun263.validate owners representative pool inspect select) states before after) :
 ∃ events : List (Event roles), events.length = states.length ∧
 Trace owners representative pool inspect select events before after ∧
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

theorem certificate (base : Assignment → Prop) (owners : List Nat) (representative : Nat → Plan roles)
 (pool : List Output) (inspect : Current owners representative pool → GeneralNominalCenteredSteps.State roles)
 (select : Current owners representative pool → List (Selection roles)) (listed : Listed owners representative pool select)
 (layout : LayoutCompatible owners representative pool select)
 (compatible : BaseCompatible base owners representative pool select)
 (coverage : ∀ state, GeneralRebaseChildRequestPool262.Covered (inspect state) pool)
 (before after : Current owners representative pool)
 (success : GeneralRebaseMultiRun263.run owners representative pool inspect select before = .ok after) :
 ∃ states, ∃ events : List (Event roles),
 GeneralRebaseValidatedDriver263.Trace (observe owners representative pool inspect select)
   (GeneralRebaseMultiRun263.validate owners representative pool inspect select) states before after ∧
 Trace owners representative pool inspect select events before after ∧ events.length = states.length ∧
 events.length ≤ owners.length * (pool.length + pool.length * pool.length) ∧
 (∀ event ∈ events, GeneralNominalCenteredHeadMatEffects.Ready event.source event.selected.root event.selected.plan) ∧
 GeneralRebaseMultiSelection263.Ready (inspect after) (select after) ∧
 (∀ next, ¬ Step (observe owners representative pool inspect select) after next) ∧
 (∀ assignment, Models base owners representative after assignment ↔ Models base owners representative before assignment ∧
   ∀ event ∈ events, GeneralNominalVersionedEffects231.ClassEffects event.source event.selected.root event.selected.plan assignment) := by
 obtain ⟨states,checked,_,bound,_,readyFinal,terminal⟩ :=
   GeneralRebaseMultiRun263.certificate owners representative pool inspect select before after success
 obtain ⟨events,length,trace,readyEvents⟩ := from_checked owners representative pool inspect select checked
 exact ⟨states,events,checked,trace,length,by simpa [length] using bound,readyEvents,readyFinal,terminal,
   models_exact base owners representative pool inspect select listed layout compatible coverage trace⟩
end Yulang.GeneralRebaseMultiTrace263
