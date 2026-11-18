import Yulang.GeneralRebaseUniversalSource263
import Yulang.GeneralRebaseUniversalTrace263
import Yulang.GeneralRebaseSourceRepresentatives263

namespace Yulang.GeneralRebaseSourceMeaning263
open GeneralNominalCenters GeneralRebaseStep258
open GeneralSourceState (Output)
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseUniversalObserver263 (Current observe validate run)
open GeneralRebaseMultiSource263 (selected)
open GeneralRebaseSourceRepresentatives263 (RegisteredAt SourceHeads Path)

def Context (base : Assignment → Prop) (registry : GeneralDeclarations.Registry)
 (root : GeneralSourceDictionaries.Occurrence roles) (start : GeneralNominalVersionedJournal232.State roles)
 (assignment : Assignment) : Prop := base assignment ∧ SourceHeads registry root start assignment

/-- Exact event meaning under an explicit head-only context. The interpretation
is fixed before the inspector and base are chosen. No source Step simulation or
automatic derivation of this semantic context is asserted. -/
def Certificate (owners : List Nat) (pool : List Output)
 (holds : Assignment → Fact → Prop) (base : Assignment → Prop)
 (inspect : Current owners pool → GeneralNominalVersionedJournal232.State roles)
 (before after : Current owners pool) : Prop :=
 ∃ events : List (GeneralRebaseUniversalTrace263.Event roles),
 GeneralRebaseUniversalTrace263.Trace owners pool (fun state => (inspect state).core)
   (fun state => selected (inspect state)) events before after ∧
 events.length ≤ owners.length * (pool.length + pool.length * pool.length) ∧
 (∀ event ∈ events, GeneralNominalCenteredHeadMatEffects.Ready event.source event.selected.root event.selected.plan) ∧
 GeneralRebaseMultiSelection263.Ready (inspect after).core (selected (inspect after)) ∧
 (∀ next, ¬ Step (observe owners pool (fun state => (inspect state).core) (fun state => selected (inspect state))) after next) ∧
 (∀ assignment, GeneralRebaseFactSemantics259.Models base holds after assignment ↔
   GeneralRebaseFactSemantics259.Models base holds before assignment ∧
   ∀ event ∈ events, GeneralNominalVersionedEffects231.ClassEffects event.source event.selected.root event.selected.plan assignment)

theorem empty_selected (registry : GeneralDeclarations.Registry) (root : GeneralSourceDictionaries.Occurrence roles)
 (start : GeneralNominalVersionedJournal232.State roles)
 (empty : ¬ ∃ owner plan, RegisteredAt registry root start owner plan)
 (state : GeneralNominalVersionedJournal232.State roles) (path : Path registry root start state) : selected state = [] := by
 apply List.eq_nil_iff_forall_not_mem.mpr
 intro entry member
 obtain ⟨plan,registered,rfl⟩ := List.mem_map.mp member
 exact empty ⟨GeneralRebaseRegisteredOwners263.code plan,plan,state,path,registered,rfl⟩

/-- A fixed source-derived interpretation exists even when no registered Plan
exists. Representative choice in the nonempty case is noncomputable mathematics,
not an executable discovery algorithm. The context explicitly requires SourceHeads. -/
theorem source_certificate (registry : GeneralDeclarations.Registry)
 (checked : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Checked registry)
 (root : GeneralSourceDictionaries.Occurrence roles) (start : GeneralNominalVersionedJournal232.State roles)
 (source : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Initial registry root start) :
 ∃ owners : List Nat, ∃ pool : List Output, ∃ holds : Assignment → Fact → Prop,
 ∀ (base : Assignment → Prop) (inspect : Current owners pool → GeneralNominalVersionedJournal232.State roles),
 (∀ state, Path registry root start (inspect state)) →
 ∀ before after, run owners pool (fun state => (inspect state).core) (fun state => selected (inspect state)) before = .ok after →
 Certificate owners pool holds (Context base registry root start) inspect before after := by
 classical
 obtain ⟨owners,pool,bounds⟩ := GeneralRebaseMultiSource263.source_bounds registry root start source
 by_cases inhabited : ∃ owner plan, RegisteredAt registry root start owner plan
 · let representative := GeneralRebaseSourceRepresentatives263.representatives registry root start inhabited
   refine ⟨owners,pool,GeneralRebaseOwnerTable263.Holds owners representative,?_⟩
   intro base inspect reachable before after success
   apply GeneralRebaseUniversalTrace263.certificate (Context base registry root start) owners pool representative
     (fun state => (inspect state).core) (fun state => selected (inspect state))
     (fun state => (bounds (inspect state) (reachable state)).1) _
     (fun state => (bounds (inspect state) (reachable state)).2) before after success
   intro state entry chosen assignment valid
   obtain ⟨plan,registered,rfl⟩ := List.mem_map.mp chosen
   exact GeneralRebaseSourceRepresentatives263.representative_compatible registry checked root start source inhabited
     (inspect state) (reachable state) plan registered assignment valid.2
 · refine ⟨owners,pool,(fun _ _ => True),?_⟩
   intro base inspect reachable before after success
   have none : ∀ state, selected (inspect state) = [] := fun state => empty_selected registry root start inhabited _ (reachable state)
   have observation : observe owners pool (fun state => (inspect state).core) (fun state => selected (inspect state)) = fun _ => [] := by
     funext state
     simp [observe,none]
   have validation : validate owners pool (fun state => (inspect state).core) (fun state => selected (inspect state)) = fun _ => .ok () := by
     funext state
     simp [validate,none,GeneralRebaseMultiSelection263.check]
   unfold run at success
   rw [observation,validation,GeneralRebaseValidatedDriver263.run] at success
   simp only [GeneralRebaseScheduler259.next,GeneralRebaseScheduler259.scan] at success
   cases Except.ok.inj success
   refine ⟨[],.nil _,by simp,by simp,?_,?_,?_⟩
   · simp [none,GeneralRebaseMultiSelection263.Ready]
   · intro next step
     rw [observation] at step
     obtain ⟨proposed,member,_,_⟩ := step
     cases member
   · intro assignment
     simp
end Yulang.GeneralRebaseSourceMeaning263
