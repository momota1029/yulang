import Yulang.GeneralRebaseStrictAccessibility267
import Yulang.GeneralRebaseProjectedBudget264

namespace Yulang.GeneralRebaseWeakProgress268
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State)
open GeneralSourceState (Output)
open GeneralRebaseLiveProjection264 (project)
open GeneralNominalVersionedMixedKernel234 (Step)
open B4Target (Steps)

def Stutter (registry : Registry) (root : Occurrence roles) (owners : List Nat) (pool : List Output)
 (first last : State roles) : Prop :=
 Step registry root first last ∧ project owners pool last = project owners pool first

abbrev Lull (registry : Registry) (root : Occurrence roles) (owners : List Nat) (pool : List Output) :=
 Steps (Stutter registry root owners pool)

def Weak (registry : Registry) (root : Occurrence roles) (owners : List Nat) (pool : List Output)
 (first last : State roles) : Prop :=
 ∃ middle, Lull registry root owners pool first middle ∧
 Step registry root middle last ∧ project owners pool last ≠ project owners pool middle

theorem lull_same (path : Lull registry root owners pool first last) :
 project owners pool last = project owners pool first := by
 induction path with
 | refl => rfl
 | tail _ step ih => exact step.2.trans ih

theorem lull_source (path : Lull registry root owners pool first last) : Steps (Step registry root) first last := by
 induction path with
 | refl => exact .refl
 | tail _ step ih => exact .tail ih step.1

theorem weak_source (edge : Weak registry root owners pool first last) : Steps (Step registry root) first last := by
 obtain ⟨_,stutters,change,_⟩ := edge
 exact .tail (lull_source stutters) change

theorem decrease (edge : Weak registry root owners pool first last) :
 (project owners pool last).remaining.length < (project owners pool first).remaining.length := by
 obtain ⟨_,stutters,step,different⟩ := edge
 have strict := GeneralRebaseSourceProjection264.strict_decrease owners pool step different
 simpa only [lull_same stutters] using strict

theorem wellFounded (registry : Registry) (root : Occurrence roles) (owners : List Nat) (pool : List Output) :
 WellFounded (fun after before => Weak registry root owners pool before after) := by
 let rank := fun state : State roles => (project owners pool state).remaining.length
 apply Subrelation.wf (r := InvImage Nat.lt rank) _ (InvImage.wf rank Nat.lt_wfRel.wf)
 intro _ _ weak
 exact decrease weak

inductive Counted (registry : Registry) (root : Occurrence roles) (owners : List Nat) (pool : List Output) :
 Nat → State roles → State roles → Prop where
 | nil (state) : Counted registry root owners pool 0 state state
 | tail : Counted registry root owners pool n first middle → Weak registry root owners pool middle last →
   Counted registry root owners pool (n+1) first last

theorem budget (path : Counted registry root owners pool n first last) :
 n + (project owners pool last).remaining.length ≤ (project owners pool first).remaining.length := by
 induction path with
 | nil _ => simp
 | tail _ next ih =>
   have strict := decrease next
   omega

/-- Exact grouping of a previously counted old trace, preserving every
strict change and all intervening stutters. -/
theorem grouping (path : GeneralRebaseProjectedBudget264.Trace owners pool registry root n first last) :
 ∃ middle, Counted registry root owners pool n first middle ∧ Lull registry root owners pool middle last := by
 induction path with
 | refl state => exact ⟨state,.nil _, .refl⟩
 | stutter _ step same ih =>
   obtain ⟨middle,packed,suffix⟩ := ih
   exact ⟨middle,packed,.tail suffix ⟨step,same⟩⟩
 | advance _ step different ih =>
   obtain ⟨middle,packed,suffix⟩ := ih
   exact ⟨_,.tail packed ⟨_,suffix,step,different⟩,.refl⟩

theorem decomposition (registry : Registry) (root : Occurrence roles) (owners : List Nat) (pool : List Output)
 (path : Steps (Step registry root) first last) :
 ∃ count middle, Counted registry root owners pool count first middle ∧ Lull registry root owners pool middle last ∧
 count + (project owners pool last).remaining.length ≤ (project owners pool first).remaining.length := by
 obtain ⟨count,annotated⟩ := GeneralRebaseProjectedBudget264.from_steps owners pool path
 obtain ⟨middle,packed,suffix⟩ := grouping annotated
 exact ⟨count,middle,packed,suffix,by rw [lull_same suffix]; exact budget packed⟩

end Yulang.GeneralRebaseWeakProgress268
