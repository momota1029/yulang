import Yulang.GeneralRebaseStableBody261
namespace Yulang.GeneralRebaseStableClass261
open GeneralNominalCenters
open GeneralSourceState (Output)
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseStep258

def facts (plan : Plan roles) (owner : Nat) (outputs : List Output) : List Fact :=
 GeneralRebaseBodyTable261.facts plan owner outputs ++ GeneralRebasePairKeys261.facts owner outputs

def Holds (plan : Plan roles) (owner : Nat) (assignment : Assignment) (fact : Fact) : Prop :=
 GeneralRebaseStableBody261.Holds plan owner assignment fact ∧ GeneralRebasePairKeys261.Holds owner assignment fact

theorem all_exact (plan : Plan roles) (owner : Nat) (outputs : List Output) (assignment : Assignment) :
 (∀ fact ∈ facts plan owner outputs, Holds plan owner assignment fact) ↔
 GeneralRebaseClassTable261.Effects plan outputs assignment := by
 constructor
 · intro valid
   exact ⟨(GeneralRebaseStableBody261.all_exact ..).mp (fun fact h => (valid fact (List.mem_append_left _ h)).1),
     (GeneralRebasePairKeys261.all_exact ..).mp (fun fact h => (valid fact (List.mem_append_right _ h)).2)⟩
 · rintro ⟨bodies,pairs⟩ fact included
   rcases List.mem_append.mp included with body | pair
   · obtain ⟨output,_,within⟩ := (GeneralRebaseBodyTable261.member ..).mp body
     exact ⟨(GeneralRebaseStableBody261.all_exact ..).mpr bodies fact body,
       GeneralRebaseStableBody261.pair_at_body plan owner output assignment fact within⟩
   · obtain ⟨first,_,last,_,_,rfl⟩ := (GeneralRebasePairKeys261.member ..).mp pair
     exact ⟨GeneralRebaseStableBody261.at_pair plan owner first last assignment,
       (GeneralRebasePairKeys261.all_exact ..).mpr pairs _ pair⟩

theorem monotone (plan : Plan roles) (owner : Nat) (small large : List Output)
 (included : ∀ output ∈ small, output ∈ large) :
 ∀ fact ∈ facts plan owner small, fact ∈ facts plan owner large := by
 intro fact present
 rcases List.mem_append.mp present with body | pair
 · exact List.mem_append_left _ (GeneralRebaseStableBody261.monotone plan owner small large included fact body)
 · exact List.mem_append_right _ (GeneralRebasePairKeys261.monotone owner small large included fact pair)

theorem reordered (plan : Plan roles) (owner : Nat) (first last : List Output)
 (same : ∀ output, output ∈ first ↔ output ∈ last) (fact : Fact) :
 fact ∈ facts plan owner first ↔ fact ∈ facts plan owner last :=
 ⟨monotone plan owner first last (fun o h => (same o).mp h) fact,
 monotone plan owner last first (fun o h => (same o).mpr h) fact⟩

def Models (base : Assignment → Prop) (plan : Plan roles) (owner : Nat) {candidates : List Output}
 (state : State (facts plan owner candidates)) := GeneralRebaseFactSemantics259.Models base (Holds plan owner) state

/-- A dynamic subrequest write adds precisely its actual class obligations.
The fixed finite candidate premise is explicit, not a source-closure result. -/
theorem write_exact (base : Assignment → Prop) (plan : Plan roles) (owner : Nat)
 (candidates outputs : List Output) (included : ∀ output ∈ outputs, output ∈ candidates)
 (state : State (facts plan owner candidates)) (assignment : Assignment) :
 Models base plan owner (write state (facts plan owner outputs)) assignment ↔
 Models base plan owner state assignment ∧ GeneralRebaseClassTable261.Effects plan outputs assignment := by
 rw [Models,GeneralRebaseFactSemantics259.write_exact]
 apply and_congr Iff.rfl
 constructor
 · intro valid
   apply (all_exact ..).mp
   intro fact member
   exact valid fact (monotone plan owner outputs candidates included fact member) member
 · intro valid fact _ member
   exact (all_exact ..).mpr valid fact member

theorem actual_write (base : Assignment → Prop) (plan : Plan roles) (owner : Nat)
 (source : GeneralNominalCenteredSteps.State roles) (root : GeneralSourceDictionaries.Occurrence roles)
 (candidates : List Output)
 (included : ∀ output ∈ GeneralNominalCenteredHeadOutputs.requests source root, output ∈ candidates)
 (state : State (facts plan owner candidates)) (assignment : Assignment) :
 Models base plan owner (write state (facts plan owner (GeneralNominalCenteredHeadOutputs.requests source root))) assignment ↔
 Models base plan owner state assignment ∧ GeneralNominalVersionedEffects231.ClassEffects source root plan assignment :=
 write_exact base plan owner candidates _ included state assignment
end Yulang.GeneralRebaseStableClass261
