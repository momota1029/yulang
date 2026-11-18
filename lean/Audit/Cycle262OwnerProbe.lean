import Yulang.GeneralRebaseStableClass261
import Yulang.GeneralRebaseQuadraticBudget262

namespace Cycle262OwnerProbe
open Yulang
open GeneralNominalCenters GeneralRebaseStep258
open GeneralSourceState (Output)
open GeneralNominalCommonBridge (Assignment)

/-- Address provenance only; no multi-owner scheduler is defined here. -/
def Tagged (owner : Nat) (fact : Fact) : Prop :=
 ∃ kind request equation, fact = GeneralRebaseRequestBodyKeys260.key owner kind request equation

theorem body_tagged (plan : Plan roles) (owner : Nat) (output : Output) (fact : Fact)
 (member : fact ∈ GeneralRebaseBodyTable261.keys plan owner output) : Tagged owner fact := by
 obtain ⟨index,equal⟩ := GeneralRebaseOwnedOutputKeys260.member _ _ fact |>.mp member
 exact ⟨1,GeneralRebaseNamedRequest260.code output,index.val,equal⟩

theorem tagged (plan : Plan roles) (owner : Nat) (outputs : List Output) (fact : Fact)
 (member : fact ∈ GeneralRebaseStableClass261.facts plan owner outputs) : Tagged owner fact := by
 rcases List.mem_append.mp member with body | pair
 · obtain ⟨output,_,member⟩ := (GeneralRebaseBodyTable261.member plan owner outputs fact).mp body
   exact body_tagged plan owner output fact member
 · obtain ⟨first,_,last,_,_,equal⟩ := (GeneralRebasePairKeys261.member owner outputs fact).mp pair
   exact ⟨3,GeneralRebasePairKeys261.code first last,0,equal⟩

theorem owner_unique (first last : Nat) (fact : Fact) (one : Tagged first fact) (two : Tagged last fact) : first = last := by
 obtain ⟨kind,request,equation,one⟩ := one
 obtain ⟨kind',request',equation',two⟩ := two
 exact (GeneralRebaseRequestBodyKeys260.key_identity (one.symm.trans two)).1

theorem tables_separate (first last : Plan roles) (one two : Nat) (different : one ≠ two)
 (outputs requests : List Output) (fact : Fact) :
 ¬ (fact ∈ GeneralRebaseStableClass261.facts first one outputs ∧
 fact ∈ GeneralRebaseStableClass261.facts last two requests) := by
 rintro ⟨left,right⟩
 exact different (owner_unique one two fact (tagged first one outputs fact left) (tagged last two requests fact right))

/-- Foreign owner meanings are vacuous on an address belonging elsewhere.
This is the local independence lemma needed before combining owner tables. -/
theorem foreign_holds (plan : Plan roles) (owner foreign : Nat) (different : owner ≠ foreign)
 (assignment : Assignment) (fact : Fact) (origin : Tagged foreign fact) :
 GeneralRebaseStableClass261.Holds plan owner assignment fact := by
 constructor
 · intro output member
   exact False.elim (different (owner_unique owner foreign fact (body_tagged plan owner output fact member) origin))
 · intro first last equal
   exact False.elim (different (owner_unique owner foreign fact
     ⟨3,GeneralRebasePairKeys261.code first last,0,equal⟩ origin))
/-- A table-size bound only; representatives are still external inputs. -/
theorem tables_bound (owners : List Nat) (representative : Nat → Plan roles) (pool : List Output) :
 (owners.flatMap (fun owner => GeneralRebaseStableClass261.facts (representative owner) owner pool)).length ≤
 owners.length * (pool.length + pool.length * pool.length) := by
 exact GeneralRebaseQuadraticBudget262.flatMap_bound owners _ _
   (fun owner _ => GeneralRebaseQuadraticBudget262.facts_bound (representative owner) owner pool)

/-- Conjoining all owner interpretations adds no foreign-owner condition to
an owned address. This still does not construct source representatives. -/
theorem combined_holds (owners : List Nat) (representative : Nat → Plan roles)
 (owner : Nat) (member : owner ∈ owners) (assignment : Assignment) (fact : Fact)
 (origin : Tagged owner fact) :
 (∀ other ∈ owners, GeneralRebaseStableClass261.Holds (representative other) other assignment fact) ↔
 GeneralRebaseStableClass261.Holds (representative owner) owner assignment fact := by
 constructor
 · intro all
   exact all owner member
 · intro own other _
   by_cases same : other = owner
   · subst other
     exact own
   · exact foreign_holds (representative other) other owner same assignment fact origin

end Cycle262OwnerProbe
#print axioms Cycle262OwnerProbe.body_tagged
#print axioms Cycle262OwnerProbe.tagged
#print axioms Cycle262OwnerProbe.owner_unique
#print axioms Cycle262OwnerProbe.tables_separate
#print axioms Cycle262OwnerProbe.foreign_holds

#print axioms Cycle262OwnerProbe.tables_bound

#print axioms Cycle262OwnerProbe.combined_holds
