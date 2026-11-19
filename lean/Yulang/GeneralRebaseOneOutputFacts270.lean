import Yulang.GeneralRebaseLiveProjection264

namespace Yulang.GeneralRebaseOneOutputFacts270
open GeneralNominalCenters (Plan)
open GeneralSourceState (Output)
open GeneralRebaseStep258 (Fact)
open GeneralRebaseUniversalBasis263 (bodyKey)
open GeneralRebaseOwnedOutputKeys260 (key)
open GeneralRebaseBodyTable261 (schema)
open GeneralRebaseMultiSelection263 (ofPlan proposal requests)
open GeneralNominalVersionedJournal232 (State)
open GeneralRebaseLiveProjection264 (liveFacts)

def pairKey (owner : Nat) (output : Output) : Fact := GeneralRebasePairKeys261.key owner output output

theorem body_key_of_mem (plan : Plan roles) (pOwner : Nat) (query : Output)
 (outputs : List Output) (requestedOwner : Nat) (hit : bodyKey requestedOwner query ∈
   GeneralRebaseBodyTable261.facts plan pOwner outputs) :
 pOwner = requestedOwner ∧ query ∈ outputs := by
 obtain ⟨actual,member,body⟩ := (GeneralRebaseBodyTable261.member ..).mp hit
 have code := GeneralRebaseUniversalBasis263.body_key_exact plan pOwner actual _ body
 have fields := GeneralRebaseRequestBodyKeys260.key_identity code
 exact ⟨fields.1.symm,GeneralRebaseNamedRequest260.code_injective fields.2.2.1 ▸ member⟩

theorem body_avoids_pairs (pOwner queriedOwner : Nat) (query : Output)
 (outputs : List Output) : bodyKey queriedOwner query ∉ GeneralRebasePairKeys261.facts pOwner outputs := by
 intro hit
 obtain ⟨_,_,_,_,_,same⟩ := (GeneralRebasePairKeys261.member ..).mp hit
 have invalid : (1 : Nat) = 3 := (GeneralRebaseRequestBodyKeys260.key_identity same).2.1
 cases invalid

theorem pair_avoids_body (plan : Plan roles) (pOwner queriedOwner : Nat) (query : Output)
 (outputs : List Output) : pairKey queriedOwner query ∉ GeneralRebaseBodyTable261.facts plan pOwner outputs := by
 intro hit
 obtain ⟨actual,_,body⟩ := (GeneralRebaseBodyTable261.member ..).mp hit
 have same := GeneralRebaseUniversalBasis263.body_key_exact plan pOwner actual _ body
 have invalid : (3 : Nat) = 1 := (GeneralRebaseRequestBodyKeys260.key_identity same).2.1
 cases invalid

theorem pair_exact (pOwner queriedOwner : Nat) (outputs : List Output) (query : Output) :
 pairKey queriedOwner query ∈ GeneralRebasePairKeys261.facts pOwner outputs ↔
 pOwner = queriedOwner ∧ query ∈ outputs := by
 constructor
 · intro hit
   obtain ⟨a,first,b,_,_,same⟩ := (GeneralRebasePairKeys261.member ..).mp hit
   obtain ⟨owner,output,_⟩ := GeneralRebasePairKeys261.key_injective same
   exact ⟨owner.symm,output.symm ▸ first⟩
 · rintro ⟨rfl,h⟩
   exact (GeneralRebasePairKeys261.member ..).mpr ⟨query,h,query,h,rfl,rfl⟩

theorem body_from_equation (plan : Plan roles) (owner : Nat) (outputs : List Output)
 (query : Output) (member : query ∈ outputs) (one : (schema plan query).equations.length = 1) :
 bodyKey owner query ∈ GeneralRebaseBodyTable261.facts plan owner outputs := by
 apply (GeneralRebaseBodyTable261.member ..).mpr
 refine ⟨query,member,?_⟩
 change _ ∈ GeneralRebaseOwnedOutputKeys260.keys _ _
 exact (GeneralRebaseOwnedOutputKeys260.member ..).mpr ⟨⟨0,by omega⟩,rfl⟩

theorem pair_proposal (plan : Plan roles) (pOwner queriedOwner : Nat) (outputs : List Output) (query : Output) :
 pairKey queriedOwner query ∈ GeneralRebaseStableClass261.facts plan pOwner outputs ↔
 pOwner = queriedOwner ∧ query ∈ outputs := by
 constructor
 · intro hit
   rcases List.mem_append.mp hit with impossible | matching
   · exact False.elim (pair_avoids_body plan pOwner queriedOwner query outputs impossible)
   · exact (pair_exact ..).mp matching
 · intro matching
   exact List.mem_append_right _ ((pair_exact ..).mpr matching)

theorem body_proposal (plan : Plan roles) (pOwner queriedOwner : Nat) (outputs : List Output) (query : Output)
 (equation : pOwner = queriedOwner → (schema plan query).equations.length = 1) :
 bodyKey queriedOwner query ∈ GeneralRebaseStableClass261.facts plan pOwner outputs ↔
 pOwner = queriedOwner ∧ query ∈ outputs := by
 constructor
 · intro hit
   rcases List.mem_append.mp hit with correct | impossible
   · exact body_key_of_mem plan pOwner query outputs queriedOwner correct
   · exact False.elim (body_avoids_pairs pOwner queriedOwner query outputs impossible)
 · rintro ⟨rfl,requested⟩
   exact List.mem_append_left _ (body_from_equation plan pOwner outputs query requested (equation rfl))

/-- Correlation of the two distinct addresses is a property of this output
schema fragment, not a change to the finite fact representation. -/
theorem synchronized (state : State roles) (owner : Nat) (output : Output)
 (equations : ∀ p ∈ state.plans, (ofPlan p).owner = owner → (schema p output).equations.length = 1) :
 bodyKey owner output ∈ liveFacts state ↔ pairKey owner output ∈ liveFacts state := by
 unfold liveFacts
 rw [GeneralRebaseLiveProjection264.member,GeneralRebaseLiveProjection264.member]
 constructor
 · rintro ⟨plan,stored,body⟩
   refine ⟨plan,stored,(pair_proposal ..).mpr ?_⟩
   exact (body_proposal plan (ofPlan plan).owner owner (requests state.core (ofPlan plan)) output
     (equations plan stored)).mp body
 · rintro ⟨plan,stored,pair⟩
   refine ⟨plan,stored,(body_proposal plan (ofPlan plan).owner owner (requests state.core (ofPlan plan)) output
     (equations plan stored)).mpr ?_⟩
   exact (pair_proposal ..).mp pair

end Yulang.GeneralRebaseOneOutputFacts270
