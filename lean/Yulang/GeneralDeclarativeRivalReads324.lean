import Yulang.GeneralDeclarativeRivalDecl324
import Yulang.GeneralDeclarativeMetadata324

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeRivalReads324
open GeneralDeclarativeRivalDecl324
open GeneralDeclarativeAggregateFixture324 (newState actualNames emitted merged bounds support exact_child)
open GeneralDeclarativeAggregateReads324 (childNames actual_head child_reads)
open GeneralDeclarativeAggregateProbe324 (parent_matches child_matches parent_ready)
open GeneralDeclarativeRepeatedSource323 (goal parent child registry pat whereClause)
open GeneralDeclarativeRepeatedReads323 (place)
open GeneralDeclarativeExampleSource320 (interp)
open GeneralDeclarativeMetadata324 (Same keys normalized_fact normalized_probe)
open GeneralDeclarativeNFComplete324 (ReadBack local_sound)
open GeneralDeclarativeNFNode324 (BodyCoverage)
open GeneralDeclarativeNFHead324 (fact)
open GeneralDeclarativeCompileLists321 (Result)
open GeneralDeclarativeEndpointProbe321 (HeadMatches)
open GeneralDeclarativeOrigins321 (restriction)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeAssembly320 (Meaning)
open GeneralDeclarativeHead320 (Models)
open GeneralDeclarativeNormalized320 (ordered_map)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarationPatterns (normalize)
open CommonRoleOutermostResolver (All₂)

theorem agrees_on_actual_head : Same registry.constructors wider.constructors interp richer (keys (normalize pat)) := by
  intro key read
  change key ∈ [0] at read
  cases List.mem_singleton.mp read
  exact ⟨rfl,rfl,rfl⟩

theorem parent_matches_here (done : Nat → Prop) :
    HeadMatches (restriction (support done)) wider.constructors richer goal parent := by
  apply ordered_map (parent_matches done)
  intro arg _ p present reads
  simp only [List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with rfl|rfl <;> exact (normalized_probe agrees_on_actual_head).mp reads

theorem child_matches_here (done : Nat → Prop) :
    HeadMatches (restriction (support done)) wider.constructors richer emitted child :=
  .cons ⟨bounds,.variable 0,[⟨0,.lower,33⟩],[⟨0,.upper,34⟩],rfl,.capture,.capture⟩ .nil

theorem parent_read : ReadBack newState wider richer goal parent actualNames place := by
  refine ⟨?_,fun _ _ => bounds,fun _ impossible => False.elim (List.not_mem_nil impossible),?_⟩
  · apply ordered_map actual_head
    rintro arg _ p found ⟨covered,rows,written,truth⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at found
    rcases found with rfl|rfl
    all_goals exact ⟨covered,rows,(normalized_fact agrees_on_actual_head).symm.trans written,truth⟩
  · intro clause used
    cases List.mem_singleton.mp used
    refine ⟨⟨[.variable 0],.cons rfl .nil,?_⟩,fun _ impossible => False.elim (List.not_mem_nil impossible)⟩
    intro i p exp written read compound
    cases List.mem_singleton.mp (List.mem_of_getElem? written)
    exact False.elim (compound 0 rfl)

theorem child_read : ReadBack newState wider richer emitted child childNames place := by
  exact ⟨.cons ⟨bounds,[⟨3,.variable 3⟩],rfl,by
    intro _ found m valid
    cases List.mem_singleton.mp found
    exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _⟩ .nil,
    fun _ _ => bounds,fun _ no => False.elim (List.not_mem_nil no),fun _ no => False.elim (List.not_mem_nil no)⟩

theorem parent_meaning (m : Assignment) (valid : Models newState m) :
    Meaning wider richer m goal parent actualNames.input [emitted] := by
  rw [← exact_child]
  refine local_sound wider_checked List.mem_cons_self rfl
    (fun _ no => False.elim (List.not_mem_nil no)) (fun _ no => False.elim (List.not_mem_nil no))
    parent_read ?_ m valid
  rintro _ ⟨_,no,_⟩
  cases no

theorem child_meaning (m : Assignment) (valid : Models newState m) :
    Meaning wider richer m emitted child childNames.input [] := by
  refine local_sound wider_checked (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) rfl
    (fun _ no => False.elim (List.not_mem_nil no)) (fun _ no => False.elim (List.not_mem_nil no))
    child_read ?_ m valid
  rintro _ ⟨_,no,_⟩
  cases no

end Yulang.GeneralDeclarativeRivalReads324
