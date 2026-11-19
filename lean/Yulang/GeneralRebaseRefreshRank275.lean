import Yulang.GeneralRebaseAllWidthStable275

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 21000
set_option maxHeartbeats 6800000
namespace Yulang.GeneralRebaseRefreshRank275
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralDictionaryOptionalInitial229 (registry)
open GeneralDictionaryVersionedSecondInstall233 (installed installed_model)
open GeneralDictionaryVersionedSecondRaw233 (oldLo oldHi newLo newHi)
open GeneralDictionaryVersionedBothModel233 (extended)
open GeneralRebaseTerminalMixedRefresh274 (raw widthCandidates known_zero known_one known_two)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedObservations233 (Refresh refresh_models)
open GeneralNominalState (Known sources)
open GeneralNominalCommonBridge (Assignment)

abbrev snapshot (state : State roles) := state.core.erased.current.context.state
abbrev FullModelExact (state : State roles) := ∀ m : Assignment, Models state m ↔ Models installed m

structure Anchor (state : State roles) : Prop where
 models : FullModelExact state
 support : ∀ id ∈ sources (snapshot state), id ∈ sources raw
 retains : ∀ id, Known raw id → Known (snapshot state) id

theorem anchor_start : Anchor installed :=
 ⟨fun _ => Iff.rfl,fun _ h => h,fun _ h => h⟩

theorem anchor_next {state : State roles} (anchor : Anchor state) (ctx : GeneralNominalCandidates.Context)
 (cert : Refresh state ctx) : Anchor (GeneralNominalVersionedRefresh232.refresh state ctx) :=
 ⟨fun m => (refresh_models cert).trans (anchor.models m),
  fun id member => anchor.support id (cert.support id member),
  fun id previous => cert.refines.known id (anchor.retains id previous)⟩

/-- Actual checked cache refresh, with the same readiness premises as either
mixed refresh constructor. The unrelated Step constructors are not identified
with these hops. -/
inductive Hop : State roles → State roles → Prop
 | step {state : State roles} (ctx : GeneralNominalCandidates.Context) (cert : Refresh state ctx)
   (id : Nat) (member : id ∈ sources (snapshot state)) (unknown : ¬ Known (snapshot state) id)
   (known : Known ctx.state id) : Hop state (GeneralNominalVersionedRefresh232.refresh state ctx)

theorem step {state next : State roles} (hop : Hop state next) :
 GeneralNominalVersionedMixedKernel234.Step registry root state next := by
 cases hop with
 | step ctx cert id member unknown known =>
   exact ⟨root,.root,.refresh root ctx cert id member unknown known⟩

theorem new_name {state : State roles} (anchor : Anchor state)
 (ctx : GeneralNominalCandidates.Context) (cert : Refresh state ctx) (id : Nat)
 (listed : id ∈ sources (snapshot state)) (unknown : ¬ Known (snapshot state) id) (known : Known ctx.state id) :
 id ∈ widthCandidates := by
 have after := ((anchor_next anchor ctx cert).models extended).mpr installed_model
 obtain ⟨test,observation,head⟩ := GeneralNominalCenteredHeadMatStepCache.known_has_head known
 have holds := GeneralNominalCenteredHeadAllocMergeStable.head_holds head
   (GeneralCanonicalObservations.recorded_sound ctx.state extended after.1.1
     (GeneralNominalSupport.head_recorded head))
 change test.Holds (extended id).1 at holds
 have original := GeneralDictionaryVersionedSecondRaw233.source_support (anchor.support id listed)
 simp only [GeneralDictionaryVersionedSecondRaw233.pool,List.mem_cons,List.not_mem_nil,or_false] at original
 rcases original with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
 · exact False.elim (unknown (anchor.retains _ known_zero))
 · exact False.elim (unknown (anchor.retains _ known_one))
 · exact False.elim (unknown (anchor.retains _ known_two))
 · have e := GeneralDictionaryVersionedSecondEquality233.index_model .three
   change (extended 3).1 = .top at e
   rw [e] at holds
   exact False.elim (GeneralDictionaryGroundCopy218Refresh.top_no_head test holds)
 · have e := GeneralDictionaryVersionedSecondEquality233.index_model .four
   change (extended 4).1 = GeneralDictionaryOptionalOutput229.value at e
   rw [e] at holds
   exact False.elim (GeneralDictionaryOptionalOutput229.no_test test holds)
 · have e := GeneralDictionaryVersionedSecondEquality233.index_model .oldLower
   change (extended oldLo).1 = GeneralDictionaryOptionalOutput229.value at e
   rw [e] at holds
   exact False.elim (GeneralDictionaryOptionalOutput229.no_test test holds)
 · decide +kernel
 · decide +kernel
 · decide +kernel

noncomputable def pending (state : State roles) (id : Nat) : Nat := by
 classical
 exact if Known (snapshot state) id then 0 else 1

noncomputable def rank (state : State roles) : Nat :=
 pending state oldHi + pending state newLo + pending state newHi

theorem pending_le_one (state : State roles) (id : Nat) : pending state id ≤ 1 := by
 unfold pending
 split <;> omega

theorem rank_le_three (state : State roles) : rank state ≤ 3 := by
 have a := pending_le_one state oldHi
 have b := pending_le_one state newLo
 have c := pending_le_one state newHi
 unfold rank
 omega

theorem pending_nonstrict {before after : State roles}
 (retains : ∀ id, Known (snapshot before) id → Known (snapshot after) id)
 (id : Nat) : pending after id ≤ pending before id := by
 classical
 unfold pending
 by_cases hold : Known (snapshot before) id
 · simp only [hold,retains id hold,ite_true,Nat.le_refl]
 · simp only [hold,ite_false]
   split <;> omega

theorem rank_drop {state next : State roles} (anchor : Anchor state) (hop : Hop state next) :
 rank next < rank state := by
 classical
 cases hop with
 | step ctx cert id listed unknown known =>
   let next := GeneralNominalVersionedRefresh232.refresh state ctx
   have strict : pending next id < pending state id := by
     unfold pending
     change (if Known ctx.state id then 0 else 1) < (if Known (snapshot state) id then 0 else 1)
     simp only [known,unknown,ite_true,ite_false,Nat.zero_lt_one]
   have low := pending_nonstrict (after := next) cert.refines.known oldHi
   have mid := pending_nonstrict (after := next) cert.refines.known newLo
   have high := pending_nonstrict (after := next) cert.refines.known newHi
   have which := new_name anchor ctx cert id listed unknown known
   change rank next < rank state
   unfold rank
   simp only [widthCandidates,List.mem_cons,List.not_mem_nil,or_false] at which
   rcases which with rfl|rfl|rfl <;> omega

theorem anchor_hop {state next : State roles} (anchor : Anchor state) (hop : Hop state next) : Anchor next := by
 cases hop with
 | step ctx cert _ _ _ _ => exact anchor_next anchor ctx cert

theorem accessible {state : State roles} (anchor : Anchor state) :
 Acc (fun next before => Hop before next) state := by
 have well := (measure rank).wf.apply state
 induction well with
 | intro state _ ih =>
   constructor
   intro next hop
   apply ih next (rank_drop anchor hop)
   exact anchor_hop anchor hop

inductive Path : State roles → State roles → Nat → Prop
 | empty (state : State roles) : Path state state 0
 | more {start end' next : State roles} {n : Nat} :
    Path start end' n → Hop end' next → Path start next (n+1)

theorem path_rank {start finish : State roles} {n : Nat} (anchor : Anchor start) (path : Path start finish n) :
 Anchor finish ∧ n + rank finish ≤ rank start := by
 induction path with
 | empty => exact ⟨anchor,by simp⟩
 | more path step ih =>
   exact ⟨anchor_hop ih.1 step,by have lower := rank_drop ih.1 step; omega⟩

theorem at_most_three {finish : State roles} {n : Nat} (path : Path installed finish n) : n ≤ 3 := by
 have drop := (path_rank anchor_start path).2
 have initial := rank_le_three installed
 omega

end Yulang.GeneralRebaseRefreshRank275
