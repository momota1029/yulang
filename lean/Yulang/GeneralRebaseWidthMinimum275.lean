import Yulang.GeneralRebaseRefreshRank275

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
set_option maxHeartbeats 6400000
namespace Yulang.GeneralRebaseWidthMinimum275
open GeneralDictionaryJournalRefinement228Source (roles)
open GeneralDictionaryVersionedSecondInstall233 (installed)
open GeneralDictionaryVersionedSecondRaw233 (oldHi newLo newHi)
open GeneralRebaseTerminalMixedRefresh274 (widthCandidates)
open GeneralRebaseAllWidthRealized275 (successor)
open GeneralRebaseRefreshRank275 (Hop Path snapshot)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalState (Known)

def typeIDs : List Nat := [0,1,2,3,4,oldHi,newLo,newHi]

theorem typeIDs_nodup : typeIDs.Nodup := by decide +kernel

theorem keeps_old {begin finish : State roles} {n : Nat} (path : Path begin finish n) :
 ∀ id, (∃ slot, (snapshot begin).base.source slot = id) →
   ∃ slot, (snapshot finish).base.source slot = id := by
 induction path with
 | empty => exact fun _ present => present
 | more _ hop ih =>
   cases hop with
   | step ctx cert _ _ _ _ =>
     intro id present
     obtain ⟨slot,equal⟩ := ih id present
     exact ⟨cert.refines.base.embed slot,(cert.refines.base.source slot).trans equal⟩

theorem at_least_eight {finish : State roles} {n : Nat} (path : Path installed finish n)
 (all : ∀ id ∈ widthCandidates, Known (snapshot finish) id) : 8 ≤ (snapshot finish).base.slots := by
 have covered : typeIDs ⊆ List.ofFn (snapshot finish).base.source := by
   intro id present
   simp only [typeIDs,List.mem_cons,List.not_mem_nil,or_false] at present
   apply List.mem_ofFn.mpr
   rcases present with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
   · exact keeps_old path 0 ⟨(0 : Fin 5),rfl⟩
   · exact keeps_old path 1 ⟨(1 : Fin 5),rfl⟩
   · exact keeps_old path 2 ⟨(2 : Fin 5),rfl⟩
   · exact keeps_old path 3 ⟨(3 : Fin 5),rfl⟩
   · exact keeps_old path 4 ⟨(4 : Fin 5),rfl⟩
   · obtain ⟨slot,equal,_⟩ := all oldHi (by decide +kernel)
     exact ⟨slot,equal⟩
   · obtain ⟨slot,equal,_⟩ := all newLo (by decide +kernel)
     exact ⟨slot,equal⟩
   · obtain ⟨slot,equal,_⟩ := all newHi (by decide +kernel)
     exact ⟨slot,equal⟩
 simpa only [List.length_ofFn,show typeIDs.length = 8 from rfl] using List.Nodup.length_le_of_subset typeIDs_nodup covered


theorem batch_is_minimal :
 (snapshot successor).base.slots = 8 ∧
 ∃ _path : Path installed successor 1, ∀ id ∈ widthCandidates, Known (snapshot successor) id := by
 refine ⟨rfl,?_,GeneralRebaseAllWidthRealized275.all_three_known⟩
 exact .more (.empty _) (.step _ GeneralRebaseAllWidthCertificate275.certificate oldHi
   (GeneralRebaseTerminalMixedRefresh274.candidates_tracked oldHi List.mem_cons_self)
   (GeneralRebaseTerminalMixedRefresh274.candidates_novel oldHi List.mem_cons_self)
   (GeneralRebaseAllWidthRealized275.all_three_known oldHi List.mem_cons_self))

end Yulang.GeneralRebaseWidthMinimum275
