import Yulang.GeneralRebaseLocalOriginPocket271
import Yulang.GeneralRebaseOutputDepthPocket271

namespace Yulang.GeneralRebaseRawIntoFull271
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedCycles232 (Equal Head Edge Path Cyclic RootCycle)
open GeneralRebaseNominalOrigin269 (Raw origin)
open GeneralRebaseStructuralOrigin270 (Slots)
open GeneralNominalCycleK2 (RecursAt)
open GeneralRebasePartialBool268 (Answer Reflect)
open GeneralSourceDictionaries (Occurrence)

theorem raw_edge (state : State roles) (full : ∃ m, Models state m) (a b : Slots state)
 (step : GeneralNominalMixedRecurrence.Edge (Raw state) a b) :
 Edge state (origin state a) (origin state b) := by
 rcases step with ⟨kind,children,recorded,i,rfl⟩ | ⟨desc,recorded,index,rel⟩
 · exact GeneralRebaseRecordWindowBoundary270.canonical_positive state a kind children recorded i
 · obtain ⟨m,valid⟩ := full
   obtain ⟨actual,seen,_⟩ := rel m valid.1.1
   obtain ⟨id,_,same⟩ := GeneralRebaseActualArguments269.bounded_of_observed (Raw state) m valid.1.1
     a desc recorded index actual seen
   have matching : GeneralRebaseActualArguments269.Member (Raw state) a b desc id.val :=
     same.symm ▸ rel
   exact ⟨origin state a,GeneralRebaseNominalOrigin269.tag desc,id,
     GeneralRebaseNominalOrigin269.head state a desc recorded,
     fun m _ => GeneralNominalOriginTerms.source_self m _,
     GeneralRebaseNominalOrigin269.member_equal state a b desc id matching⟩

theorem raw_path (state : State roles) (full : ∃ m, Models state m)
 {a b : Slots state} (walk : GeneralNominalMixedRecurrence.Path (Raw state) a b) :
 Path state (origin state a) (origin state b) := by
 induction walk with
 | nil => exact .nil _
 | cons e _ ih => exact .cons (raw_edge state full _ _ e) ih

theorem recurs (state : State roles) (full : ∃ m, Models state m) (s : Slots state)
 (actual : RecursAt (Raw state) s) :
 Cyclic state (origin state s) := by
 obtain ⟨first,edge,path⟩ := GeneralNominalCycleK2.recurs_cycle _ _ actual
 exact ⟨⟨origin state first,raw_edge state full s first edge,raw_path state full path⟩,full⟩

theorem root_from_raw (state : State roles) (full : ∃ m, Models state m) (root : Occurrence roles)
 (actual : GeneralNominalCycleK2.RootK2 (Raw state) (GeneralNominalVersionedCandidates231.inputs root).demand) :
 RootCycle state root := by
 obtain ⟨_,_,i,s,source,cycled⟩ := actual
 have v := recurs state full s cycled
 unfold origin at v
 rw [source] at v
 exact Or.inl ⟨i,v⟩

theorem root_exact (registry : GeneralDeclarations.Registry) (state : State roles) (full : ∃ m, Models state m)
 (root : Occurrence roles) :
 ((GeneralRebaseSourceSurvivor267.Boundary roles).RootK2 registry state root) ↔ RootCycle state root :=
 ⟨fun h => h.elim (root_from_raw state full root) id,Or.inr⟩

def execute (state : State roles) (root : Occurrence roles) : Answer :=
 GeneralRebaseLocalOriginPocket271.rootOrigin state root

theorem execute_sound (registry : GeneralDeclarations.Registry) (state : State roles) (full : ∃ m, Models state m)
 (root : Occurrence roles) :
 Reflect ((GeneralRebaseSourceSurvivor267.Boundary roles).RootK2 registry state root) (execute state root) :=
 GeneralRebasePartialFinite268.transfer (root_exact registry state full root).symm
   (GeneralRebaseLocalOriginPocket271.rootOrigin_sound state full root)

namespace Actual252
open GeneralDictionaryOutputDepth252 (initial root sourceRegistry model initial_model)
open GeneralRebaseOutputDepthPocket271 (inspected unchanged diagnostic actual_model)
open GeneralRebaseScalarSnapshot271 (initial_sites)
open GeneralRebaseJournalMeaning271 renaming root → transportRoot

theorem computed : execute inspected root = some false := diagnostic

theorem actual_k2_clear : ¬ (GeneralRebaseSourceSurvivor267.Boundary GeneralDictionaryOutputDepth252.roles).RootK2
 sourceRegistry initial root := by
 have known := execute_sound sourceRegistry inspected ⟨model,actual_model⟩ root
 rw [computed] at known
 intro denied
 have onSource := (root_exact sourceRegistry initial ⟨model,initial_model⟩ root).mp denied
 have localCycle := (transportRoot unchanged (initial_sites GeneralDictionaryOutputDepth252.context root) root).mpr onSource
 exact known ((root_exact sourceRegistry inspected ⟨model,actual_model⟩ root).mpr localCycle)

end Actual252
end Yulang.GeneralRebaseRawIntoFull271
