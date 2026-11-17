import Yulang.GeneralDictionaryLooseIterationFrame240
import Yulang.GeneralDictionaryLooseIterationFresh240
import Yulang.GeneralDictionaryLooseLoopSafety240
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryLooseIterationSafety240
open GeneralDictionaryLooseLoopSource240 (roles registry root model)
open GeneralDictionaryLooseIterationBook240 GeneralDictionaryLooseIterationFrame240
open GeneralDictionaryLooseLoopSafety240 (sourceForm source_form)
open GeneralDictionaryVersionLoopCycles238
open CommonNominalFullCarrier GeneralNominalRecursiveInspection

theorem raw_edge_decreases (n) {a b : Fin (n+5)} (edge : GeneralNominalMixedRecurrence.Edge (context n).state a b) :
    (sourceForm ((context n).state.base.source b)).rank < (sourceForm ((context n).state.base.source a)).rank := by
 rcases edge with structural | nominal
 · obtain ⟨kind,children,recorded,index,child⟩ := structural
   cases recorded
 · obtain ⟨descriptor,recorded,index,actual,seen,same⟩ :=
     GeneralNominalMixedRecurrence.actual_edge_sound (context n).state a b nominal model (packet_holds n).1
   have observation := embed_observation model _ actual seen
   cases observation with
   | nominal parent equal found =>
     cases parent
     change Equivalent (model ((context n).state.base.source a)).1 _ at equal
     rw [source_form] at equal
     obtain ⟨child,smaller,meaning⟩ := nominal_child (sourceForm ((context n).state.base.source a)) equal found
     change Equivalent actual (model ((context n).state.base.source b)).1 at same
     rw [source_form] at same
     have ranks := equivalent_rank child (sourceForm ((context n).state.base.source b))
       ⟨subtype_trans meaning.2 same.1,subtype_trans same.2 meaning.1⟩
     omega

theorem no_raw_recurs (n) (slot : Fin (n+5)) : ¬ GeneralNominalCycleK2.RecursAt (context n).state slot := by
 have paths : ∀ a b, GeneralNominalMixedRecurrence.Path (context n).state a b →
     (sourceForm ((context n).state.base.source b)).rank ≤ (sourceForm ((context n).state.base.source a)).rank := by
   intro a b path
   induction path with
   | nil => exact Nat.le_refl _
   | cons edge path ih => exact Nat.le_trans ih (Nat.le_of_lt (raw_edge_decreases n edge))
 intro cycle
 obtain ⟨next,edge,path⟩ := GeneralNominalCycleK2.recurs_cycle _ _ cycle
 have smaller := raw_edge_decreases n edge
 have larger := paths _ _ path
 omega

theorem administrative_ready (shape : Shape journal n) : GeneralNominalVersionedDiagnostic232.AdministrativeReady journal root := by
 refine ⟨⟨_,(by rw [shape.centers]; exact List.mem_singleton_self _),rfl⟩,?_⟩
 intro first one same last two _
 cases List.mem_singleton.mp (shape.centers ▸ one)
 cases List.mem_singleton.mp (shape.centers ▸ two)
 exact .refl _

theorem acyclic (valid : GeneralNominalVersionedJournal232.Models journal model) (origin) :
 ¬ GeneralNominalVersionedCycles232.Cyclic journal origin :=
 GeneralDictionaryVersionLoopCycles238.acyclic valid (fun name => ⟨sourceForm name,source_form name⟩) origin

theorem safe (shape : Shape journal n) (valid : GeneralNominalVersionedJournal232.Models journal model) :
 B4TargetV8.SafeKnown (GeneralNominalVersionedDiagnostic232.boundary roles) registry journal root := by
 refine ⟨?_,?_,?_,?_⟩
 · change ¬ GeneralNominalState.RootPending journal.core.erased.current.context.state root.demand
   rw [shape.current]; exact known n
 · rintro (old | (⟨index,cycle⟩ | ⟨site,present,same,index,cycle⟩))
   · rw [shape.current] at old
     obtain ⟨_,_,_,slot,_,cycle⟩ := old; exact no_raw_recurs n slot cycle
   · exact acyclic valid _ cycle
   · exact acyclic valid _ cycle
 · rintro (old | ⟨candidate,framed,entry,member,cycle⟩)
   · rw [shape.current] at old
     obtain ⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ := old; exact no_raw_recurs n visited.1 cycle
   · exact acyclic valid _ cycle
 · rintro (⟨_,d,visible,role,_,unprepared⟩ | unclosed)
   · cases List.mem_singleton.mp visible
     rw [shape.current] at unprepared
     exact unprepared (prepared n (GeneralDictionaryLooseIterationFresh240.fresh n))
   · exact unclosed (administrative_ready shape)
end Yulang.GeneralDictionaryLooseIterationSafety240
