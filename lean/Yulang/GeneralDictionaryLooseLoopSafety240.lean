import Yulang.GeneralDictionaryLooseLoopFull240
import Yulang.GeneralDictionaryLooseLoopInitial240
import Yulang.GeneralDictionaryVersionLoopCycles238
import Yulang.GeneralNominalMixedRecurrence
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryLooseLoopSafety240
open GeneralDictionaryLooseLoopSource240 GeneralDictionaryLooseLoopFrame240
open GeneralDictionaryVersionLoopCycles238
open CommonNominalFullCarrier GeneralNominalRecursiveInspection

def sourceForm : Nat → Form | 0 | 1 => .scalar | 2 => .foo | 3 => .pair | _ => .foo
theorem source_form (identity : Nat) : (model identity).1 = (sourceForm identity).value := by
 cases identity with
 | zero => rfl
 | succ identity => cases identity with
   | zero => rfl
   | succ identity => cases identity with
     | zero => rfl
     | succ identity => cases identity <;> rfl

theorem acyclic (origin) : ¬ GeneralNominalVersionedCycles232.Cyclic initial origin :=
 GeneralDictionaryVersionLoopCycles238.acyclic initial_model (fun n => ⟨sourceForm n,source_form n⟩) origin

theorem raw_edge_decreases {a b : Fin 5} (edge : GeneralNominalMixedRecurrence.Edge snapshot a b) :
    (sourceForm b.val).rank < (sourceForm a.val).rank := by
 rcases edge with structural | nominal
 · obtain ⟨kind,children,recorded,index,child⟩ := structural
   cases recorded
 · obtain ⟨descriptor,recorded,index,actual,seen,same⟩ :=
     GeneralNominalMixedRecurrence.actual_edge_sound snapshot a b nominal model source_model
   have observation := embed_observation model _ actual seen
   cases observation with
   | nominal parent equal found =>
     cases parent
     change Equivalent (model a.val).1 _ at equal
     rw [source_form] at equal
     obtain ⟨child,smaller,meaning⟩ := nominal_child (sourceForm a.val) equal found
     change Equivalent actual (model b.val).1 at same
     rw [source_form] at same
     have ranks := equivalent_rank child (sourceForm b.val)
       ⟨subtype_trans meaning.2 same.1,subtype_trans same.2 meaning.1⟩
     omega

theorem no_raw_recurs (slot : Fin 5) : ¬ GeneralNominalCycleK2.RecursAt snapshot slot := by
 have paths : ∀ a b, GeneralNominalMixedRecurrence.Path snapshot a b →
     (sourceForm b.val).rank ≤ (sourceForm a.val).rank := by
   intro a b path
   induction path with
   | nil => exact Nat.le_refl _
   | cons edge path ih => exact Nat.le_trans ih (Nat.le_of_lt (raw_edge_decreases edge))
 intro cycle
 obtain ⟨next,edge,path⟩ := GeneralNominalCycleK2.recurs_cycle _ _ cycle
 have smaller := raw_edge_decreases edge
 have larger := paths _ _ path
 omega

theorem administrative_ready : GeneralNominalVersionedDiagnostic232.AdministrativeReady initial root := by
 refine ⟨⟨_,List.mem_singleton_self _,rfl⟩,?_⟩
 intro first one same last two _
 cases List.mem_singleton.mp one
 cases List.mem_singleton.mp two
 exact .refl _

theorem safe : B4TargetV8.SafeKnown (GeneralNominalVersionedDiagnostic232.boundary roles) registry initial root := by
 refine ⟨known,?_,?_,?_⟩
 · rintro (old | (⟨index,cycle⟩ | ⟨site,present,same,index,cycle⟩))
   · obtain ⟨_,_,_,slot,_,cycle⟩ := old; exact no_raw_recurs slot cycle
   · exact acyclic _ cycle
   · exact acyclic _ cycle
 · rintro (old | ⟨candidate,framed,entry,member,cycle⟩)
   · obtain ⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ := old; exact no_raw_recurs visited.1 cycle
   · exact acyclic _ cycle
 · rintro (⟨_,d,visible,role,_,unprepared⟩ | unclosed)
   · cases List.mem_singleton.mp visible; exact unprepared prepared
   · exact unclosed administrative_ready
end Yulang.GeneralDictionaryLooseLoopSafety240
