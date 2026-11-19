import Yulang.GeneralRebaseAllWidthStable275

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 24500
set_option maxHeartbeats 7800000
namespace Yulang.GeneralRebaseAllWidthSafety275
open GeneralDictionaryOptionalCycles229
open GeneralNominalRecursiveInspection CommonNominalFullCarrier
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralDictionaryOptionalInitial229 (registry declaration)
open GeneralDictionaryVersionedSecondInstall233 (installed installed_model)
open GeneralDictionaryVersionedBothModel233 (extended)
open GeneralRebaseAllWidthRealized275 (successor model_exact)
open GeneralRebaseAllWidthRegistration275 (source viewShapes viewHeads widthSlot)
open GeneralRebaseAllWidthFrame275 (centers frame)
open GeneralNominalVersionedJournal232 (Models)

theorem retained_model : Models successor extended := (model_exact _).mpr installed_model

theorem acyclic (origin) : ¬ GeneralNominalVersionedCycles232.Cyclic successor origin :=
 GeneralNominalVersionedAcyclic232.acyclic retained_model GeneralDictionaryVersionedSecondSelected233.model_form origin

noncomputable def slotForm (slot : Fin 8) : Form :=
 Classical.choose (GeneralDictionaryVersionedSecondSelected233.model_form (source slot))

theorem slotForm_exact (slot : Fin 8) : (extended (source slot)).1 = (slotForm slot).value :=
 Classical.choose_spec (GeneralDictionaryVersionedSecondSelected233.model_form (source slot))

theorem raw_edge_decreases {a b : Fin 8}
 (edge : GeneralNominalMixedRecurrence.Edge successor.core.erased.current.context.state a b) :
 (slotForm b).rank < (slotForm a).rank := by
 rcases edge with structural | nominal
 · obtain ⟨kind,children,recorded,index,_⟩ := structural
   change viewHeads a = .structural kind children at recorded
   unfold viewHeads at recorded
   split at recorded
   · cases recorded
     exact Fin.elim0 index
   · cases recorded
 · obtain ⟨descriptor,_,index,actual,seen,same⟩ :=
     GeneralNominalMixedRecurrence.actual_edge_sound _ a b nominal extended retained_model.1.1
   have observation := embed_observation extended _ actual seen
   cases observation with
   | nominal parent equal found =>
     cases parent
     change Equivalent (extended (source a)).1 _ at equal
     rw [slotForm_exact a] at equal
     obtain ⟨child,smaller,meaning⟩ := nominal_child (slotForm a) equal found
     change Equivalent _ (extended (source b)).1 at same
     rw [slotForm_exact b] at same
     have rankEq := equivalent_rank child (slotForm b)
       ⟨subtype_trans meaning.2 same.1,subtype_trans same.2 meaning.1⟩
     omega

theorem path_rank {state : GeneralNominalState.State} (rank : Fin state.base.slots → Nat)
 (decrease : ∀ a b, GeneralNominalMixedRecurrence.Edge state a b → rank b < rank a)
 (a b : Fin state.base.slots) (path : GeneralNominalMixedRecurrence.Path state a b) :
 rank b ≤ rank a := by
 induction path with
 | nil => exact Nat.le_refl _
 | cons edge _ ih => exact Nat.le_trans ih (Nat.le_of_lt (decrease _ _ edge))

theorem no_raw_recurs (slot : Fin 8) :
 ¬ GeneralNominalCycleK2.RecursAt successor.core.erased.current.context.state slot := by
 intro cycle
 obtain ⟨next,edge,path⟩ := GeneralNominalCycleK2.recurs_cycle _ _ cycle
 have lower := raw_edge_decreases edge
 have upper := path_rank (state := successor.core.erased.current.context.state) (fun slot => (slotForm slot).rank)
   (fun _ _ edge => raw_edge_decreases edge) _ _ path
 omega

theorem known : ¬ GeneralNominalState.RootPending successor.core.erased.current.context.state root.demand := by
 rintro ⟨index,unknown⟩
 exact unknown (GeneralRebaseAllWidthRefinement275.refines.known _ GeneralRebaseTerminalMixedRefresh274.known_zero)

theorem administrative_ready : GeneralNominalVersionedDiagnostic232.AdministrativeReady successor root := by
 refine ⟨⟨_,centers ▸ List.mem_singleton_self _,rfl⟩,?_⟩
 intro first one _ last two _
 rw [centers] at one two
 cases List.mem_singleton.mp one
 cases List.mem_singleton.mp two
 exact .refl _

theorem safe : B4TargetV8.SafeKnown (GeneralNominalVersionedDiagnostic232.boundary roles) registry successor root := by
 refine ⟨known,?_,?_,?_⟩
 · rintro (raw | (⟨index,cycle⟩ | ⟨site,_,_,index,cycle⟩))
   · obtain ⟨_,_,_,slot,_,cycle⟩ := raw; exact no_raw_recurs slot cycle
   · exact acyclic _ cycle
   · exact acyclic _ cycle
 · rintro (raw | ⟨candidate,framed,entry,_,cycle⟩)
   · obtain ⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ := raw; exact no_raw_recurs visited.1 cycle
   · exact acyclic _ cycle
 · rintro (⟨_,d,visible,_,_,unprepared⟩ | unready)
   · cases List.mem_singleton.mp visible; exact unprepared frame.prepared
   · exact unready administrative_ready

end Yulang.GeneralRebaseAllWidthSafety275
