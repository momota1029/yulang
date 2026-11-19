import Yulang.GeneralRebaseRefreshEvidence275
import Yulang.GeneralRebaseAllWidthSafety275

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27000
set_option maxHeartbeats 9100000
namespace Yulang.GeneralRebaseRefreshSafety275
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralDictionaryOptionalInitial229 (registry declaration)
open GeneralDictionaryVersionedSecondInstall233 (installed_model)
open GeneralDictionaryVersionedBothModel233 (extended)
open GeneralDictionaryOptionalCycles229
open GeneralNominalRecursiveInspection CommonNominalFullCarrier
open GeneralNominalVersionedJournal232 (State Models)
open GeneralRebaseRefreshClosure275 (Gates)
open GeneralRebaseRefreshEvidence275 (Validated)
open GeneralRebaseRefreshRank275 (snapshot)

variable {state : State roles}

theorem model (gates : Gates state) : Models state extended :=
 (gates.anchor.models extended).mpr installed_model

noncomputable def slotForm (slot : Fin (snapshot state).base.slots) : Form :=
 Classical.choose (GeneralDictionaryVersionedSecondSelected233.model_form ((snapshot state).base.source slot))

theorem slotForm_exact (slot : Fin (snapshot state).base.slots) :
 (extended ((snapshot state).base.source slot)).1 = (slotForm slot).value :=
 Classical.choose_spec (GeneralDictionaryVersionedSecondSelected233.model_form ((snapshot state).base.source slot))

theorem semantic_acyclic (gates : Gates state) (origin) : ¬ GeneralNominalVersionedCycles232.Cyclic state origin :=
 GeneralNominalVersionedAcyclic232.acyclic (model gates) GeneralDictionaryVersionedSecondSelected233.model_form origin

theorem structural_decreases (gates : Gates state) {a b : Fin (snapshot state).base.slots}
 (edge : GeneralSourceK2.Child (snapshot state).view a b) :
 (slotForm b).rank < (slotForm a).rank := by
 obtain ⟨kind,children,recorded,index,rfl⟩ := edge
 let shape := (snapshot state).view.shapes kind
 let values : List Ty := List.ofFn fun index : Fin shape.arity => (extended ((snapshot state).base.source (children index))).1
 have size : values.length = shape.arity := List.length_ofFn
 have found : values[index.val]? = some (extended ((snapshot state).base.source (children index))).1 := by
   simp [values,List.getElem?_ofFn]
   exact index.isLt
 have meaning : Equivalent (extended ((snapshot state).base.source a)).1 (shapeValue shape values) :=
   GeneralNominalFiniteBracket.structural_slot _ extended (model gates).1.1 a kind children recorded rfl
 rw [slotForm_exact a] at meaning
 rw [slotForm_exact (children index)] at found
 obtain ⟨child,smaller,equal⟩ := structural_child (slotForm a) size meaning found
 have eqRank := equivalent_rank (slotForm (children index)) child equal
 omega

theorem nominal_decreases (gates : Gates state) {a b : Fin (snapshot state).base.slots}
 (edge : GeneralNominalMixedRecurrence.ActualArgument (snapshot state) a b) :
 (slotForm b).rank < (slotForm a).rank := by
 obtain ⟨descriptor,_,index,actual,seen,same⟩ :=
   GeneralNominalMixedRecurrence.actual_edge_sound _ a b edge extended (model gates).1.1
 have observation := embed_observation extended _ actual seen
 cases observation with
 | nominal parent equal found =>
   cases parent
   change Equivalent (extended ((snapshot state).base.source a)).1 _ at equal
   rw [slotForm_exact a] at equal
   obtain ⟨child,smaller,meaning⟩ := nominal_child (slotForm a) equal found
   rw [slotForm_exact b] at same
   have eqRank := equivalent_rank child (slotForm b)
     ⟨subtype_trans meaning.2 same.1,subtype_trans same.2 meaning.1⟩
   omega

theorem edge_decreases (gates : Gates state) {a b : Fin (snapshot state).base.slots}
 (edge : GeneralNominalMixedRecurrence.Edge (snapshot state) a b) :
 (slotForm b).rank < (slotForm a).rank :=
 edge.elim (structural_decreases gates) (nominal_decreases gates)

theorem no_raw_recurs (gates : Gates state) (slot : Fin (snapshot state).base.slots) :
 ¬ GeneralNominalCycleK2.RecursAt (snapshot state) slot := by
 intro cycle
 obtain ⟨next,edge,path⟩ := GeneralNominalCycleK2.recurs_cycle _ _ cycle
 have lower := edge_decreases gates edge
 have upper := GeneralRebaseAllWidthSafety275.path_rank (state := snapshot state) (fun slot => (slotForm slot).rank)
   (fun _ _ e => edge_decreases gates e) _ _ path
 omega

theorem known (gates : Gates state) : ¬ GeneralNominalState.RootPending (snapshot state) root.demand := by
 rintro ⟨index,unknown⟩
 obtain ⟨slot,same,desc,seen⟩ := gates.nominal_zero
 exact unknown ⟨slot,same,Or.inr ⟨desc,seen⟩⟩

theorem administrative_ready (gates : Gates state) : GeneralNominalVersionedDiagnostic232.AdministrativeReady state root := by
 refine ⟨⟨_,gates.centers ▸ List.mem_singleton_self _,rfl⟩,?_⟩
 intro first one _ last two _
 rw [gates.centers] at one two
 cases List.mem_singleton.mp one
 cases List.mem_singleton.mp two
 exact .refl _

theorem safe (gates : Gates state) (good : Validated state) :
 B4TargetV8.SafeKnown (GeneralNominalVersionedDiagnostic232.boundary roles) registry state root := by
 obtain ⟨p,frame,_,_,_⟩ := good
 have decl := (GeneralRebaseRefreshFrame275.of_frame frame).declaration_eq
 refine ⟨known gates,?_,?_,?_⟩
 · rintro (raw | (⟨index,cycle⟩ | ⟨site,_,_,index,cycle⟩))
   · obtain ⟨_,_,_,slot,_,cycle⟩ := raw
     exact no_raw_recurs gates slot cycle
   · exact semantic_acyclic gates _ cycle
   · exact semantic_acyclic gates _ cycle
 · rintro (raw | ⟨candidate,framed,entry,_,cycle⟩)
   · obtain ⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ := raw
     exact no_raw_recurs gates visited.1 cycle
   · exact semantic_acyclic gates _ cycle
 · rintro (⟨_,d,visible,_,_,unprepared⟩ | pending)
   · cases List.mem_singleton.mp visible
     exact unprepared (decl ▸ frame.prepared)
   · exact pending (administrative_ready gates)

end Yulang.GeneralRebaseRefreshSafety275
