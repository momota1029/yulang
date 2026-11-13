import Yulang.GeneralDictionaryNestedRefinementExamples

/-! An explicit 8-to-9 carrier refinement of the positive nested source.
This is a Refines regression, not a claim of a Value refresh step: its fresh
source is unconstrained rather than introduced from a reserved source. -/
namespace Yulang.GeneralDictionaryNestedCarrierExample
open GeneralNominalRefinements GeneralNominalRecursiveInspection
open GeneralNominalProvenanceSource
open GeneralDictionaryNestedRefinement
open GeneralDictionaryNestedRefinementExamples (query bounds nested_scope nested_finished)

abbrev embed (slot : Fin 8) : Fin 9 := ⟨slot.val,by omega⟩
def entries (slot : Fin 9) : Option (GeneralNominalState.Descriptor 9) :=
 if h : slot.val < 8 then (state.nominals ⟨slot.val,h⟩).map (renameDescriptor embed) else none

abbrev after : GeneralNominalState.State where
 base := GeneralNominalOutputGrowthModels.base 7
 view := GeneralNominalOutputGrowthModels.view 7
 constructors := state.constructors
 nominals := entries
 catalogue := by
   intro slot d h
   unfold entries at h
   split at h
   · obtain ⟨old,oldMem,eq⟩ := Option.map_eq_some_iff.mp h
     subst d
     exact state.catalogue _ _ oldMem
   · cases h
 bodies_opaque := by intro _ _ _; rfl
 seed := state.seed

theorem retained (slot : Fin 8) (d : GeneralNominalState.Descriptor 8)
 (recorded : state.nominals slot = some d) :
 after.nominals (embed slot) = some (renameDescriptor embed d) := by
 change entries (embed slot) = _
 simp only [entries,slot.isLt,↓reduceDIte]
 change Option.map (renameDescriptor embed) (state.nominals slot) = _
 rw [recorded]
 rfl

def refinement : Refines state after where
 base := ⟨embed,fun _ => rfl,fun _ => rfl,(by intro _ member; cases member),
   (by intro _ known; exact False.elim (known rfl)),(by intro _ member; cases member)⟩
 heads := by intro _ _ recorded; cases recorded
 nominals := retained
 ordinary := by intro _ member; cases member
 known := by
   rintro identity ⟨slot,equal,head | nominal⟩
   · exact False.elim (head rfl)
   · obtain ⟨d,recorded⟩ := nominal
     exact ⟨embed slot,equal,Or.inr ⟨_,retained slot d recorded⟩⟩
 reserved := by intro _ member; cases member
 allocated := by intro _ member; cases member
 seed := rfl
 constructors := rfl

private theorem fits_forward (a b : GeneralNominalState.State) (r : Refines a b)
 (ps : List (GeneralNominalState.Parameter a.base.slots))
 (values : List CommonNominalFullCarrier.Argument) (m : GeneralNominalCommonBridge.Assignment)
 (fits : GeneralNominalState.FitsAll a.base m ps values) :
 GeneralNominalState.FitsAll b.base m (ps.map (renameParameter r.base.embed)) values := by
 induction fits with
 | nil => exact .nil
 | @cons p v ps vs h hs ih => exact .cons ((fits_transport r _ p v).mpr h) ih

theorem model_preserved (a b u : CommonNominalFullCarrier.Ty) :
 GeneralNominalState.Models after (model a b u) := by
 refine ⟨⟨PresenceNormalForm.all_nil _ _,?_,?_⟩,?_,PresenceNormalForm.all_nil _ _⟩
 · intro _ _ h; cases h
 · intro _ h; cases h
 · intro slot d recorded
   change entries slot = some d at recorded
   unfold entries at recorded
   split at recorded
   · rename_i h
     obtain ⟨old,oldMem,eq⟩ := Option.map_eq_some_iff.mp recorded
     subst d
     obtain ⟨args,fits,equivalent⟩ := (source_models a b u).2.1 _ _ oldMem
     refine ⟨args,?_,equivalent⟩
     exact fits_forward state after refinement _ _ _ fits
   · cases recorded

theorem carrier_strictly_larger : state.base.slots < after.base.slots := by decide +kernel

theorem nested_report_transported : inspect after query (mapBounds refinement.base.embed bounds) none =
 mapReport refinement.base.embed (inspect state query bounds none) :=
 inspect_refined state after refinement query bounds none nested_scope nested_finished

theorem capture_sources_retained : bindings after (inspect after query (mapBounds refinement.base.embed bounds) none) =
 [(7,2,2),(7,5,5)] := by
 rw [nested_report_transported,bindings_map]
 exact GeneralDictionaryNestedRefinementExamples.captures_two_sources

end Yulang.GeneralDictionaryNestedCarrierExample
