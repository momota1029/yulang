import Yulang.GeneralRebaseRecordTagBoundary270

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseRecordWindowBoundary270
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedCycles232 (Head Edge Equal)
open GeneralNominalRecursiveInspection (Test Origin)
open GeneralNominalOriginTerms (arity project)
open GeneralRebaseNominalOrigin269 (Raw origin)
open GeneralRebaseStructuralOrigin270 (Slots Kind shape root_shape shape_head projected_equals)
open GeneralRebaseRecordTagBoundary270 (duplicate_head duplicate_tests_not_same duplicate_not_live_full)

theorem alternate_checked (state : State roles) (slot : Slots state) (k : Kind state)
 (child : Fin (shape state k).arity → Slots state) (label : Nat)
 (recorded : (Raw state).view.heads slot = .structural k child)
 (one : shape state k = .record [label]) (m : GeneralNominalCommonBridge.Assignment) (ok : Models state m) :
 ∃ visible, CommonNominalFullCarrier.Equivalent (m ((Raw state).base.source slot)).1
   (CommonNominalFullCarrier.record label visible CommonNominalFullCarrier.emptyRecord) := by
 have fact := root_shape state slot k child recorded m ok
 generalize v : GeneralRebaseStructuralOrigin270.kids state m child = values at fact
 have size : values.length = 1 := by
   rw [← v]
   have size0 : (GeneralRebaseStructuralOrigin270.kids state m child).length = (shape state k).arity := List.length_ofFn ..
   rw [size0,one]
   rfl
 obtain ⟨visible,rfl⟩ := List.length_eq_one_iff.mp size
 rw [one] at fact
 exact ⟨visible,fact⟩

theorem alternate_head (state : State roles) (slot : Slots state) (k : Kind state)
 (child : Fin (shape state k).arity → Slots state) (label : Nat)
 (recorded : (Raw state).view.heads slot = .structural k child)
 (one : shape state k = .record [label]) :
 Head state (origin state slot) (.structural (.record [label,label])) := by
 intro m ok
 obtain ⟨v,known⟩ := alternate_checked state slot k child label recorded one m ok
 exact duplicate_head m _ _ v known

theorem no_literal_exhaustion (state : State roles) (slot : Slots state) (k : Kind state)
 (child : Fin (shape state k).arity → Slots state) (label : Nat)
 (recorded : (Raw state).view.heads slot = .structural k child)
 (one : shape state k = .record [label]) :
 ¬ (∀ t, Head state (origin state slot) t → arity t ≠ 0 → t = .structural (shape state k)) := by
 intro all
 have diff := all _ (alternate_head state slot k child label recorded one) (by change 2 ≠ 0; decide +kernel)
 rw [one] at diff
 exact duplicate_tests_not_same label diff

theorem noncanonical_hidden_excluded (state : State roles) (slot : Slots state) (k : Kind state)
 (child : Fin (shape state k).arity → Slots state) (label : Nat)
 (recorded : (Raw state).view.heads slot = .structural k child)
 (one : shape state k = .record [label]) (witness : ∃ m, Models state m) (target : Origin) :
 ¬ Equal state (.structural (origin state slot) (.record [label,label]) 1) target :=
 duplicate_not_live_full state _ label witness (alternate_checked state slot k child label recorded one) target

theorem canonical_positive (state : State roles) (slot : Slots state) (k : Kind state)
 (child : Fin (shape state k).arity → Slots state)
 (recorded : (Raw state).view.heads slot = .structural k child)
 (i : Fin (shape state k).arity) :
 Edge state (origin state slot) (origin state (child i)) :=
 ⟨origin state slot,.structural (shape state k),i,shape_head state slot k child recorded,
   fun m _ => GeneralNominalOriginTerms.source_self m _,projected_equals state slot k child recorded i⟩

end Yulang.GeneralRebaseRecordWindowBoundary270
