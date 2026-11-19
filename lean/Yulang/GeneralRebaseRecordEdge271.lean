import Yulang.GeneralRebaseRecordReadback271
import Yulang.GeneralRebaseRecordWindowBoundary270

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseRecordEdge271
open CommonNominalFullCarrier
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedCycles232 (Equal Edge Head)
open GeneralNominalOriginTerms (project arity)
open GeneralNominalRecursiveInspection (Origin Test Observes shapeValue)
open GeneralNominalCommonBridge (Assignment)
open GeneralNormalizedObservation (Shape)
open GeneralRebaseNominalOrigin269 (Raw origin)
open GeneralRebaseStructuralOrigin270 (Slots Kind shape kids root_shape shape_head same_tag projected_equals)
open GeneralRebaseRecordReadback271 (same_fields hidden_not_same visible_matches_canonical)
open GeneralRebaseRecordIndices271 (Shadowed)
open GeneralRebaseOriginCongruence269 (edge_normal)
open GeneralRebaseRecordWindowBoundary270 (canonical_positive)

theorem slot_payload (state : State roles) (k : Kind state) (m : Assignment)
 (child : Fin (shape state k).arity → Slots state) (j : Fin (shape state k).arity) :
 (kids state m child)[j.val]? = some (m ((Raw state).base.source (child j))).1 := by
 unfold kids
 rw [List.getElem?_ofFn]
 split
 · rfl
 · rename_i no
   exact False.elim (no j.isLt)

theorem matches_child (state : State roles) (slot : Slots state) (k : Kind state) (keys read : List Nat)
 (child : Fin (shape state k).arity → Slots state)
 (recorded : (Raw state).view.heads slot = .structural k child) (isRecord : shape state k = .record keys)
 (inhabited : ∃ m, Models state m) (i : Fin read.length) (dest : Origin)
 (rel : Equal state (.structural (origin state slot) (.record read) i.val) dest) :
 ∃ j, Equal state (origin state (child j)) dest := by
 have size (m : Assignment) : (kids state m child).length = keys.length := by
   calc
    _ = (shape state k).arity := List.length_ofFn ..
    _ = _ := by rw [isRecord]; rfl
 have layout : keys.Nodup := by
   have canonical := (Raw state).view.canonical k
   change (shape state k).Canonical at canonical
   rw [isRecord] at canonical
   exact canonical.imp Nat.ne_of_lt
 have observed (m : Assignment) (good : Models state m) :
   Equivalent (m ((Raw state).base.source slot)).1 (shapeValue (.record keys) (kids state m child)) := by
   have raw := root_shape state slot k child recorded m good
   rw [isRecord] at raw
   exact raw
 let key := read[i.val]
 have loc : read[i.val]? = some key := List.getElem?_eq_getElem i.isLt
 obtain ⟨m,valid⟩ := inhabited
 have visible : ¬ Shadowed read i.val key :=
   fun hidden => hidden_not_same m _ dest read i.val key loc hidden (rel m valid)
 have listed : key ∈ keys := by
   obtain ⟨val,saw⟩ := (rel m valid).1
   cases saw with
   | structural parent len shapeOK childOK =>
     cases parent
     apply (same_fields keys read (kids state m child) _ (size m) len _ key).mpr
     · exact List.getElem_mem i.isLt
     · exact ⟨subtype_trans (observed m valid).2 shapeOK.1,subtype_trans shapeOK.2 (observed m valid).1⟩
 obtain ⟨j,jBound,atKey⟩ := List.mem_iff_getElem.mp listed
 let position : Fin (shape state k).arity := ⟨j,by rw [isRecord]; exact jBound⟩
 have measure : keys[position.val]? = some key := (List.getElem?_eq_getElem jBound).trans (congrArg some atKey)
 refine ⟨position,?_⟩
 intro assignment good
 have pair := rel assignment good
 refine ⟨⟨_,.source _⟩,pair.2.1,?_⟩
 intro x y one two
 cases one
 obtain ⟨w,there⟩ := pair.1
 have same := visible_matches_canonical assignment _ keys read (kids state assignment child) (size assignment)
   (observed assignment good) position.val i.val key measure loc layout visible (slot_payload state k assignment child position) there
 have last := pair.2.2 _ _ there two
 exact ⟨subtype_trans same.1 last.1,subtype_trans last.2 same.2⟩

/-- The original unrestricted tests may have duplicates or a different
order. Only first-visible positions can be edges, so the stored
canonical children exhaust all semantic edges. -/
theorem record_edge_iff (state : State roles) (slot : Slots state) (k : Kind state) (keys : List Nat)
 (child : Fin (shape state k).arity → Slots state)
 (recorded : (Raw state).view.heads slot = .structural k child) (isRecord : shape state k = .record keys)
 (inhabited : ∃ m, Models state m) (dest : Origin) :
 Edge state (origin state slot) dest ↔ ∃ j, Equal state (origin state (child j)) dest := by
 constructor
 · intro step
   obtain ⟨_live,t,i,head,equal⟩ := (edge_normal state _ _).mp step
   have tag := same_tag state slot inhabited (.structural (shape state k)) t (shape_head state slot k child recorded) head
   rw [isRecord] at tag
   cases t with
   | scalar _ => cases tag
   | nominal _ _ => cases tag
   | structural s =>
     cases s with
     | pair | variant _ => cases tag
     | exactEmpty => exact Fin.elim0 i
     | record labels => exact matches_child state slot k keys labels child recorded isRecord inhabited i dest equal
 · rintro ⟨j,eq⟩
   exact ⟨origin state slot,.structural (shape state k),j,shape_head state slot k child recorded,
      fun m _ => GeneralNominalOriginTerms.source_self m _,
      GeneralRebaseOriginCongruence269.equal_trans (projected_equals state slot k child recorded j) eq⟩

theorem exactEmpty_no_edge (state : State roles) (slot : Slots state) (k : Kind state)
 (child : Fin (shape state k).arity → Slots state)
 (recorded : (Raw state).view.heads slot = .structural k child) (isEmpty : shape state k = .exactEmpty)
 (inhabited : ∃ m, Models state m) (dest : Origin) :
 ¬ Edge state (origin state slot) dest := by
 intro route
 obtain ⟨_live,t,i,head,_⟩ := (edge_normal state _ _).mp route
 have tag := same_tag state slot inhabited (.structural (shape state k)) t (shape_head state slot k child recorded) head
 rw [isEmpty] at tag
 cases t with
 | scalar _ => cases tag
 | nominal _ _ => cases tag
 | structural s =>
   cases s with
   | pair | variant _ => cases tag
   | exactEmpty => exact Fin.elim0 i
   | record labels =>
     obtain ⟨m,valid⟩ := inhabited
     obtain ⟨values,sz,other⟩ := (head m valid).2 _ (.source _)
     have root := root_shape state slot k child recorded m valid
     rw [isEmpty] at root
     rw [GeneralNominalRecordInversion.record_shape labels values sz] at other
     exact GeneralNominalFiniteHeadInversion.record_not_exactEmpty (labels.zip values)
        ⟨subtype_trans other.2 root.1,subtype_trans root.2 other.1⟩

/-- Every normalized structural shape has exact semantic edge support,
including records whose original test positions are not canonical. -/
theorem structural_edge_iff (state : State roles) (slot : Slots state) (k : Kind state)
 (child : Fin (shape state k).arity → Slots state)
 (recorded : (Raw state).view.heads slot = .structural k child)
 (inhabited : ∃ m, Models state m) (dest : Origin) :
 Edge state (origin state slot) dest ↔ ∃ j, Equal state (origin state (child j)) dest := by
 have classify (s : Shape) : (∃ keys, s = .record keys) ∨
   GeneralRebaseStructuralOrigin270.Rigid s = true ∨ s = .exactEmpty := by
   cases s with
   | record labels => exact Or.inl ⟨labels,rfl⟩
   | pair | variant _ => exact Or.inr (Or.inl rfl)
   | exactEmpty => exact Or.inr (Or.inr rfl)
 rcases classify (shape state k) with ⟨labels,known⟩ | rigid | known
 · exact record_edge_iff state slot k labels child recorded known inhabited dest
 · exact GeneralRebaseStructuralOrigin270.rigid_edge_iff state slot k child recorded rigid inhabited dest
 · have zero : (shape state k).arity = 0 := by rw [known]; rfl
   constructor
   · exact fun h => False.elim (exactEmpty_no_edge state slot k child recorded known inhabited dest h)
   · rintro ⟨idx,_⟩
     have impossible : idx.val < 0 := zero ▸ idx.isLt
     exact False.elim (Nat.not_lt_zero _ impossible)

end Yulang.GeneralRebaseRecordEdge271
