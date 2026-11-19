import Yulang.GeneralRebaseFiniteTree272
import Yulang.GeneralRebaseRecordAlignment271

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseTreeProjection272
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRecursiveInspection (Origin Test Observes shapeValue)
open GeneralNominalOriginTerms (Same Head arity project)
open GeneralNominalFiniteMeaning (At build project_value)
open GeneralNominalReadbackFunctionality (TestCanonical)
open GeneralNominalFiniteHeadInversion renaming head → tag
open GeneralDictionaryInspectionHeads215 (Tagged tag_subtype tagged_test)
open GeneralNominalRecordInversion (record_shape)
open GeneralRebaseRecordReadback271 (same_fields hidden_not_same visible_payload)
open GeneralRebaseRecordIndices271 (Shadowed index_visible)

theorem built_tag (test : Test) (children : Fin (arity test) → Ty) :
 Tagged (build test children) (tag test) := by
 intro env
 exact GeneralNominalFiniteHeadInversion.build_role test children env

theorem model_tag (m : Assignment) (o : Origin) (t u : Test)
 (kids : Fin (arity t) → Ty) (meaning : At m .actual o (build t kids)) (observed : Head m o u) :
 tag t = tag u := by
 obtain ⟨value,saw⟩ := meaning.1
 have rel := meaning.2 _ saw
 exact tag_subtype (built_tag t kids) (tagged_test u (observed.2 _ saw)) rel.2

theorem zip_child (k : Fin n → Ty) (i : Fin n) : (List.ofFn k)[i.val]? = some (k i) := by
 rw [List.getElem?_ofFn]
 split
 · rfl
 · rename_i no
   exact False.elim (no i.isLt)

theorem transport_value (m : Assignment) (a b : Origin) (t x : Ty)
 (seen : Observes m a x) (close : Equivalent x t) (rel : Same m a b) : At m .actual b t := by
 refine ⟨rel.2.1,?_⟩
 intro y there
 have cmp := rel.2.2 _ _ seen there
 exact ⟨subtype_trans cmp.2 close.1,subtype_trans close.2 cmp.1⟩

theorem exact_index (m : Assignment) (first last : Origin) (test : Test) (i : Fin (arity test))
 (children : Fin (arity test) → Ty) (canonical : TestCanonical test)
 (root : At m .actual first (build test children)) (rel : Same m (project first test i) last) :
 At m .actual last (children i) := by
 have observed := project_value test canonical children root i
 obtain ⟨value,seen⟩ := observed.1
 exact transport_value m _ _ _ _ seen (observed.2 value seen) rel

theorem record_index (m : Assignment) (first last : Origin) (keys read : List Nat)
 (children : Fin keys.length → Ty) (layout : keys.Nodup)
 (root : At m .actual first (build (.structural (.record keys)) children))
 (i : Fin read.length) (rel : Same m (.structural first (.record read) i.val) last) :
 ∃ j : Fin keys.length, At m .actual last (children j) := by
 let key := read[i.val]
 have loc : read[i.val]? = some key := List.getElem?_eq_getElem i.isLt
 have visible : ¬ Shadowed read i.val key :=
   fun hidden => hidden_not_same m first last read i.val key loc hidden rel
 obtain ⟨value,seen⟩ := rel.1
 cases seen with
 | structural parent length good whereAt =>
   have equivalent := root.2 _ parent
   have fieldMeaning : Equivalent (shapeValue (.record keys) (List.ofFn children)) (shapeValue (.record read) _) :=
     ⟨subtype_trans equivalent.2 good.1,subtype_trans good.2 equivalent.1⟩
   have existsKey := (same_fields keys read _ _ (List.length_ofFn ..) length fieldMeaning key).mpr
     (List.getElem_mem i.isLt)
   obtain ⟨idx,bounded,atLabel⟩ := List.mem_iff_getElem.mp existsKey
   let j : Fin keys.length := ⟨idx,bounded⟩
   have chosen : keys[idx]? = some key := (List.getElem?_eq_getElem bounded).trans (congrArg some atLabel)
   have inside := visible_payload keys read _ _ (List.length_ofFn ..) length fieldMeaning idx i.val key
     chosen loc (zip_child children j) whereAt (index_visible keys idx key chosen layout) visible
   exact ⟨j,transport_value m _ _ _ _ (.structural parent length good whereAt) ⟨inside.2,inside.1⟩ rel⟩

theorem exact_empty_conflict (m : Assignment) (o : Origin) (read : List Nat)
 (known : At m .actual o exactEmpty) (other : Head m o (.structural (.record read))) : False := by
 obtain ⟨v,saw⟩ := known.1
 obtain ⟨values,size,seen⟩ := other.2 _ saw
 have eq := known.2 _ saw
 rw [record_shape read values size] at seen
 exact GeneralNominalFiniteHeadInversion.record_not_exactEmpty (read.zip values) ⟨subtype_trans seen.2 eq.1,subtype_trans eq.2 seen.1⟩

theorem same_or_records (t u : Test) (h : tag t = tag u) :
 t = u ∨ (tag t = .records ∧ tag u = .records) := by
 cases t <;> cases u
 case scalar.scalar x y => cases h; exact Or.inl rfl
 case nominal.nominal x xn y yn => cases h; exact Or.inl rfl
 case structural.structural x y =>
   cases x <;> cases y <;> cases h <;>
     first | exact Or.inl rfl | exact Or.inr ⟨rfl,rfl⟩
 case scalar.structural _ y => cases y <;> cases h
 case nominal.structural _ _ y => cases y <;> cases h
 case structural.scalar x _ => cases x <;> cases h
 case structural.nominal x _ _ => cases x <;> cases h
 all_goals cases h

/-- An arbitrary old test and live projection must be one of the stored
canonical children, even when the literal record query is reordered
or contains shadowed fields. -/
theorem child_of_live (m : Assignment) (first last : Origin) (test actual : Test)
 (children : Fin (arity test) → Ty) (i : Fin (arity actual))
 (canon : TestCanonical test) (known : At m .actual first (build test children))
 (head : Head m first actual) (rel : Same m (project first actual i) last) :
 ∃ j, At m .actual last (children j) := by
 rcases same_or_records test actual (model_tag m first test actual children known head) with rfl | ⟨t,u⟩
 · exact ⟨i,exact_index m first last test i children canon known rel⟩
 · cases test with
   | scalar | nominal => cases t
   | structural s =>
     cases actual with
     | scalar | nominal => cases u
     | structural a =>
       cases a with
       | pair | variant _ => cases u
       | exactEmpty => exact Fin.elim0 i
       | record read =>
         cases s with
         | pair | variant _ => cases t
         | exactEmpty => exact False.elim (exact_empty_conflict m first read known head)
         | record keys => exact record_index m first last keys read children (canon.imp Nat.ne_of_lt) known i rel

end Yulang.GeneralRebaseTreeProjection272
