import Yulang.GeneralRebaseTreeNominal272

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseTreeRecord272
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRecursiveInspection (Origin Observes shapeValue)
open GeneralNominalFiniteMeaning (At build)
open GeneralRebaseFiniteTree272 (Tree value Canonical)
open GeneralRebaseTreeReadbackState272 (Result Meaning no_structural_position)
open GeneralRebaseRecordAlignment271 (visibleSet visibleSet_exact align aligned mapped_nth)
open GeneralRebaseRecordReadback271 (same_fields visible_payload hidden_observes)
open GeneralRebaseRecordIndices271 (Shadowed first_at index_visible)
open GeneralRebaseTreeProjection272 (zip_child)

def fromRecord (keys read : List Nat) (children : Fin keys.length → Tree) (index : Nat) : Result :=
 match read[index]? with
 | none => .absent
 | some key =>
   if visibleSet keys read then
     if key ∈ read.take index then .many
     else match (List.finRange keys.length).find? (fun j => keys[j.val]? == some key) with
       | some j => .found (children j)
       | none => .unknown
   else .absent

theorem aligned_observes (m : Assignment) (p : Origin) (keys read : List Nat) (xs : List Ty)
 (length : xs.length = keys.length) (known : At m .actual p (shapeValue (.record keys) xs))
 (fits : visibleSet keys read = true) (i : Nat) (child : Ty)
 (shown : (align keys xs read)[i]? = some child) :
 Observes m (.structural p (.record read) i) child := by
 obtain ⟨first,seen⟩ := known.1
 have eq := known.2 first seen
 have alignEq := aligned keys xs read length fits
 exact .structural seen (List.length_map ..) ⟨subtype_trans eq.1 alignEq.1,subtype_trans alignEq.2 eq.2⟩ shown

theorem visible_at (m : Assignment) (p : Origin) (keys read : List Nat) (xs : List Ty)
 (length : xs.length = keys.length) (known : At m .actual p (shapeValue (.record keys) xs))
 (fits : visibleSet keys read = true) (i j key : Nat) (first : keys[j]? = some key)
 (readable : read[i]? = some key) (can : keys.Nodup) (unhidden : ¬ Shadowed read i key)
 (v : Ty) (whereAt : xs[j]? = some v) :
 At m .actual (.structural p (.record read) i) v := by
 have selected := first_at keys xs j key v first whereAt (index_visible keys j key first can)
 have direct := aligned_observes m p keys read xs length known fits i v (mapped_nth keys xs read i key v readable selected)
 refine ⟨⟨v,direct⟩,?_⟩
 intro later seen
 cases seen with
 | structural parent size eq found =>
   have original := known.2 _ parent
   have same : Equivalent (shapeValue (.record keys) xs) (shapeValue (.record read) _) :=
     ⟨subtype_trans original.2 eq.1,subtype_trans eq.2 original.1⟩
   have agrees := visible_payload keys read _ _ length size same j i key first readable whereAt found
     (index_visible keys j key first can) unhidden
   exact ⟨agrees.2,agrees.1⟩

theorem shadow_many (m : Assignment) (p : Origin) (keys read : List Nat) (xs : List Ty)
 (length : xs.length = keys.length) (known : At m .actual p (shapeValue (.record keys) xs))
 (fits : visibleSet keys read = true) (i key : Nat) (hit : read[i]? = some key)
 (later : Shadowed read i key) :
 Meaning m (.structural p (.record read) i) .many := by
 intro anyValue
 have inside : i < (align keys xs read).length := by
   rw [show (align keys xs read).length = read.length from List.length_map ..]
   exact (List.getElem?_eq_some_iff.mp hit).1
 have visible := aligned_observes m p keys read xs length known fits i _
   (List.getElem?_eq_getElem inside)
 exact hidden_observes m p read i key hit later ⟨_,visible⟩ anyValue

theorem disjoint (m : Assignment) (p : Origin) (keys read : List Nat) (xs : List Ty)
 (length : xs.length = keys.length) (known : At m .actual p (shapeValue (.record keys) xs))
 (away : visibleSet keys read ≠ true) (i : Nat) :
 Meaning m (.structural p (.record read) i) .absent := by
 intro actual seen
 cases seen with
 | structural root size tight atVal =>
   have record := known.2 _ root
   have same : Equivalent (shapeValue (.record keys) xs) (shapeValue (.record read) _) :=
     ⟨subtype_trans record.2 tight.1,subtype_trans tight.2 record.1⟩
   exact away ((visibleSet_exact _ _).mpr (fun key => same_fields keys read _ _ length size same key))

theorem sound (m : Assignment) (p : Origin) (keys read : List Nat) (children : Fin keys.length → Tree) (i : Nat)
 (canon : keys.Nodup) (known : At m .actual p (build (.structural (.record keys)) (fun j => value (children j))))
 (sub : ∀ j, Canonical (children j)) : Meaning m (.structural p (.record read) i) (fromRecord keys read children i) := by
 let xs := List.ofFn (fun j => value (children j))
 have count : xs.length = keys.length := List.length_ofFn ..
 unfold fromRecord
 split
 · rename_i missing
   exact no_structural_position m p (.record read) i (List.getElem?_eq_none_iff.mp missing)
 · rename_i key located
   split
   · rename_i fits
     split
     · exact shadow_many m p keys read xs count known fits i key located (by assumption)
     · rename_i unhidden
       split
       · rename_i j picked
         have pickedKey : keys[j.val]? = some key :=
           beq_iff_eq.mp (List.find?_some (p := fun k : Fin keys.length => keys[k.val]? == some key) picked)
         exact ⟨sub j,visible_at m p keys read xs count known fits i j.val key pickedKey located canon unhidden _
           (zip_child (fun k => value (children k)) j)⟩
       · trivial
   · rename_i different
     exact disjoint m p keys read xs count known different i

theorem total (keys read : List Nat) (children : Fin keys.length → Tree) (i : Nat) :
 fromRecord keys read children i ≠ .unknown := by
 unfold fromRecord
 split
 · intro impossible; cases impossible
 · rename_i key hit
   split
   · rename_i checked
     split
     · intro impossible; cases impossible
     · split
       · intro impossible; cases impossible
       · rename_i missing
         have isRead : key ∈ read := by
           obtain ⟨bound,here⟩ := List.getElem?_eq_some_iff.mp hit
           exact here ▸ List.getElem_mem bound
         have isKnown := ((visibleSet_exact _ _).mp checked key).mpr isRead
         obtain ⟨j,bound,found⟩ := List.mem_iff_getElem.mp isKnown
         let k : Fin keys.length := ⟨j,bound⟩
         have bit : (keys[k.val]? == some key) = true :=
           beq_iff_eq.mpr ((List.getElem?_eq_getElem bound).trans (congrArg some found))
         have no := List.find?_eq_none.mp missing k (List.mem_finRange _)
         rw [bit] at no
         contradiction
   · intro impossible; cases impossible

end Yulang.GeneralRebaseTreeRecord272
