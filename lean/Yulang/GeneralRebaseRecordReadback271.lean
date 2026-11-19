import Yulang.GeneralRebaseRecordIndices271
import Yulang.GeneralRebaseRecordTagBoundary270

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseRecordReadback271
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRecursiveInspection (Origin Observes shapeValue)
open GeneralNominalRecordInversion (record_shape record_membership)
open GeneralNormalizedObservation (Shape)
open GeneralNominalOriginTerms (Same)
open GeneralRebaseRecordIndices271 (Shadowed first_at set_hidden index_visible)
open GeneralRebaseRecordLookup271 (payload)

theorem same_fields (keys read : List Nat) (xs ys : List Ty)
 (xlen : xs.length = keys.length) (ylen : ys.length = read.length)
 (same : Equivalent (shapeValue (.record keys) xs) (shapeValue (.record read) ys)) (label : Nat) :
 label ∈ keys ↔ label ∈ read := by
 rw [record_shape keys xs xlen,record_shape read ys ylen] at same
 simpa only [List.map_fst_zip (Nat.le_of_eq xlen.symm),List.map_fst_zip (Nat.le_of_eq ylen.symm)] using
   record_membership (keys.zip xs) (read.zip ys) same label

theorem visible_payload (keys read : List Nat) (xs ys : List Ty)
 (xlen : xs.length = keys.length) (ylen : ys.length = read.length)
 (same : Equivalent (shapeValue (.record keys) xs) (shapeValue (.record read) ys))
 (i j key : Nat) (left : keys[i]? = some key) (right : read[j]? = some key)
 (seenA : xs[i]? = some a) (seenB : ys[j]? = some b)
 (one : ¬ Shadowed keys i key) (two : ¬ Shadowed read j key) : Equivalent a b := by
 rw [record_shape keys xs xlen,record_shape read ys ylen] at same
 exact payload _ _ key _ _ (first_at keys xs i key a left seenA one)
  (first_at read ys j key b right seenB two) same

theorem overwrite_value (labels : List Nat) (xs : List Ty) (xslen : xs.length = labels.length)
 (i key : Nat) (loc : labels[i]? = some key) (shadow : Shadowed labels i key) (new : Ty) :
 Equivalent (shapeValue (.record labels) (xs.set i new)) (shapeValue (.record labels) xs) := by
 rw [record_shape labels _ (List.length_set.trans xslen),record_shape labels xs xslen]
 exact GeneralRebaseRecordOverwrite271.checked _ _ (set_hidden labels xs i key new loc shadow)

theorem hidden_observes (m : Assignment) (parent : Origin) (labels : List Nat) (i key : Nat)
 (loc : labels[i]? = some key) (shadow : Shadowed labels i key)
 (seen : ∃ x, Observes m (.structural parent (.record labels) i) x) (new : Ty) :
 Observes m (.structural parent (.record labels) i) new := by
 obtain ⟨_,proof⟩ := seen
 cases proof with
 | structural initial length same found =>
   rename_i actual values
   have old := overwrite_value labels values length i key loc shadow new
   have bound := (List.getElem?_eq_some_iff.mp found).1
   exact .structural initial (List.length_set.trans length)
     ⟨subtype_trans same.1 old.2,subtype_trans old.1 same.2⟩
     (by rw [List.getElem?_set]; simp [bound])

theorem hidden_not_same (m : Assignment) (parent target : Origin) (labels : List Nat) (i key : Nat)
 (loc : labels[i]? = some key) (shadow : Shadowed labels i key) :
 ¬ Same m (.structural parent (.record labels) i) target := by
 intro equal
 obtain ⟨y,seen⟩ := equal.2.1
 have first := equal.2.2 _ y (hidden_observes m parent labels i key loc shadow equal.1 (.base .int)) seen
 have last := equal.2.2 _ y (hidden_observes m parent labels i key loc shadow equal.1 (.base .str)) seen
 have impossible := GeneralDictionaryInspectionHeads215.tag_subtype
   (GeneralDictionaryInspectionHeads215.tagged_scalar .int) (GeneralDictionaryInspectionHeads215.tagged_scalar .str)
   (subtype_trans first.1 last.2)
 cases impossible

theorem visible_matches_canonical (m : Assignment) (source : Nat)
 (keys read : List Nat) (known : List Ty) (knownLen : known.length = keys.length)
 (eq : Equivalent (m source).1 (shapeValue (.record keys) known))
 (i j key : Nat) (measured : keys[i]? = some key) (located : read[j]? = some key)
 (canonical : keys.Nodup) (visible : ¬ Shadowed read j key)
 (child : known[i]? = some a)
 (saw : Observes m (.structural (.source source) (.record read) j) b) :
 Equivalent a b := by
 cases saw with
 | structural root readLen good atValue =>
   cases root
   exact visible_payload keys read known _ knownLen readLen
     ⟨subtype_trans eq.2 good.1,subtype_trans good.2 eq.1⟩
     i j key measured located child atValue (index_visible keys i key measured canonical) visible

end Yulang.GeneralRebaseRecordReadback271
