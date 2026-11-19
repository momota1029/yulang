import Yulang.GeneralRebaseTreeReadbackState272

namespace Yulang.GeneralRebaseTreeNominal272
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRecursiveInspection (Origin Test Observes)
open GeneralNominalOriginTerms (arity)
open GeneralNominalFiniteMeaning (At build project_value)
open GeneralRebaseFiniteTree272 (Tree Canonical value)
open GeneralRebaseTreeReadbackState272 (Result Meaning any_nominal no_child_of_absent_nominal)
open GeneralRebaseTreeProjection272 (built_tag)
open GeneralNominalFiniteHeadInversion renaming head → tag
open GeneralDictionaryInspectionHeads215 (tag_subtype tagged_nominal)

def fromTree (name index : Nat) : Tree → Result
 | .node (.nominal actual count) children =>
   if name = actual then
     if inside : index < count then .found (children ⟨index,inside⟩) else .absent
   else .absent
 | _ => .absent

theorem required (m : Assignment) (p : Origin) (name idx : Nat) (test : Test)
 (values : Fin (arity test) → Ty) (known : At m .actual p (build test values))
 (seen : Observes m (.nominal p name idx) actual) :
 ∃ n, tag test = .nominal name n ∧ idx < n := by
 cases seen with
 | nominal parent rel found =>
   have meaning := known.2 _ parent
   exact ⟨_,tag_subtype (built_tag test values) (tagged_nominal name _) (subtype_trans meaning.2 rel.1),
     (List.getElem?_eq_some_iff.mp found).1⟩

theorem fromTree_sound (m : Assignment) (p : Origin) (name index : Nat)
 (tree : Tree) (cert : Meaning m p (.found tree)) :
 Meaning m (.nominal p name index) (fromTree name index tree) := by
 cases tree with
 | node test children =>
   have no (impossible : ¬∃ count, tag test = .nominal name count ∧ index < count) :
     Meaning m (.nominal p name index) .absent := by
     intro v event
     exact impossible (required m p name index test (fun i => value (children i)) cert.2 event)
   cases test with
   | scalar b =>
     apply no
     rintro ⟨_,clash,_⟩
     cases clash
   | structural shape =>
     apply no
     rintro ⟨_,clash,_⟩
     cases shape <;> cases clash
   | nominal got count =>
     change Meaning m (.nominal p name index)
       (if name = got then if ok : index < count then .found (children ⟨index,ok⟩) else .absent else .absent)
     split
     · rename_i align
       subst name
       split
       · rename_i valid
         exact ⟨cert.1.2 ⟨index,valid⟩,project_value (.nominal got count) (by trivial)
             (fun i => value (children i)) cert.2 ⟨index,valid⟩⟩
       · rename_i absent
         apply no
         rintro ⟨other,eq,lt⟩
         cases eq
         exact absent lt
     · rename_i different
       apply no
       rintro ⟨other,eq,lt⟩
       cases eq
       exact different rfl

def step (name i : Nat) : Result → Result
 | .unknown => .unknown
 | .absent => .absent
 | .many => .many
 | .found tree => fromTree name i tree

theorem sound (m : Assignment) (p : Origin) (name i : Nat) (r : Result)
 (cert : Meaning m p r) : Meaning m (.nominal p name i) (step name i r) := by
 cases r with
 | unknown => trivial
 | absent => exact no_child_of_absent_nominal m _ _ _ cert
 | many => exact any_nominal m _ _ _ cert
 | found t => exact fromTree_sound m _ _ _ t cert

end Yulang.GeneralRebaseTreeNominal272
