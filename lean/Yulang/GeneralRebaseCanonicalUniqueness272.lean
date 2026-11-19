import Yulang.GeneralRebaseTreeSchemaClosure272

namespace Yulang.GeneralRebaseCanonicalUniqueness272
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalOriginTerms (arity)
open GeneralRebaseFiniteTree272 (Tree Canonical value children_agree)
open GeneralRebaseTreeInterpreter272 (Source Certified)

/-- Canonical finite tree witnesses are unique in the full carrier.
Two stored equations cannot force different accepted tree witnesses
for a fixed source in the same model. -/
theorem exact (a b : Tree) (first : Canonical a) (last : Canonical b)
 (meaning : Equivalent (value a) (value b)) : a = b := by
 induction a generalizing b with
 | node t children ih =>
   cases b with
   | node u kids =>
     have shape := GeneralNominalFiniteHeadInversion.test_equal t u (fun i => value (children i))
       (fun j => value (kids j)) first.1 last.1 meaning
     subst u
     have every (i : Fin (arity t)) : children i = kids i :=
       ih i _ (first.2 i) (last.2 i) (children_agree t first.1 _ _ meaning i)
     exact congrArg (Tree.node t) (funext every)

theorem source_agree (m : Assignment) (left right : Source) (one : Certified m left) (two : Certified m right)
 (id : Nat) (a b : Tree) (x : left id = some a) (y : right id = some b) : a = b := by
 have h := one id a x
 have k := two id b y
 exact exact a b h.1 k.1 ⟨subtype_trans h.2.2 k.2.1,subtype_trans k.2.2 h.2.1⟩

end Yulang.GeneralRebaseCanonicalUniqueness272
