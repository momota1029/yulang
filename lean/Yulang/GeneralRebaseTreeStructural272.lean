import Yulang.GeneralRebaseTreeRecord272

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseTreeStructural272
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRecursiveInspection (Origin Test Observes)
open GeneralNormalizedObservation (Shape)
open GeneralNominalOriginTerms (arity)
open GeneralNominalFiniteMeaning (At build project_value)
open GeneralRebaseFiniteTree272 (Tree Canonical value)
open GeneralRebaseTreeReadbackState272 (Result Meaning no_structural_position any_structural no_child_of_absent_structural)
open GeneralRebaseTreeProjection272 (built_tag)
open GeneralNominalFiniteHeadInversion renaming head → tag
open GeneralDictionaryInspectionHeads215 (tag_subtype tagged_shape)

def unequal (chosen : Shape) (children : Fin chosen.arity → Tree) (asked : Shape) (idx : Nat) : Result :=
 match chosen, children, asked with
 | .record keys,kids,.record read => GeneralRebaseTreeRecord272.fromRecord keys read kids idx
 | _,_,_ => .absent

def fromTree (asked : Shape) (idx : Nat) : Tree → Result
 | .node (.structural chosen) children =>
   if chosen = asked then
     if inside : idx < chosen.arity then .found (children ⟨idx,inside⟩) else .absent
   else unequal chosen children asked idx
 | _ => .absent

theorem needed_tag (m : Assignment) (p : Origin) (test : Test) (children : Fin (arity test) → Ty)
 (known : At m .actual p (build test children)) (asked : Shape) (idx : Nat)
 (seen : Observes m (.structural p asked idx) actual) :
 tag test = tag (.structural asked) := by
 cases seen with
 | structural parent len eq found =>
   have resolved := known.2 _ parent
   exact tag_subtype (built_tag test children) (tagged_shape asked _ len) (subtype_trans resolved.2 eq.1)

theorem width_wrong_for_exact (m : Assignment) (p : Origin) (asked : List Nat) (idx : Nat)
 (known : At m .actual p exactEmpty) : Meaning m (.structural p (.record asked) idx) .absent := by
 intro w seen
 cases seen with
 | structural parent len good found =>
   rename_i ty ys
   have earlier := known.2 _ parent
   have eq : Equivalent (GeneralNominalRecursiveInspection.shapeValue (.record asked) ys) exactEmpty :=
     ⟨subtype_trans good.2 earlier.1,subtype_trans earlier.2 good.1⟩
   rw [GeneralNominalRecordInversion.record_shape asked ys len] at eq
   exact GeneralNominalFiniteHeadInversion.record_not_exactEmpty _ eq

theorem unequal_sound (m : Assignment) (p : Origin) (chosen asked : Shape) (idx : Nat)
 (children : Fin chosen.arity → Tree)
 (cert : Meaning m p (.found (.node (.structural chosen) children))) (other : chosen ≠ asked) :
 Meaning m (.structural p asked idx) (unequal chosen children asked idx) := by
 have no (mismatch : tag (.structural chosen) ≠ tag (.structural asked)) :
   Meaning m (.structural p asked idx) .absent := by
   intro w seen
   exact mismatch (needed_tag m p (.structural chosen) (fun i => value (children i)) cert.2 _ _ seen)
 cases chosen <;> cases asked <;> try exact False.elim (other rfl)
 case record.record keys read =>
   exact GeneralRebaseTreeRecord272.sound m p keys read children idx (cert.1.1.imp Nat.ne_of_lt) cert.2 cert.1.2
 case variant.variant first last =>
   apply no
   intro eq
   cases eq
   exact other rfl
 case exactEmpty.record labels => exact width_wrong_for_exact m p labels idx cert.2
 case record.exactEmpty labels => exact no_structural_position m p .exactEmpty idx (Nat.zero_le _)
 all_goals apply no; intro eq; cases eq

theorem fromTree_sound (m : Assignment) (p : Origin) (asked : Shape) (idx : Nat)
 (tree : Tree) (cert : Meaning m p (.found tree)) :
 Meaning m (.structural p asked idx) (fromTree asked idx tree) := by
 cases tree with
 | node test children =>
   have no (clash : tag test ≠ tag (.structural asked)) :
       Meaning m (.structural p asked idx) .absent := by
     intro w seen
     exact clash (needed_tag m p test (fun i => value (children i)) cert.2 _ _ seen)
   cases test with
   | scalar _ | nominal _ _ => apply no; cases asked <;> intro eq <;> cases eq
   | structural chosen =>
     change Meaning m (.structural p asked idx)
       (if chosen = asked then
         if inside : idx < chosen.arity then .found (children ⟨idx,inside⟩) else .absent
        else unequal chosen children asked idx)
     split
     · rename_i same
       subst asked
       split
       · rename_i yes
         exact ⟨cert.1.2 ⟨idx,yes⟩,
           project_value (.structural chosen) cert.1.1 (fun i => value (children i)) cert.2 ⟨idx,yes⟩⟩
       · exact no_structural_position m p chosen idx (Nat.le_of_not_gt (by assumption))
     · exact unequal_sound m p chosen asked idx children cert (by assumption)

def step (asked : Shape) (i : Nat) : Result → Result
 | .unknown => .unknown
 | .absent => .absent
 | .many => if i < asked.arity then .many else .absent
 | .found t => fromTree asked i t

theorem sound (m : Assignment) (p : Origin) (asked : Shape) (i : Nat) (r : Result)
 (cert : Meaning m p r) : Meaning m (.structural p asked i) (step asked i r) := by
 cases r with
 | unknown => trivial
 | absent => exact no_child_of_absent_structural m _ _ _ cert
 | many =>
   by_cases h : i < asked.arity
   · simpa only [step,h,ite_true] using any_structural m p asked i cert h
   · simpa only [step,h,ite_false] using no_structural_position m p asked i (Nat.le_of_not_gt h)
 | found t => exact fromTree_sound m _ _ _ t cert

end Yulang.GeneralRebaseTreeStructural272
