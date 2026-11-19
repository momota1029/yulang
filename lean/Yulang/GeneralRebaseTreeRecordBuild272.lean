import Yulang.GeneralRebaseTreeConstructors272

namespace Yulang.GeneralRebaseTreeRecordBuild272
open CommonNominalFullCarrier
open GeneralRebaseFiniteTree272 (Tree value Canonical)
open GeneralRebaseTreeConstructors272 (recordTree record_value record_canonical)

def appendField (label : Nat) (child tail : Tree) : Option Tree :=
 match tail with
 | .node (.structural (.record keys)) rest =>
   if keys.all (fun other => label < other) then
      some (recordTree (label::keys) (Fin.cases child rest))
   else none
 | _ => none

theorem prepend_meaning (label : Nat) (child : Tree) (keys : List Nat) (rest : Fin keys.length → Tree) :
 value (recordTree (label::keys) (Fin.cases child rest)) =
 record label (value child) (value (recordTree keys rest)) := by
 rw [record_value (label::keys),record_value keys]
 simp only [List.ofFn_succ,Fin.cases_zero,Fin.cases_succ,List.zip_cons_cons,
    GeneralNominalStructuralReadback.recordValues,List.foldr_cons]

theorem appendField_exact (label : Nat) (child tail out : Tree)
 (c : Canonical child) (d : Canonical tail) (result : appendField label child tail = some out) :
 Canonical out ∧ value out = record label (value child) (value tail) := by
 unfold appendField at result
 split at result
 · rename_i keys rest
   split at result
   · rename_i monotone
     cases Option.some.inj result
     constructor
     · apply record_canonical
       · apply List.pairwise_cons.mpr
         exact ⟨fun k member => of_decide_eq_true (List.all_eq_true.mp monotone k member),d.1⟩
       · intro index
         refine Fin.cases ?_ ?_ index
         · exact c
         · intro i
           exact d.2 i
     · exact prepend_meaning label child keys rest
   · contradiction
 · contradiction

end Yulang.GeneralRebaseTreeRecordBuild272
