import Yulang.GeneralRebaseHeadProbe267

namespace Yulang.GeneralRebasePartialClassification267

inductive Verdict (Element : Type) where
 | none
 | unique (entry : Element)
 | ambiguous (first last : Element)
 | deferred
 deriving DecidableEq

def apart [DecidableEq Element] (first last : Element) : Bool := decide (first ≠ last)

theorem apart_iff [DecidableEq Element] (first last : Element) :
 apart first last = true ↔ first ≠ last := by simp [apart]

def classify [DecidableEq Element] (known unknown : List Element) : Verdict Element :=
 match known with
 | [] => if unknown.isEmpty then .none else .deferred
 | first :: rest =>
   match rest.find? (apart first) with
   | some other => .ambiguous first other
   | none => if unknown.any (apart first) then .deferred else .unique first

/-- Three decided results have independent certificates. In particular an
unknown entry cannot manufacture a second definitely viable candidate. -/
def Valid (known unknown : List Element) : Verdict Element → Prop
 | .none => known = [] ∧ unknown = []
 | .unique entry => entry ∈ known ∧ (∀ x ∈ known, x = entry) ∧ ∀ x ∈ unknown, x = entry
 | .ambiguous first last => first ∈ known ∧ last ∈ known ∧ first ≠ last
 | .deferred => True

theorem classify_valid [DecidableEq Element] (known unknown : List Element) :
 Valid known unknown (classify known unknown) := by
 cases known with
 | nil =>
   by_cases empty : unknown.isEmpty = true
   · simpa only [classify,empty,↓reduceIte,Valid,true_and] using List.isEmpty_iff.mp empty
   · simp only [classify,ite_eq_right empty,Valid]
 | cons first rest =>
   cases found : rest.find? (apart first) with
   | some other =>
     simp only [classify,found,Valid]
     exact ⟨List.mem_cons_self,List.mem_cons_of_mem _ (List.mem_of_find?_eq_some found),
       (apart_iff ..).mp (List.find?_some found)⟩
   | none =>
     by_cases seen : unknown.any (apart first) = true
     · simp only [classify,found,ite_eq_left seen,Valid]
     · simp only [classify,found,ite_eq_right seen,Valid]
       refine ⟨List.mem_cons_self,?_,?_⟩
       · intro x member
         rcases List.mem_cons.mp member with same | inside
         · exact same
         · exact Classical.byContradiction (fun different => (List.find?_eq_none.mp found x inside)
               ((apart_iff ..).mpr (fun eq => different eq.symm)))
       · intro x member
         exact Classical.byContradiction (fun different => seen (List.any_eq_true.mpr
           ⟨x,member,(apart_iff ..).mpr (fun eq => different eq.symm)⟩))

theorem unique_despite_duplicate_unknown [DecidableEq Element] (entry : Element)
 (known unknown : List Element) (sameKnown : ∀ x ∈ known, x = entry)
 (sameUnknown : ∀ x ∈ unknown, x = entry) :
 classify (entry :: known) unknown = .unique entry := by
 have noSecond : known.find? (apart entry) = none := by
   apply List.find?_eq_none.mpr
   intro x seen different
   exact ((apart_iff ..).mp different) (sameKnown x seen).symm
 have unknownSame : ¬ unknown.any (apart entry) = true := by
   intro result
   obtain ⟨x,seen,apart⟩ := List.any_eq_true.mp result
   exact ((apart_iff ..).mp apart) (sameUnknown x seen).symm
 simp [classify,noSecond,unknownSame]

end Yulang.GeneralRebasePartialClassification267
