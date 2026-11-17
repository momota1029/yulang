import Yulang.GeneralNominalFiniteEquationRealization236
set_option backward.isDefEq.respectTransparency false
/-! Finite coherent strictly descending equations have a simultaneous solution.
Only their equation subsystem is claimed, not unrelated journal constraints. -/
namespace Yulang.GeneralNominalAcyclicEquations237
open GeneralNominalFiniteEquationRealization236 (Entry)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
variable (entries : List Entry) (base : Assignment)
noncomputable def body (n : Nat) (recurse : (m : Nat) → m < n → Ty) : Ty :=
 match entries.find? (fun entry => entry.1 == n) with
 | none => (base n).1
 | some entry => entry.2.eval CommonNominalFullCarrier.model
     (fun m => (if h : m < n then recurse m h else (base m).1, (base m).2))
noncomputable def value (n : Nat) : Ty := Nat.lt_wfRel.wf.fix (body entries base) n
noncomputable def solution : Assignment := fun n => (value entries base n,(base n).2)

theorem unfold_value (n : Nat) : value entries base n =
 body entries base n (fun m _ => value entries base m) :=
 WellFounded.fix_eq _ _ _

def Coherent : Prop := ∀ first ∈ entries, ∀ last ∈ entries, first.1 = last.1 → first.2 = last.2
def Descending : Prop := ∀ entry ∈ entries, ∀ n ∈ GeneralNominalState.typeSources entry.2, n < entry.1

theorem outside (absent : ∀ entry ∈ entries, entry.1 ≠ n) : solution entries base n = base n := by
 have missing : entries.find? (fun entry => entry.1 == n) = none :=
   List.find?_eq_none.mpr (fun entry member => by simpa using absent entry member)
 unfold solution
 rw [unfold_value]
 simp only [body,missing]

theorem row (n : Nat) : (solution entries base n).2 = (base n).2 := rfl

theorem equation (coherent : Coherent entries) (descending : Descending entries)
 (entry : Entry) (member : entry ∈ entries) :
 (solution entries base entry.1).1 = entry.2.eval CommonNominalFullCarrier.model (solution entries base) := by
 have found : ∃ chosen, entries.find? (fun candidate => candidate.1 == entry.1) = some chosen := by
   cases recorded : entries.find? (fun candidate => candidate.1 == entry.1) with
   | none =>
     have absent := List.find?_eq_none.mp recorded entry member
     simp at absent
   | some chosen => exact ⟨chosen,rfl⟩
 obtain ⟨chosen,found⟩ := found
 have present := List.mem_of_find?_eq_some found
 have target : chosen.1 = entry.1 := by simpa using List.find?_some found
 have term := coherent chosen present entry member target
 change value entries base entry.1 = _
 rw [unfold_value]
 simp only [body,found,term]
 apply GeneralNominalCenteredModelExtension.type_eval_same
 intro n within
 have smaller := descending entry member n within
 simp only [smaller,dite_eq_left,solution]

theorem equations (coherent : Coherent entries) (descending : Descending entries) :
 ∀ entry ∈ entries, PresenceNormalForm.All CommonNominalFullCarrier.model (solution entries base)
   (GeneralNominalAllocation.equations entry.1 entry.2) := by
 intro entry member
 apply (GeneralNominalCaptureMerges.equations_exact ..).mpr
 rw [equation entries base coherent descending entry member]
 exact ⟨subtype_refl _,subtype_refl _⟩
end Yulang.GeneralNominalAcyclicEquations237
