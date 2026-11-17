import Std
/-! Executable finite writes with injective target names. Rows or other
coordinates can be preserved separately by applying this only to type values. -/
namespace Yulang.GeneralFiniteAssignment246
variable {Name Value : Type} [DecidableEq Name]

def write (entries : List (Name × Value)) (fallback : Name → Value) (name : Name) : Value :=
 match entries with
 | [] => fallback name
 | entry :: rest => if entry.1 = name then entry.2 else write rest fallback name

theorem write_outside (entries : List (Name × Value)) (fallback : Name → Value) (name : Name)
 (outside : ∀ entry ∈ entries, entry.1 ≠ name) : write entries fallback name = fallback name := by
 induction entries with
 | nil => rfl
 | cons entry rest ih =>
   rw [write,ite_eq_right (outside entry (by simp))]
   exact ih (fun other member => outside other (List.mem_cons_of_mem _ member))

theorem write_member (entries : List (Name × Value)) (fallback : Name → Value)
 (coherent : ∀ first ∈ entries, ∀ last ∈ entries, first.1 = last.1 → first.2 = last.2)
 (entry : Name × Value) (member : entry ∈ entries) : write entries fallback entry.1 = entry.2 := by
 induction entries with
 | nil => simp at member
 | cons first rest ih =>
   by_cases same : first.1 = entry.1
   · rw [write,ite_eq_left same]
     exact coherent first (by simp) entry member same
   · rw [write,ite_eq_right same]
     have tail : entry ∈ rest := by
       rcases List.mem_cons.mp member with equal | included
       · exact False.elim (same (congrArg Prod.fst equal.symm))
       · exact included
     exact ih (fun a am b bm eq => coherent a (List.mem_cons_of_mem _ am) b (List.mem_cons_of_mem _ bm) eq) tail

def finite (targets : Fin size → Name) (values : Fin size → Value) (fallback : Name → Value) : Name → Value :=
 write (List.ofFn (fun index => (targets index,values index))) fallback

theorem finite_at (targets : Fin size → Name) (injective : Function.Injective targets)
 (values : Fin size → Value) (fallback : Name → Value) (index : Fin size) :
 finite targets values fallback (targets index) = values index := by
 apply write_member _ fallback _ (targets index,values index) (List.mem_ofFn.mpr ⟨index,rfl⟩)
 intro first firstMem last lastMem equal
 obtain ⟨a,rfl⟩ := List.mem_ofFn.mp firstMem
 obtain ⟨b,rfl⟩ := List.mem_ofFn.mp lastMem
 have same := injective equal
 subst b
 rfl

theorem finite_outside (targets : Fin size → Name) (values : Fin size → Value)
 (fallback : Name → Value) (name : Name) (outside : ∀ index, targets index ≠ name) :
 finite targets values fallback name = fallback name := by
 apply write_outside
 intro entry member
 obtain ⟨index,rfl⟩ := List.mem_ofFn.mp member
 exact outside index
end Yulang.GeneralFiniteAssignment246
