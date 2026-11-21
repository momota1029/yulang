import Yulang.GeneralDeclarativeStableReplay329
import Yulang.GeneralDeclarativeStableCanonical329

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeStableScope329
open GeneralDeclarations (Registry Declaration Checked)
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeStableReads329 (Heads names_all)
open GeneralDeclarativeStableCanonical329 (Representative found)
open GeneralDeclarativeStableTies329 (rows row pairOf)
open GeneralDeclarativeStableAssemble329 (firsts)
open GeneralDeclarativeOpaqueCapture328 (choose choice_exact)
open GeneralDeclarativeDemand320 (Demand)

/-- Exact footprint of a selected tie: two different real center
names occurring under one source binder, the other end being the
representative used by this actual frame. This says nothing about
alias classes which may already connect those names elsewhere. -/
theorem accounts (representative : Representative selected spans)
    (present : e ∈ rows selected (spans.map pairOf)) :
    ∃ key first last, (key,first) ∈ spans ∧ (key,last) ∈ spans ∧
      first.center = (selected key).center ∧ last.center ≠ first.center ∧
      e = ⟨first.center,.variable last.center⟩ := by
  obtain ⟨u,inMap,rfl⟩ := List.mem_map.mp present
  obtain ⟨repeated,unequal⟩ := List.mem_filter.mp inMap
  obtain ⟨⟨key,last⟩,inSpans,rfl⟩ := List.mem_map.mp repeated
  have candidate : key ∈ spans.map Prod.fst := List.mem_map.mpr ⟨_,inSpans,rfl⟩
  obtain ⟨first,firstIn,center⟩ := representative key candidate
  refine ⟨key,first,last,firstIn,inSpans,center,?_,?_⟩
  · simpa [pairOf,center] using unequal
  · simp [row,pairOf,center]

theorem no_rows_if_linear {spans : List (Nat × Capture)}
    (linear : (spans.map Prod.fst).Nodup) (fallback : Nat → Capture) :
    rows (firsts spans fallback) (spans.map pairOf) = [] := by
  have notUsed (e : Equation) : e ∉ rows (firsts spans fallback) (spans.map pairOf) := by
    intro p
    obtain ⟨n,first,last,f,l,_,diff,_⟩ := accounts (GeneralDeclarativeStableCanonical329.uses_existing spans fallback) p
    have same : first = last :=
      ((choice_exact (fallback := fallback) linear f).symm.trans (choice_exact (fallback := fallback) linear l))
    exact diff (congrArg Capture.center same.symm)
  cases h : rows (firsts spans fallback) (spans.map pairOf) with
  | nil => rfl
  | cons first rest => exact False.elim (notUsed first (h ▸ List.mem_cons_self))

/-- The actual source table keeps the selected input binders separate
from declared output-only binders. This does not prohibit an ordinary
logical target from independently referring to the same value. -/
theorem source_scope {s : State} {d : Demand} (checked : Checked r) (visible : impl ∈ r.declarations)
    (read : Heads s r.constructors i d.arguments impl.head spans)
    (representative : Representative selected spans)
    (found : e ∈ rows selected (spans.map pairOf)) :
    ∃ key first last, key ∈ impl.inputNames ∧ key ∉ impl.outputNames ∧
      (key,first) ∈ spans ∧ (key,last) ∈ spans ∧ e = ⟨first.center,.variable last.center⟩ := by
  obtain ⟨key,a,b,first,last,_,_,row⟩ := accounts representative found
  have known : key ∈ impl.inputNames := by
    rw [GeneralDeclarations.Declaration.inputNames,← names_all read]
    exact List.mem_map.mpr ⟨_,first,rfl⟩
  refine ⟨key,a,b,known,?_,first,last,row⟩
  intro output
  exact (checked.2 impl visible).outputOnly.1 key output
    (GeneralPatternVariableProvenance.normalize_args_variables impl.head known)

end Yulang.GeneralDeclarativeStableScope329
