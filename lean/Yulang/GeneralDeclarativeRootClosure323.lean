import Yulang.GeneralDeclarativeOutputExact323
import Yulang.GeneralDeclarativeCompileLists321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeRootClosure323
open GeneralDeclarations (Checked)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeOutputFacts320 (rootFact)
open GeneralDeclarativeOutputs320 (OutputMeaning)
open GeneralDeclarativeEntailment320 (Holds Entails appendFacts model_append literal)
open GeneralDeclarativeCompileLists321 (Result collect_result)
open GeneralDeclarativeOutputExact323 (root_exact all_models_exact)
open GeneralDeclarativeBatch320 (collect collect_sound)
open GeneralNominalCommonBridge (Assignment)

def DeclaredRows (r : GeneralDeclarations.Registry) (interp : GeneralNominalInspection.Interpretation)
    (decl : GeneralDeclarations.Declaration) (d : GeneralDeclarativeDemand320.Demand)
    (capture : Nat → GeneralDeclarativeWhere319.Capture) : Prop :=
  ∀ out ∈ d.outputs, ∃ row, rootFact r interp decl d capture out = some [row]

/-- Ordered root output emission selects only explicit/default shape and
the extant target from the source demand. No model closure premise is
part of this compiler totality property. -/
theorem collected (shape : DeclaredRows r interp decl d capture) :
    ∃ rows, collect (rootFact r interp decl d capture) d.outputs = some rows := by
  have recurse {xs : List GeneralSourceState.Output}
      (parts : ∀ out ∈ xs, ∃ row, rootFact r interp decl d capture out = some [row]) :
      ∃ rows, collect (rootFact r interp decl d capture) xs = some rows := by
    induction xs with
    | nil => exact ⟨[],rfl⟩
    | cons one rest ih =>
      obtain ⟨row,a⟩ := parts one List.mem_cons_self
      obtain ⟨rows,b⟩ := ih (fun out found => parts out (List.mem_cons_of_mem _ found))
      exact ⟨row :: rows,by simp [collect,a,b]⟩
  exact recurse shape

theorem exact_rows {xs : List GeneralSourceState.Output}
    (shape : ∀ out ∈ xs, ∃ row, rootFact r interp decl d capture out = some [row])
    (emitted : collect (rootFact r interp decl d capture) xs = some rows) :
    row ∈ rows ↔ ∃ out ∈ xs, rootFact r interp decl d capture out = some [row] := by
  induction xs generalizing rows with
  | nil => simp [collect] at emitted; subst rows; simp
  | cons one rest ih =>
    obtain ⟨head,a⟩ := shape one List.mem_cons_self
    refine ?_
    cases b : collect (rootFact r interp decl d capture) rest with
    | none => simp [collect,a,b] at emitted
    | some tail =>
      have all : head :: tail = rows := by simpa [collect,a,b] using emitted
      subst rows
      constructor
      · intro member
        rcases List.mem_cons.mp member with rfl|found
        · exact ⟨one,List.mem_cons_self,a⟩
        · obtain ⟨out,inRest,built⟩ := (ih (fun out h => shape out (List.mem_cons_of_mem _ h)) b).mp found
          exact ⟨out,List.mem_cons_of_mem _ inRest,built⟩
      · rintro ⟨out,listed,built⟩
        rcases List.mem_cons.mp listed with rfl|inRest
        · have same := List.cons.inj (Option.some.inj (built.symm.trans a))
          exact List.mem_cons.mpr (.inl same.1)
        · exact List.mem_cons_of_mem _ ((ih (fun out h => shape out (List.mem_cons_of_mem _ h)) b).mpr
            ⟨out,inRest,built⟩)

/-- Exact semantic form of the independent selected-output closure: no
other compiler rows, dictionary evidence, or operational state appear. -/
theorem closure_exact (checked : Checked r) (visible : decl ∈ r.declarations)
    (shape : DeclaredRows r interp decl d capture)
    (emitted : collect (rootFact r interp decl d capture) d.outputs = some rows)
    (m : Assignment) :
    (∀ row ∈ rows, Holds m row) ↔ ∀ out ∈ d.outputs,
      OutputMeaning r.roles r.constructors interp decl d capture m out := by
  constructor
  · intro holds out requested
    obtain ⟨row,built⟩ := shape out requested
    have here := (exact_rows shape emitted).mpr ⟨out,requested,built⟩
    exact (root_exact checked visible built m).mpr (holds row here)
  · intro semantic row found
    obtain ⟨out,requested,built⟩ := (exact_rows shape emitted).mp found
    exact (root_exact checked visible built m).mp (semantic out requested)

theorem models_close (checked : Checked r) (visible : decl ∈ r.declarations)
    (shape : DeclaredRows r interp decl d capture)
    (emitted : collect (rootFact r interp decl d capture) d.outputs = some rows)
    (m : Assignment) :
    Models (appendFacts s rows) m ↔ Models s m ∧
      ∀ out ∈ d.outputs, OutputMeaning r.roles r.constructors interp decl d capture m out := by
  rw [model_append,closure_exact checked visible shape emitted]

theorem ordinary_sufficient
    (emitted : collect (rootFact r interp decl d capture) d.outputs = some rows)
    (closed : ∀ row ∈ rows, Entails s row) :
    Result s (collect (rootFact r interp decl d capture) d.outputs) :=
  ⟨rows,emitted,closed⟩

end Yulang.GeneralDeclarativeRootClosure323
