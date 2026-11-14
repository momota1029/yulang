import Yulang.GeneralNominalViewTransport196

set_option backward.isDefEq.respectTransparency false
/-! Variable-only source heads do not inspect descriptors. Their reinspection
certificate is proved for every replacement view, not assumed. -/
namespace Yulang.GeneralNominalVariableView196
open GeneralDeclarations GeneralNominalRecursiveInspection
open GeneralNominalInspection (Query Bounds)
open GeneralNominalViewTransport196

theorem inspect_variable (state : GeneralNominalState.State) (next : View state)
    (names : List Nat) (bounds : Bounds state) (origin : Option Origin) :
    inspect (replace state next) (.variables names) bounds origin =
      report next (inspect state (.variables names) bounds origin) := by
  simp only [inspect,report,List.map_map]
  rfl

theorem report_append (state : GeneralNominalState.State) (next : View state)
    (first last : Report state) :
    report next (first.append last) = (report next first).append (report next last) := by
  simp [report,Report.append,List.map_append]

theorem inspect_variables (state : GeneralNominalState.State) (next : View state)
    (names : List (List Nat)) (bounds : List (Bounds state)) (origins : Nat → Option Origin) (index : Nat) :
    inspectMany (replace state next) (names.map Query.variables) bounds origins index =
      report next (inspectMany state (names.map Query.variables) bounds origins index) := by
  induction names generalizing bounds index with
  | nil => cases bounds <;> simp [inspectMany,report]
  | cons names rest ih =>
    cases bounds with
    | nil => simp [inspectMany,report]
    | cons bound bounds =>
      simp only [List.map_cons,inspectMany]
      rw [inspect_variable,ih,report_append]

/-- Computed query shape, not semantic evidence, is the only restriction. -/
theorem rechecked_variables (old : GeneralNominalCandidates.Context) (next : View old.state)
    (declaration : Declaration) (names : List (List Nat))
    (shape : GeneralNominalInspection.queries old.state old.interpretation declaration = names.map Query.variables)
    (bounds : List (Bounds old.state)) : Rechecked old next declaration bounds := by
  unfold Rechecked GeneralNominalRecursiveCandidates.report
  have newShape : GeneralNominalInspection.queries (replace old.state next) old.interpretation declaration =
      names.map Query.variables := shape
  simp only [context,newShape,shape,inspect_variables,report]

/-- Uniform descriptor-change transport for registries of variable-only heads.
Constructors, normalized descriptors and models remain the actual existing ones. -/
theorem rechecks_variables (registry : Registry) (old : GeneralNominalCandidates.Context)
    (next : View old.state)
    (shape : ∀ declaration ∈ registry.declarations, ∃ names : List (List Nat),
      GeneralNominalInspection.queries old.state old.interpretation declaration = names.map Query.variables) :
    Rechecks registry old next := by
  intro declaration member bounds
  obtain ⟨names,same⟩ := shape declaration member
  exact rechecked_variables old next declaration names same bounds
end Yulang.GeneralNominalVariableView196
