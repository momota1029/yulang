import Yulang.GeneralDeclarativeI65I74OpaqueEntry448
import Yulang.ModuleVisibility

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.Opaque448.VisibleInput
open Yulang.GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open RetainedFull445 (FullProblem)
open GeneralSourceMetadataBareBundle291 (InputBundle)

structure LocatedDeclaration where
  owner : Nat
  declaration : Declaration

/-- An independently resolved caller view, not a witness to a report.
The access IDs must come from ordinary name resolution. This function
does not infer imports/access from IDs, nor parse `my/our/pub`. -/
structure CallerScope where
  occurrence : List Nat
  currentFile : Nat
  loadedFiles : List Nat
  accessibleIds : List Nat

def branchVisible (scope : CallerScope) (row : LocatedDeclaration) : Bool :=
  decide (row.owner = scope.currentFile ∨ row.owner ∈ scope.loadedFiles) &&
    decide (row.declaration.id ∈ scope.accessibleIds)

theorem scoped_visibility_exact448 (scope : CallerScope) (row : LocatedDeclaration) :
    branchVisible scope row = true ↔
      (row.owner = scope.currentFile ∨ row.owner ∈ scope.loadedFiles) ∧
      row.declaration.id ∈ scope.accessibleIds := by simp [branchVisible]

def existingFileScope (s : CallerScope) : ModuleVisibility.FileScope Nat :=
  ⟨s.currentFile,s.loadedFiles,fun row => decide (row.implementation.key ∈ s.accessibleIds)⟩

theorem same_owner_and_identity_use_existing_file_gate448
    (scope : CallerScope) (row : LocatedDeclaration) (old : ModuleVisibility.Declaration Nat)
    (owner : row.owner = old.owner) (id : row.declaration.id = old.implementation.key) :
    branchVisible scope row = (existingFileScope scope).visible old := by
  simp only [branchVisible,ModuleVisibility.FileScope.visible,existingFileScope,owner,id]

def projectDeclarations (scope : CallerScope) (rows : List LocatedDeclaration) : List Declaration :=
  (rows.filter (branchVisible scope)).map LocatedDeclaration.declaration

def projectInput (src : InputBundle) (scope : CallerScope) (rows : List LocatedDeclaration) :
    InputBundle := {src with declarations := projectDeclarations scope rows}

theorem project_exact_order448 (scope : CallerScope) (rows : List LocatedDeclaration) :
    projectDeclarations scope rows =
      (rows.filter fun row => (row.owner = scope.currentFile ∨ row.owner ∈ scope.loadedFiles) &&
        row.declaration.id ∈ scope.accessibleIds).map LocatedDeclaration.declaration := by
  rfl

theorem hidden_append_keeps_actual_source448 (scope : CallerScope) (src : InputBundle)
    (rows hidden : List LocatedDeclaration)
    (hiddenAtSite : ∀ row ∈ hidden, branchVisible scope row = false) :
    projectInput src scope (rows ++ hidden) = projectInput src scope rows := by
  have none : hidden.filter (branchVisible scope) = [] := List.filter_eq_nil_iff.mpr (fun row atRow => by simp [hiddenAtSite row atRow])
  simp [projectInput,projectDeclarations,List.filter_append,none]

/-- Equality with the source actually embedded in the immutable old
input, not permission for a submitted solver witness to choose a subset. -/
structure SameResolvedInput (p : FullProblem) (src : InputBundle)
    (scope : CallerScope) (rows : List LocatedDeclaration) : Prop where
  site : p.root.occurrence = scope.occurrence
  compiled : GeneralSourceMetadataBareBundle291.compile (projectInput src scope rows) =
    some p.state.base.core.current.environment.source

theorem source_projection_reads_entire_original_role_list448 {p : FullProblem} {src scope rows}
    (same : SameResolvedInput p src scope rows) :
    visible p.state.base.core p.root =
      (projectDeclarations scope rows).filter (fun d => d.role == p.root.demand.role) := by
  have exact := congrArg InputBundle.declarations
    (GeneralSourceMetadataBareBundle291.preserves_input _ _ same.compiled).1
  change p.state.base.core.current.environment.source.declarations =
    projectDeclarations scope rows at exact
  change p.state.base.core.current.environment.source.declarations.filter
     (fun d => d.role == p.root.demand.role) = _
  rw [exact]

theorem hidden_source_addition_keeps_same_full_problem448 {p : FullProblem} {src scope rows hidden}
    (same : SameResolvedInput p src scope rows)
    (hiddenAtSite : ∀ row ∈ hidden, branchVisible scope row = false) :
    SameResolvedInput p src scope (rows ++ hidden) :=
  ⟨same.site,hidden_append_keeps_actual_source448 scope src rows hidden hiddenAtSite ▸ same.compiled⟩

/-- The same catalogue/occurrence with a different loaded-file set has
a different genuine scoped list. Module visibility cannot factor through
erased catalogue identities + call occurrence alone. -/
theorem scope_not_recoverable_from_erased_call448 (a b : Declaration)
    (role : a.role = b.role) (caller : List Nat) :
    ¬ ∃ f : List Declaration → List Nat → List Declaration,
      ∀ (scope : CallerScope) (rows : List LocatedDeclaration),
        f (rows.map LocatedDeclaration.declaration) scope.occurrence =
        (projectDeclarations scope rows).filter (fun d => d.role == a.role) := by
  rintro ⟨f,h⟩
  let all : List LocatedDeclaration := [⟨1,a⟩,⟨2,b⟩]
  let hidden : CallerScope := ⟨caller,1,[],[a.id,b.id]⟩
  let seen : CallerScope := ⟨caller,1,[2],[a.id,b.id]⟩
  have short : f [a,b] caller = [a] := by
    simpa [all,hidden,projectDeclarations,branchVisible] using h hidden all
  have both : f [a,b] caller = [a,b] := by
    simpa [all,seen,projectDeclarations,branchVisible,role] using h seen all
  have lengths := congrArg List.length (short.symm.trans both)
  cases lengths

end Yulang.GeneralDeclarativeI65.I72.Opaque448.VisibleInput
