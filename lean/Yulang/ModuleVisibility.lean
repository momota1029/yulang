import Yulang.ModuleRoles
import Yulang.RoleVisibility
import Yulang.QualifiedExamples

/-!
# File-local impl visibility at EOF

A declaration is eligible only when its owner file is the current file or has
been loaded, and the ordinary module-access check permits it. The latter is an
input from name resolution: this module does not reinterpret `my`/`our`/`pub`,
lexical module ancestry, aliases, or import syntax.

The selected declarations are the sole impl database supplied to the existing
`QualifiedInference.finishModule`. In particular, every nested `where` call
uses the root file's same selected list. Hidden declarations need not even be
well formed: only the selected database is checked. Membership-equivalent
visible declarations give the same EOF result, including order and duplicates.

This module connects visibility to the established EOF gate. That gate still
validates a supplied partial assignment; it does not infer missing type slots.
The separate ground-head inference layer addresses that additional operation.
-/

namespace Yulang.ModuleVisibility

open Inference RoleConstraints QualifiedInference

structure Declaration (File : Type) where
  owner : File
  implementation : Roles.Impl
  deriving DecidableEq

structure FileScope (File : Type) where
  current : File
  loaded : List File
  accessible : Declaration File → Bool

def FileScope.visible [DecidableEq File] (scope : FileScope File) (entry : Declaration File) : Bool :=
  decide (entry.owner = scope.current ∨ entry.owner ∈ scope.loaded) && scope.accessible entry

theorem FileScope.visible_exact [DecidableEq File] (scope : FileScope File)
    (entry : Declaration File) :
    scope.visible entry = true ↔
      (entry.owner = scope.current ∨ entry.owner ∈ scope.loaded) ∧ scope.accessible entry = true := by
  simp [FileScope.visible]

def FileScope.select [DecidableEq File] (scope : FileScope File)
    (catalog : List (Declaration File)) : List Roles.Impl :=
  (catalog.filter scope.visible).map Declaration.implementation

theorem FileScope.mem_select [DecidableEq File] (scope : FileScope File)
    (catalog : List (Declaration File)) (implementation : Roles.Impl) :
    implementation ∈ scope.select catalog ↔
      ∃ entry ∈ catalog, scope.visible entry = true ∧ entry.implementation = implementation := by
  simp only [FileScope.select, List.mem_map, List.mem_filter, and_assoc]

theorem FileScope.selected_origin [DecidableEq File] (scope : FileScope File)
    (catalog : List (Declaration File)) (implementation : Roles.Impl)
    (selected : implementation ∈ scope.select catalog) :
    ∃ entry ∈ catalog, entry.implementation = implementation ∧
      (entry.owner = scope.current ∨ entry.owner ∈ scope.loaded) ∧ scope.accessible entry = true := by
  obtain ⟨entry, member, visible, same⟩ := (scope.mem_select catalog implementation).mp selected
  exact ⟨entry, member, same, (scope.visible_exact entry).mp visible⟩

theorem FileScope.unloaded_hidden [DecidableEq File] (scope : FileScope File)
    (entry : Declaration File) (other : entry.owner ≠ scope.current)
    (unloaded : entry.owner ∉ scope.loaded) : scope.visible entry = false := by
  simp [FileScope.visible, other, unloaded]

theorem FileScope.own_accessible [DecidableEq File] (scope : FileScope File)
    (entry : Declaration File) (own : entry.owner = scope.current)
    (access : scope.accessible entry = true) : scope.visible entry = true :=
  (scope.visible_exact entry).mpr ⟨Or.inl own, access⟩

theorem FileScope.select_append_hidden [DecidableEq File] (scope : FileScope File)
    (catalog hidden : List (Declaration File))
    (invisible : ∀ entry ∈ hidden, scope.visible entry = false) :
    scope.select (catalog ++ hidden) = scope.select catalog := by
  have removed : hidden.filter scope.visible = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro entry member
    simp [invisible entry member]
  simp [FileScope.select, List.filter_append, removed]

/-- Only the visible membership of a catalog matters; hidden entries may
change freely, and visible entries may be reordered or repeated. -/
def SameVisible [DecidableEq File] (scope : FileScope File)
    (left right : List (Declaration File)) : Prop :=
  ∀ entry, scope.visible entry = true → (entry ∈ left ↔ entry ∈ right)

theorem selected_membership_congr [DecidableEq File] (scope : FileScope File)
    {left right : List (Declaration File)} (same : SameVisible scope left right)
    (implementation : Roles.Impl) :
    implementation ∈ scope.select left ↔ implementation ∈ scope.select right := by
  rw [scope.mem_select, scope.mem_select]
  constructor
  · rintro ⟨entry, member, visible, equal⟩
    exact ⟨entry, (same entry visible).mp member, visible, equal⟩
  · rintro ⟨entry, member, visible, equal⟩
    exact ⟨entry, (same entry visible).mpr member, visible, equal⟩

def resolveAt [DecidableEq File] (scope : FileScope File) (catalog : List (Declaration File))
    (wf : Roles.WellFormed (scope.select catalog)) (goal : Roles.Goal) : Roles.Result :=
  Roles.resolve (scope.select catalog) wf goal

theorem resolveAt_congr [DecidableEq File] (scope : FileScope File)
    {left right : List (Declaration File)} (same : SameVisible scope left right)
    (leftWF : Roles.WellFormed (scope.select left)) (rightWF : Roles.WellFormed (scope.select right))
    (goal : Roles.Goal) : resolveAt scope left leftWF goal = resolveAt scope right rightWF goal :=
  RoleVisibility.resolve_congr (selected_membership_congr scope same) leftWF rightWF goal

theorem pendingCheck_congr (m : Model) (decode : m.Ty → Roles.Term)
    {left right : List Roles.Impl} (same : ∀ implementation, implementation ∈ left ↔ implementation ∈ right)
    (leftWF : Roles.WellFormed left) (rightWF : Roles.WellFormed right)
    (assignment : α → Comp m) (interface : Interface α n) :
    pendingCheck m decode left leftWF assignment interface =
      pendingCheck m decode right rightWF assignment interface := by
  unfold pendingCheck
  congr 1
  funext goal
  rw [RoleVisibility.resolve_congr same leftWF rightWF]

def finish [DecidableEq File] (m : Model) (decode : m.Ty → Roles.Term)
    (scope : FileScope File) (catalog : List (Declaration File))
    (wf : Roles.WellFormed (scope.select catalog)) (assignment : α → Option (Comp m))
    (interface : Interface α n) : Option (ClosedInterface m n) :=
  finishModule m decode (scope.select catalog) wf assignment interface

theorem finish_exact [DecidableEq File] (m : Model) (decode : m.Ty → Roles.Term)
    (scope : FileScope File) (catalog : List (Declaration File))
    (wf : Roles.WellFormed (scope.select catalog)) (assignment : α → Option (Comp m))
    (interface : Interface α n) (closed : ClosedInterface m n) :
    finish m decode scope catalog wf assignment interface = some closed ↔
      interface.known assignment = true ∧
      Satisfies (resolvingTheory decode (scope.select catalog))
        ((pending interface.obligations).map (Goal.eval m (completeAssignment m assignment))) ∧
      interface.closeAt m (completeAssignment m assignment) = closed :=
  finishModule_exact m decode (scope.select catalog) wf assignment interface closed

theorem finish_congr [DecidableEq File] (m : Model) (decode : m.Ty → Roles.Term)
    (scope : FileScope File) {left right : List (Declaration File)} (same : SameVisible scope left right)
    (leftWF : Roles.WellFormed (scope.select left)) (rightWF : Roles.WellFormed (scope.select right))
    (assignment : α → Option (Comp m)) (interface : Interface α n) :
    finish m decode scope left leftWF assignment interface =
      finish m decode scope right rightWF assignment interface := by
  unfold finish finishModule
  rw [pendingCheck_congr m decode (selected_membership_congr scope same) leftWF rightWF]

theorem finish_permutation [DecidableEq File] (m : Model) (decode : m.Ty → Roles.Term)
    (scope : FileScope File) {left right : List (Declaration File)} (permutation : left.Perm right)
    (leftWF : Roles.WellFormed (scope.select left)) (rightWF : Roles.WellFormed (scope.select right))
    (assignment : α → Option (Comp m)) (interface : Interface α n) :
    finish m decode scope left leftWF assignment interface =
      finish m decode scope right rightWF assignment interface :=
  finish_congr m decode scope (fun _ _ => permutation.mem_iff) leftWF rightWF assignment interface

theorem finish_append_hidden [DecidableEq File] (m : Model) (decode : m.Ty → Roles.Term)
    (scope : FileScope File) (catalog hidden : List (Declaration File))
    (invisible : ∀ entry ∈ hidden, scope.visible entry = false)
    (wf : Roles.WellFormed (scope.select catalog))
    (extendedWF : Roles.WellFormed (scope.select (catalog ++ hidden)))
    (assignment : α → Option (Comp m)) (interface : Interface α n) :
    finish m decode scope (catalog ++ hidden) extendedWF assignment interface =
      finish m decode scope catalog wf assignment interface := by
  apply finish_congr
  intro entry visible
  simp only [List.mem_append]
  constructor
  · intro member
    rcases member with own | hiddenMember
    · exact own
    · have absent := invisible entry hiddenMember
      simp [visible] at absent
  · exact Or.inl

theorem finish_duplicate_catalog [DecidableEq File] (m : Model) (decode : m.Ty → Roles.Term)
    (scope : FileScope File) (catalog : List (Declaration File))
    (wf : Roles.WellFormed (scope.select catalog))
    (duplicateWF : Roles.WellFormed (scope.select (catalog ++ catalog)))
    (assignment : α → Option (Comp m)) (interface : Interface α n) :
    finish m decode scope (catalog ++ catalog) duplicateWF assignment interface =
      finish m decode scope catalog wf assignment interface :=
  finish_congr m decode scope (fun _ _ => by simp) duplicateWF wf assignment interface

theorem finish_preserves_scheme [DecidableEq File] (m : Model) (decode : m.Ty → Roles.Term)
    (scope : FileScope File) (catalog : List (Declaration File))
    (wf : Roles.WellFormed (scope.select catalog)) (assignment : α → Option (Comp m))
    (interface : Interface α n) (closed : ClosedInterface m n)
    (accepted : finish m decode scope catalog wf assignment interface = some closed)
    (theory : Theory m) (total : α → Comp m)
    (agrees : ∀ slot value, assignment slot = some value → total slot = value) (output : Comp m) :
    interface.scheme.Holds m theory (extend total output) ↔
      BindingTyping m theory (.qualified n closed.requirements (fun locals => Comp.pure m (closed.value locals))) output :=
  finalized_scheme_exact m decode (scope.select catalog) wf assignment interface closed accepted theory total agrees output

namespace Examples

open QualifiedExamples

def declaredHere : Declaration Nat := ⟨0, addIntImpl⟩
def scope (file : Nat) (loaded : List Nat) : FileScope Nat := ⟨file, loaded, fun _ => true⟩
def catalog : List (Declaration Nat) := [declaredHere]
def knownInt : Unit → Option (Comp model) := fun _ => some (Roles.Term.app 0 [], ())

theorem localWF : Roles.WellFormed ((scope 0 []).select catalog) := addInt_wf
theorem importedWF : Roles.WellFormed ((scope 1 [0]).select catalog) := addInt_wf
theorem hiddenWF : Roles.WellFormed ((scope 1 []).select catalog) := empty_impls_wellFormed

theorem current_file_uses_own_impl :
    finish model decode (scope 0 []) catalog localWF knownInt capturedInterface =
      some (capturedInterface.closeAt model (fun _ => (Roles.Term.app 0 [], ()))) :=
  eof_accepts_later_integer_solution

theorem imported_file_impl_is_used :
    finish model decode (scope 1 [0]) catalog importedWF knownInt capturedInterface =
      some (capturedInterface.closeAt model (fun _ => (Roles.Term.app 0 [], ()))) :=
  eof_accepts_later_integer_solution

theorem another_file_alone_has_no_impl :
    finish model decode (scope 1 []) catalog hiddenWF knownInt capturedInterface = none := by
  have missing : Roles.resolve ((scope 1 []).select catalog) hiddenWF
      ⟨0, [Roles.Term.app 0 []]⟩ = .noImpl := Roles.resolve_none _ _ _ rfl
  have rejected : pendingCheck model decode ((scope 1 []).select catalog) hiddenWF
      (completeAssignment model knownInt) capturedInterface = false := by
    unfold pendingCheck
    rw [captured_role_stays_pending]
    change (decide (Roles.resolve ((scope 1 []).select catalog) hiddenWF
      ⟨0, [Roles.Term.app 0 []]⟩ = .resolved) && true) = false
    rw [missing]
    rfl
  simp [finish, finishModule, rejected]

theorem imports_do_not_override_access :
    (FileScope.mk 1 [0] (fun _ => false) : FileScope Nat).select catalog = [] := rfl

def nestedCatalog : List (Declaration Nat) :=
  [⟨0, Roles.Examples.listImpl⟩, ⟨1, Roles.Examples.intImpl⟩]

theorem nestedMissingWF : Roles.WellFormed ((scope 2 [0]).select nestedCatalog) := by
  intro implementation member
  have equal : implementation = Roles.Examples.listImpl := by simpa [FileScope.select, FileScope.visible, scope, nestedCatalog] using member
  rw [equal]
  exact Roles.Examples.listImpl_wellFormed

theorem nestedLoadedWF : Roles.WellFormed ((scope 2 [0, 1]).select nestedCatalog) := Roles.Examples.goodImpls_wellFormed

theorem nested_where_cannot_see_unloaded_file :
    resolveAt (scope 2 [0]) nestedCatalog nestedMissingWF
      (Roles.Examples.display (Roles.Examples.list Roles.Examples.int)) = .noImpl := by
  rw [resolveAt, Roles.resolve_one _ _ _ Roles.Examples.listImpl (by decide)]
  simp only [Roles.Examples.listImpl, List.map_cons, List.map_nil]
  rw [Roles.resolve_none _ _ _ (by decide)]
  rfl

theorem nested_where_uses_root_loaded_files :
    resolveAt (scope 2 [0, 1]) nestedCatalog nestedLoadedWF
      (Roles.Examples.display (Roles.Examples.list (Roles.Examples.list Roles.Examples.int))) = .resolved :=
  Roles.Examples.nested_list_resolved

end Examples
end Yulang.ModuleVisibility
