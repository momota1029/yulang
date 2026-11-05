import Yulang.ModuleVisibility

/-!
# EOF validation without impl-directed type completion

Spec §6.3, decision 33 (2026-11-05): an ambient weak slot that remains
undetermined at EOF is an error even if exactly one visible impl could supply
a type for it. Ordinary inference or an annotation must determine the slot
before role resolution. Generalized slots remain parameters of the export.

The entry below first scans the existing interface support. Only when every
ambient slot is present does it evaluate residual predicates and run the
existing terminating resolver. It returns a missing-slot witness or a concrete
failed role query, and is proved equivalent to `ModuleRoles.finishModule` and
the file-visible `ModuleVisibility.finish`. It never extends its assignment.

Theorems cover arbitrary models, finite interfaces, and well-formed visible
impl databases. Source collection of all residual obligations, classification
of ambient versus generalized slots, and ordinary type inference remain
upstream inputs. Diagnostics are semantic witnesses, not source error text.
-/

namespace Yulang.EOFNoDefaulting

open Inference RoleConstraints QualifiedInference

def firstMissing (interface : Interface α n) (assignment : α → Option (Comp m)) : Option α :=
  interface.support.find? fun slot => (assignment slot).isNone

theorem firstMissing_none_iff (interface : Interface α n)
    (assignment : α → Option (Comp m)) :
    firstMissing interface assignment = none ↔ interface.known assignment = true := by
  simp [firstMissing, Interface.known, List.find?_eq_none, List.all_eq_true,
    Option.isSome_iff_ne_none]

theorem firstMissing_sound (interface : Interface α n)
    (assignment : α → Option (Comp m)) (slot : α)
    (missing : firstMissing interface assignment = some slot) :
    slot ∈ interface.support ∧ assignment slot = none := by
  have absent : (assignment slot).isNone = true :=
    List.find?_some (p := fun slot => (assignment slot).isNone) missing
  exact ⟨List.mem_of_find?_eq_some missing, Option.isNone_iff_eq_none.mp absent⟩

/-- The query is evaluated once; no candidate types are enumerated. -/
def roleFailure (impls : List Roles.Impl) (wf : Roles.WellFormed impls) :
    List Roles.Goal → Option (Roles.Goal × Roles.Result)
  | [] => none
  | goal :: rest =>
      let answer := Roles.resolve impls wf goal
      if answer = .resolved then roleFailure impls wf rest else some (goal, answer)

theorem roleFailure_none_iff (impls : List Roles.Impl) (wf : Roles.WellFormed impls)
    (goals : List Roles.Goal) :
    roleFailure impls wf goals = none ↔
      ∀ goal ∈ goals, Roles.resolve impls wf goal = .resolved := by
  induction goals with
  | nil => simp [roleFailure]
  | cons goal rest ih =>
      simp only [roleFailure]
      split <;> simp_all

theorem roleFailure_sound (impls : List Roles.Impl) (wf : Roles.WellFormed impls)
    (goals : List Roles.Goal) (goal : Roles.Goal) (answer : Roles.Result)
    (failed : roleFailure impls wf goals = some (goal, answer)) :
    goal ∈ goals ∧ Roles.resolve impls wf goal = answer ∧ answer ≠ .resolved := by
  induction goals with
  | nil => simp [roleFailure] at failed
  | cons head rest ih =>
      simp only [roleFailure] at failed
      split at failed
      · obtain ⟨member, result, rejected⟩ := ih failed
        exact ⟨List.mem_cons_of_mem _ member, result, rejected⟩
      · simp only [Option.some.injEq, Prod.mk.injEq] at failed
        obtain ⟨rfl, rfl⟩ := failed
        exact ⟨by simp, rfl, by assumption⟩

def concreteGoals (m : Model) (decode : m.Ty → Roles.Term)
    (assignment : α → Option (Comp m)) (interface : Interface α n) : List Roles.Goal :=
  (pending interface.obligations).map fun goal =>
    ((goal.eval m (completeAssignment m assignment)).map decode).toGoal

theorem concreteGoals_resolve_iff (m : Model) (decode : m.Ty → Roles.Term)
    (impls : List Roles.Impl) (wf : Roles.WellFormed impls)
    (assignment : α → Option (Comp m)) (interface : Interface α n) :
    (∀ goal ∈ concreteGoals m decode assignment interface,
      Roles.resolve impls wf goal = .resolved) ↔
        pendingCheck m decode impls wf (completeAssignment m assignment) interface = true := by
  simp [concreteGoals, pendingCheck, List.all_eq_true]

inductive Failure (α : Type) where
  | undetermined : α → Failure α
  | role : Roles.Goal → Roles.Result → Failure α
  deriving Repr

/-- No role query is constructed until every ambient slot in the interface
has an assignment. The returned interface uses that exact assignment. -/
def finish (m : Model) (decode : m.Ty → Roles.Term)
    (impls : List Roles.Impl) (wf : Roles.WellFormed impls)
    (assignment : α → Option (Comp m)) (interface : Interface α n) :
    Except (Failure α) (ClosedInterface m n) :=
  match firstMissing interface assignment with
  | some slot => .error (.undetermined slot)
  | none =>
      match roleFailure impls wf (concreteGoals m decode assignment interface) with
      | some (goal, answer) => .error (.role goal answer)
      | none => .ok (interface.closeAt m (completeAssignment m assignment))

/-- The richer diagnostic entrance has exactly the established EOF gate's
successes, including the same closed interface. -/
theorem finish_success_iff (m : Model) (decode : m.Ty → Roles.Term)
    (impls : List Roles.Impl) (wf : Roles.WellFormed impls)
    (assignment : α → Option (Comp m)) (interface : Interface α n)
    (closed : ClosedInterface m n) :
    finish m decode impls wf assignment interface = .ok closed ↔
      finishModule m decode impls wf assignment interface = some closed := by
  rw [finishModule_exact]
  rw [← pendingCheck_exact m decode impls wf]
  cases missing : firstMissing interface assignment with
  | some slot =>
      have notKnown : interface.known assignment ≠ true := by
        intro known
        have absent := (firstMissing_none_iff interface assignment).mpr known
        rw [missing] at absent
        cases absent
      simp [finish, missing, notKnown]
  | none =>
      have known := (firstMissing_none_iff interface assignment).mp missing
      cases failed : roleFailure impls wf (concreteGoals m decode assignment interface) with
      | none =>
          have checked := (concreteGoals_resolve_iff m decode impls wf assignment interface).mp
            ((roleFailure_none_iff impls wf _).mp failed)
          simp [finish, missing, failed, known, checked]
      | some failure =>
          have notChecked : pendingCheck m decode impls wf
              (completeAssignment m assignment) interface ≠ true := by
            intro checked
            have absent := (roleFailure_none_iff impls wf _).mpr
              ((concreteGoals_resolve_iff m decode impls wf assignment interface).mpr checked)
            rw [failed] at absent
            cases absent
          rcases failure with ⟨goal, answer⟩
          simp [finish, missing, failed, notChecked]

/-- Unresolved errors depend only on the input assignment and interface,
not on impl visibility, multiplicity, or the existence of a unique candidate. -/
theorem undetermined_exact (m : Model) (decode : m.Ty → Roles.Term)
    (impls : List Roles.Impl) (wf : Roles.WellFormed impls)
    (assignment : α → Option (Comp m)) (interface : Interface α n) (slot : α) :
    finish m decode impls wf assignment interface = .error (.undetermined slot) ↔
      firstMissing interface assignment = some slot := by
  unfold finish
  cases firstMissing interface assignment <;> simp
  split <;> simp

theorem undetermined_exists_iff (m : Model) (decode : m.Ty → Roles.Term)
    (impls : List Roles.Impl) (wf : Roles.WellFormed impls)
    (assignment : α → Option (Comp m)) (interface : Interface α n) :
    (∃ slot, finish m decode impls wf assignment interface = .error (.undetermined slot)) ↔
      ∃ slot ∈ interface.support, assignment slot = none := by
  constructor
  · rintro ⟨slot, rejected⟩
    exact ⟨slot, firstMissing_sound interface assignment slot
      ((undetermined_exact m decode impls wf assignment interface slot).mp rejected)⟩
  · rintro ⟨slot, member, missing⟩
    cases found : firstMissing interface assignment with
    | some chosen =>
        exact ⟨chosen, (undetermined_exact m decode impls wf assignment interface chosen).mpr found⟩
    | none =>
        have known := (firstMissing_none_iff interface assignment).mp found
        obtain ⟨value, assigned⟩ := known_has_value interface assignment known slot member
        rw [missing] at assigned
        cases assigned

theorem undetermined_catalog_independent (m : Model) (decode : m.Ty → Roles.Term)
    (left right : List Roles.Impl) (leftWF : Roles.WellFormed left) (rightWF : Roles.WellFormed right)
    (assignment : α → Option (Comp m)) (interface : Interface α n) (slot : α) :
    finish m decode left leftWF assignment interface = .error (.undetermined slot) ↔
      finish m decode right rightWF assignment interface = .error (.undetermined slot) := by
  rw [undetermined_exact, undetermined_exact]

theorem role_error_exact (m : Model) (decode : m.Ty → Roles.Term)
    (impls : List Roles.Impl) (wf : Roles.WellFormed impls)
    (assignment : α → Option (Comp m)) (interface : Interface α n)
    (goal : Roles.Goal) (answer : Roles.Result) :
    finish m decode impls wf assignment interface = .error (.role goal answer) ↔
      firstMissing interface assignment = none ∧
        roleFailure impls wf (concreteGoals m decode assignment interface) = some (goal, answer) := by
  unfold finish
  cases firstMissing interface assignment <;> simp
  cases roleFailure impls wf (concreteGoals m decode assignment interface) with
  | none => simp
  | some failure => cases failure; simp

/-- A reported concrete-role failure follows determination of every support
slot and is an actual `noImpl` or `ambiguous` result, never `resolved`. -/
theorem role_error_sound (m : Model) (decode : m.Ty → Roles.Term)
    (impls : List Roles.Impl) (wf : Roles.WellFormed impls)
    (assignment : α → Option (Comp m)) (interface : Interface α n)
    (goal : Roles.Goal) (answer : Roles.Result)
    (rejected : finish m decode impls wf assignment interface = .error (.role goal answer)) :
    (∀ slot ∈ interface.support, ∃ value, assignment slot = some value) ∧
      goal ∈ concreteGoals m decode assignment interface ∧
      Roles.resolve impls wf goal = answer ∧ answer ≠ .resolved := by
  obtain ⟨missing, failure⟩ := (role_error_exact m decode impls wf assignment interface goal answer).mp rejected
  exact ⟨known_has_value interface assignment ((firstMissing_none_iff interface assignment).mp missing),
    roleFailure_sound impls wf _ goal answer failure⟩

theorem accepted_no_unresolved (m : Model) (decode : m.Ty → Roles.Term)
    (impls : List Roles.Impl) (wf : Roles.WellFormed impls)
    (assignment : α → Option (Comp m)) (interface : Interface α n)
    (closed : ClosedInterface m n)
    (accepted : finish m decode impls wf assignment interface = .ok closed) :
    (∀ slot ∈ interface.support, ∃ value, assignment slot = some value) ∧
      ∀ total, (∀ slot value, assignment slot = some value → total slot = value) →
        closed = interface.closeAt m total :=
  finishModule_no_unresolved_exports m decode impls wf assignment interface closed
    ((finish_success_iff m decode impls wf assignment interface closed).mp accepted)

/-- Arbitrary databases may alter role acceptance, but cannot select a
different exported type or qualifier once the same assignment is accepted. -/
theorem accepted_export_independent (m : Model) (decode : m.Ty → Roles.Term)
    (left right : List Roles.Impl) (leftWF : Roles.WellFormed left) (rightWF : Roles.WellFormed right)
    (assignment : α → Option (Comp m)) (interface : Interface α n)
    (leftClosed rightClosed : ClosedInterface m n)
    (leftAccepted : finish m decode left leftWF assignment interface = .ok leftClosed)
    (rightAccepted : finish m decode right rightWF assignment interface = .ok rightClosed) :
    leftClosed = rightClosed := by
  have leftExact := (finishModule_exact m decode left leftWF assignment interface leftClosed).mp
    ((finish_success_iff m decode left leftWF assignment interface leftClosed).mp leftAccepted)
  have rightExact := (finishModule_exact m decode right rightWF assignment interface rightClosed).mp
    ((finish_success_iff m decode right rightWF assignment interface rightClosed).mp rightAccepted)
  exact leftExact.2.2.symm.trans rightExact.2.2

/-- Adding visible impls preserves this exact export or reports overlap for a
previously determined goal. It cannot infer another type, produce a missing
slot, or lose a previously available impl. -/
theorem accepted_with_more_impls (m : Model) (decode : m.Ty → Roles.Term)
    {smaller larger : List Roles.Impl} (included : RoleVisibility.Included smaller larger)
    (smallWF : Roles.WellFormed smaller) (largeWF : Roles.WellFormed larger)
    (assignment : α → Option (Comp m)) (interface : Interface α n)
    (closed : ClosedInterface m n)
    (accepted : finish m decode smaller smallWF assignment interface = .ok closed) :
    finish m decode larger largeWF assignment interface = .ok closed ∨
      ∃ goal, finish m decode larger largeWF assignment interface = .error (.role goal .ambiguous) := by
  obtain ⟨known, satisfied, same⟩ :=
    (finishModule_exact m decode smaller smallWF assignment interface closed).mp
      ((finish_success_iff m decode smaller smallWF assignment interface closed).mp accepted)
  have missing := (firstMissing_none_iff interface assignment).mpr known
  have solved := (concreteGoals_resolve_iff m decode smaller smallWF assignment interface).mpr
    ((pendingCheck_exact m decode smaller smallWF _ interface).mpr satisfied)
  cases failed : roleFailure larger largeWF (concreteGoals m decode assignment interface) with
  | none => exact Or.inl (by simp [finish, missing, failed, same])
  | some failure =>
      rcases failure with ⟨goal, answer⟩
      obtain ⟨member, actual, notResolved⟩ := roleFailure_sound larger largeWF _ goal answer failed
      have ambiguous : answer = .ambiguous := by
        rcases RoleVisibility.resolved_mono included smallWF largeWF goal (solved goal member) with
          resolved | ambiguous
        · exact (notResolved (actual.symm.trans resolved)).elim
        · exact actual.symm.trans ambiguous
      exact Or.inr ⟨goal, by simp [finish, missing, failed, ambiguous]⟩

def finishFile [DecidableEq File] (m : Model) (decode : m.Ty → Roles.Term)
    (scope : ModuleVisibility.FileScope File) (catalog : List (ModuleVisibility.Declaration File))
    (wf : Roles.WellFormed (scope.select catalog)) (assignment : α → Option (Comp m))
    (interface : Interface α n) : Except (Failure α) (ClosedInterface m n) :=
  finish m decode (scope.select catalog) wf assignment interface

theorem finishFile_success_iff [DecidableEq File] (m : Model) (decode : m.Ty → Roles.Term)
    (scope : ModuleVisibility.FileScope File) (catalog : List (ModuleVisibility.Declaration File))
    (wf : Roles.WellFormed (scope.select catalog)) (assignment : α → Option (Comp m))
    (interface : Interface α n) (closed : ClosedInterface m n) :
    finishFile m decode scope catalog wf assignment interface = .ok closed ↔
      ModuleVisibility.finish m decode scope catalog wf assignment interface = some closed :=
  finish_success_iff m decode (scope.select catalog) wf assignment interface closed

namespace Examples

open QualifiedExamples ModuleVisibility.Examples

theorem unique_visible_impl_does_not_complete :
    finishFile model decode (scope 0 []) catalog localWF (fun _ : Unit => none) capturedInterface =
      .error (.undetermined ()) := rfl

theorem annotation_determined_slot_is_accepted :
    finishFile model decode (scope 0 []) catalog localWF knownInt capturedInterface =
      .ok (capturedInterface.closeAt model (fun _ => (Roles.Term.app 0 [], ()))) :=
  (finishFile_success_iff model decode (scope 0 []) catalog localWF knownInt capturedInterface _).mpr
    current_file_uses_own_impl

theorem import_cannot_complete_slot :
    finishFile model decode (scope 1 [0]) catalog importedWF (fun _ : Unit => none) capturedInterface =
      .error (.undetermined ()) := rfl

theorem no_import_still_reports_undetermined :
    finishFile model decode (scope 1 []) catalog hiddenWF (fun _ : Unit => none) capturedInterface =
      .error (.undetermined ()) := rfl

/-- The weak slot occurs only in an obligation, not the exported value. -/
theorem residual_only_slot_is_still_checked :
    ambientVariables (typeVariables capturedInterface.value) = [] ∧
      finish model decode [addIntImpl] addInt_wf (fun _ : Unit => none) capturedInterface =
        .error (.undetermined ()) := ⟨rfl, rfl⟩

def weakExport : Interface Unit 0 := ⟨.var (.inl ()), []⟩

theorem unqualified_weak_export_is_rejected :
    finish model decode [addIntImpl] addInt_wf (fun _ : Unit => none) weakExport =
      .error (.undetermined ()) := rfl

theorem known_type_without_import_reports_concrete_noImpl :
    finishFile model decode (scope 1 []) catalog hiddenWF knownInt capturedInterface =
      .error (.role ⟨0, [.app 0 []]⟩ .noImpl) := by
  have missing : Roles.resolve ((scope 1 []).select catalog) hiddenWF
      ⟨0, [Roles.Term.app 0 []]⟩ = .noImpl := Roles.resolve_none _ _ _ rfl
  change (match roleFailure ((scope 1 []).select catalog) hiddenWF [⟨0, [.app 0 []]⟩] with
    | some (goal, answer) => Except.error (Failure.role goal answer)
    | none => Except.ok _) = _
  simp [roleFailure, missing]

def addStrImpl : Roles.Impl := ⟨0, [.app 1 []], [], 21⟩

theorem expandedWF : Roles.WellFormed [addIntImpl, addStrImpl] := by
  simp [Roles.WellFormed, Roles.Impl.WellFormed, addIntImpl, addStrImpl]

theorem extra_impl_does_not_complete_slot :
    finish model decode [addIntImpl, addStrImpl] expandedWF (fun _ : Unit => none) capturedInterface =
      .error (.undetermined ()) := rfl

theorem extra_impl_preserves_annotated_type :
    finish model decode [addIntImpl, addStrImpl] expandedWF knownInt capturedInterface =
      .ok (capturedInterface.closeAt model (fun _ => (Roles.Term.app 0 [], ()))) := by
  have resolved : Roles.resolve [addIntImpl, addStrImpl] expandedWF
      ⟨0, [Roles.Term.app 0 []]⟩ = .resolved := by
    rw [Roles.resolve_one _ _ _ addIntImpl (by decide)]
    rfl
  change (match roleFailure [addIntImpl, addStrImpl] expandedWF [⟨0, [.app 0 []]⟩] with
    | some (goal, answer) => Except.error (Failure.role goal answer)
    | none => Except.ok (capturedInterface.closeAt model (fun _ => (Roles.Term.app 0 [], ())))) = _
  simp [roleFailure, resolved]

theorem generalized_qualifier_is_not_an_undetermined_slot :
    finish model decode [] empty_impls_wellFormed (fun e : Empty => nomatch e) twiceInterface =
      .ok (twiceInterface.closeAt model Empty.elim) := rfl

end Examples

end Yulang.EOFNoDefaulting
