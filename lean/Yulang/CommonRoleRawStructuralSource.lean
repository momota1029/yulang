import Yulang.CommonRoleNamedStructuralDerivations

/-! Raw structural associated source programs carry no scope certificates.
Checking reconstructs the existing single-placeholder fragment, preserving every
occurrence and source name. Failure means outside this adapter, not a newly
chosen language-level rejection. Parsing and dynamic child creation remain open. -/
namespace Yulang.CommonRoleRawStructuralSource
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (Atom All)
namespace Checked
abbrev Occurrence := CommonRoleStructuralAssociatedTemplates.Occurrence
abbrev Program := CommonRoleStructuralAssociatedTemplates.Program
abbrev Source := CommonRoleStructuralNamedInputs.Source
end Checked

structure Occurrence where
  receiver : Nat
  output : Nat
  name : Nat
  goal : Roles.Goal
  deriving DecidableEq, Repr
abbrev Program := List Occurrence
structure Source where
  program : Program
  atoms : List (Atom Nat)

def eraseOccurrence (q : Checked.Occurrence) : Occurrence :=
  ⟨q.receiver,q.output,q.name,q.template.goal⟩
def eraseProgram (p : Checked.Program) : Program := p.map eraseOccurrence

def checkOccurrence (q : Occurrence) : Option Checked.Occurrence :=
  (CommonRoleStructuralAssociatedTemplates.check q.goal).map fun t =>
    ⟨q.receiver,q.output,q.name,t⟩

def checkProgram : Program → Option Checked.Program
  | [] => some []
  | q :: qs => (checkOccurrence q).bind fun head =>
      (checkProgram qs).map (fun tail => head :: tail)

def Scoped (p : Program) := ∀ q ∈ p, Roles.argsBound q.goal.args ≤ 1

theorem check_template_exact (g : Roles.Goal) (t : CommonRoleStructuralAssociatedTemplates.Template) :
    CommonRoleStructuralAssociatedTemplates.check g = some t ↔ t.goal = g := by
  constructor
  · exact CommonRoleStructuralAssociatedTemplates.checked_goal g t
  · intro same
    subst g
    unfold CommonRoleStructuralAssociatedTemplates.check
    rw [dite_eq_left t.scope_ok]

theorem check_occurrence_exact (q : Occurrence) (t : Checked.Occurrence) :
    checkOccurrence q = some t ↔ eraseOccurrence t = q := by
  unfold checkOccurrence
  rw [Option.map_eq_some_iff]
  constructor
  · rintro ⟨template,checked,same⟩
    subst t
    have goal := (check_template_exact q.goal template).mp checked
    cases q
    simp_all [eraseOccurrence]
  · intro same
    rw [← same]
    exact ⟨t.template,(check_template_exact _ _).mpr rfl,by cases t; rfl⟩

theorem check_program_exact (p : Program) (q : Checked.Program) :
    checkProgram p = some q ↔ eraseProgram q = p := by
  induction p generalizing q with
  | nil => cases q <;> simp [checkProgram,eraseProgram]
  | cons first rest ih =>
    simp only [checkProgram,Option.bind_eq_some_iff,Option.map_eq_some_iff]
    constructor
    · rintro ⟨head,hhead,tail,htail,same⟩
      cases same
      simp only [eraseProgram,List.map_cons]
      rw [(check_occurrence_exact first head).mp hhead]
      exact congrArg (first :: ·) ((ih tail).mp htail)
    · intro same
      cases q with
      | nil => simp [eraseProgram] at same
      | cons head tail =>
        obtain ⟨hhead,htail⟩ := List.cons.inj same
        exact ⟨head,(check_occurrence_exact first head).mpr hhead,tail,(ih tail).mpr htail,rfl⟩

theorem erase_scoped (p : Checked.Program) : Scoped (eraseProgram p) := by
  intro q member
  obtain ⟨checked,_,rfl⟩ := List.mem_map.mp member
  exact checked.template.scope_ok

theorem check_occurrence_accepts (q : Occurrence) :
    (checkOccurrence q).isSome = true ↔ Roles.argsBound q.goal.args ≤ 1 := by
  simp only [checkOccurrence,Option.isSome_map]
  exact CommonRoleStructuralAssociatedTemplates.check_accepts q.goal

theorem check_program_accepts (p : Program) :
    (checkProgram p).isSome = true ↔ Scoped p := by
  induction p with
  | nil => simp [checkProgram,Scoped]
  | cons q qs ih =>
    simp only [checkProgram]
    constructor
    · intro h
      cases checked : checkOccurrence q with
      | none => simp [checked] at h
      | some head =>
        have tail : (checkProgram qs).isSome = true := by simpa [checked] using h
        have scope : Roles.argsBound q.goal.args ≤ 1 :=
          (check_occurrence_accepts q).mp (by simp [checked])
        intro x member
        rcases List.mem_cons.mp member with rfl | member
        · exact scope
        · exact ih.mp tail x member
    · intro scope
      have accepted := (check_occurrence_accepts q).mpr (scope q (by simp))
      cases checked : checkOccurrence q with
      | none => simp [checked] at accepted
      | some head =>
        have tail := ih.mpr (fun x member => scope x (List.mem_cons_of_mem q member))
        simp [tail]

/-- Structural materialization is specified directly on raw goal syntax. -/
def Step (env : Roles.AssocEnv) (roles : Roles.RoleDecls) (q : Occurrence)
    (head result : Inference.Base) : Prop :=
  ∃ payload, CommonRoleOrdinaryKnownness.encode head = some payload ∧
    ∃ g : Roles.Goal, g.role = q.goal.role ∧
      CommonRoleStructuralAssociatedTemplates.Fills payload q.goal.args g.args ∧
      RoleConstraints.Resolves env.cores g ∧ ∃ rhs,
        Roles.AssocDerives env roles g q.name rhs ∧ CommonRoleAssociatedStateFlow.scalar rhs = some result

theorem step_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls) (q : Checked.Occurrence)
    (head result : Inference.Base) :
    CommonRoleStructuralAssociatedTemplates.Step env roles q head result ↔
      Step env roles (eraseOccurrence q) head result := by
  constructor
  · rintro ⟨g,⟨payload,encoded,role,filled⟩,resolved,rhs,derived,scalar⟩
    exact ⟨payload,encoded,g,role,filled,resolved,rhs,derived,scalar⟩
  · rintro ⟨payload,encoded,g,role,filled,resolved,rhs,derived,scalar⟩
    exact ⟨g,⟨payload,encoded,role,filled⟩,resolved,rhs,derived,scalar⟩

abbrev equalities := CommonRoleNamedStructuralDerivations.equalities
inductive Derives (env : Roles.AssocEnv) (roles : Roles.RoleDecls) (src : Source) : Atom Nat → Prop
  | seed (a) : a ∈ src.atoms → Derives env roles src a
  | split (a b) : Derives env roles src a → b ∈ CommonRoleStructuralDecomposition.atom a →
      Derives env roles src b
  | trans (l m r) : Derives env roles src (.tyLe l m) → Derives env roles src (.tyLe m r) →
      Derives env roles src (.tyLe l r)
  | associated (q head result a) : q ∈ src.program →
      (∀ b ∈ equalities q.receiver head, Derives env roles src b) →
      Step env roles q head result → a ∈ equalities q.output result → Derives env roles src a

def erase (src : Checked.Source) : Source := ⟨eraseProgram src.program,src.atoms⟩

/-- Checking neither adds nor removes derivations, including contradictory
associated feedback and repeated source occurrences. -/
theorem derives_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls) (src : Checked.Source) (a) :
    CommonRoleNamedStructuralDerivations.Derives env roles src a ↔ Derives env roles (erase src) a := by
  constructor
  · intro h
    induction h with
    | seed a member => exact .seed a member
    | split a b _ member ih => exact .split a b ih member
    | trans l m r _ _ iha ihb => exact .trans l m r iha ihb
    | associated q head result a member _ step eqs ih =>
      exact .associated (eraseOccurrence q) head result a (List.mem_map.mpr ⟨q,member,rfl⟩)
        ih ((step_exact env roles q head result).mp step) eqs
  · intro h
    induction h with
    | seed a member => exact .seed a member
    | split a b _ member ih => exact .split a b ih member
    | trans l m r _ _ iha ihb => exact .trans l m r iha ihb
    | associated q head result a member _ step eqs ih =>
      obtain ⟨original,sourceMem,rfl⟩ := List.mem_map.mp member
      exact .associated original head result a sourceMem ih
        ((step_exact env roles original head result).mpr step) eqs

def Known (env : Roles.AssocEnv) (roles : Roles.RoleDecls) (src : Source) (name : Nat) (head : Inference.Base) :=
  ∀ a ∈ equalities name head, Derives env roles src a

def Models (env : Roles.AssocEnv) (roles : Roles.RoleDecls) (src : Source) (v : Nat → Comp Common.model) :=
  All Common.model v src.atoms ∧ ∀ q ∈ src.program, ∀ head result,
    Known env roles src q.receiver head → Step env roles q head result →
      Common.Equivalent (v q.output).1 (.base result)

theorem models_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (src : Checked.Source) (v : Nat → Comp Common.model) :
    CommonRoleNamedStructuralDerivations.Models env roles src v ↔ Models env roles (erase src) v := by
  apply and_congr_right
  intro _
  constructor
  · intro model q member head result known step
    obtain ⟨original,sourceMem,rfl⟩ := List.mem_map.mp member
    exact model original sourceMem head result
      (fun a member => (derives_exact env roles src a).mpr (known a member))
      ((step_exact env roles original head result).mpr step)
  · intro model q member head result known step
    exact model (eraseOccurrence q) (List.mem_map.mpr ⟨q,member,rfl⟩) head result
      (fun a member => (derives_exact env roles src a).mp (known a member))
      ((step_exact env roles q head result).mp step)

def check (src : Source) : Option Checked.Source :=
  (checkProgram src.program).map fun p => ⟨p,src.atoms⟩

theorem check_exact (src : Source) (checked : Checked.Source) :
    check src = some checked ↔ erase checked = src := by
  unfold check
  rw [Option.map_eq_some_iff]
  constructor
  · rintro ⟨p,hp,same⟩
    subst checked
    have program := (check_program_exact src.program p).mp hp
    cases src
    simp_all [erase]
  · intro same
    rw [← same]
    exact ⟨checked.program,(check_program_exact _ _).mpr rfl,by cases checked; rfl⟩

theorem check_accepts (src : Source) : (check src).isSome = true ↔ Scoped src.program := by
  simp only [check,Option.isSome_map,check_program_accepts]

/-- Existing ordinary grammar, with no checked State supplied by the caller. -/
def Good (src : Source) := PresenceGeneratedChildGrammar.GoodAtoms src.atoms ∧
  PresenceGeneratedWidth.WidthAtoms src.atoms ∧ PresenceSourceConstraintSupport.GoodAtoms src.atoms

abbrev Output := (src : Checked.Source) × CommonRoleSettledConstraints.State (CommonRoleStructuralNamedInputs.capacity src)

def run (env : Roles.AssocEnv) (roles : Roles.RoleDecls) (wf : Roles.WellFormed env.cores) (src : Source) :
    Option Output :=
  (check src).bind fun checked =>
    (CommonRoleStructuralNamedInputs.run env roles wf checked).map (fun output => ⟨checked,output⟩)

theorem run_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles) (src : Source) :
    (run env roles wf src).isSome = true ↔ Scoped src.program ∧ Good src ∧
      ∃ v : Nat → Comp Common.model, Models env roles src v := by
  cases checked : check src with
  | none =>
    have bad : ¬ Scoped src.program := by
      intro h
      have := (check_accepts src).mpr h
      simp [checked] at this
    simp [run,checked,bad]
  | some source =>
    have scope := (check_accepts src).mp (by simp [checked])
    have same := (check_exact src source).mp checked
    simp only [run,checked,Option.bind_some,Option.isSome_map]
    rw [CommonRoleNamedStructuralDerivations.run_named_exists_iff env roles wf awf source]
    rw [← same]
    simp only [erase,erase_scoped,true_and]
    apply and_congr Iff.rfl
    exact exists_congr (models_exact env roles source)

/-- Returned packages contain precisely the checked original syntax. -/
theorem run_origin (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (src : Source) (output : Output)
    (returned : run env roles wf src = some output) : erase output.1 = src := by
  unfold run at returned
  obtain ⟨checked,hcheck,mapped⟩ := Option.bind_eq_some_iff.mp returned
  obtain ⟨state,_,same⟩ := Option.map_eq_some_iff.mp mapped
  cases same
  exact (check_exact src checked).mp hcheck

/-- All original-name valuations, not a chosen witness, satisfy exactly the
constraints of the returned raw-source run. -/
theorem run_models (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (src : Source) (output : Output) (returned : run env roles wf src = some output)
    (v : Nat → Comp Common.model) :
    All Common.model (v ∘ CommonRoleStructuralNamedInputs.readName output.1) output.2.atoms ↔
      Models env roles src v := by
  unfold run at returned
  obtain ⟨checked,hcheck,mapped⟩ := Option.bind_eq_some_iff.mp returned
  obtain ⟨state,hstate,same⟩ := Option.map_eq_some_iff.mp mapped
  cases same
  rw [CommonRoleNamedStructuralDerivations.run_named_models env roles wf awf checked state hstate,
    models_exact env roles checked v,(check_exact src checked).mp hcheck]

end Yulang.CommonRoleRawStructuralSource
