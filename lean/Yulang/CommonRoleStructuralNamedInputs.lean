import Yulang.CommonRoleStructuralHornSchedules
import Yulang.CommonRoleStructuralAssociatedTemplates

/-! Named structural ordinary atoms compute their own finite allocation and
checked State. The existing finite structural Program computes receiver goals;
no external slot map, dimension, checked state or higher-order template is
supplied. Parser/scope adequacy and dynamic occurrence creation remain outside.
One unused internal slot makes allocation total on names absent from the source. -/
namespace Yulang.CommonRoleStructuralNamedInputs
open Core.PresenceGeneration (TyTerm RowTerm Comp)
open PresenceNormalForm (Atom All)
open CommonRoleSettledConstraints (State)
open CommonRoleStructuralAssociatedTemplates (Program)

def rowNames : RowTerm Nat → List Nat
  | .var a => [a] | .empty => [] | .join a b => rowNames a ++ rowNames b

def tyNames : TyTerm Nat → List Nat
  | .var a => [a]
  | .base _ | .bottom | .top | .emptyRecord | .exactEmpty => []
  | .union a b | .inter a b | .pair a b | .record _ a b | .recordDefault _ a b => tyNames a ++ tyNames b
  | .required _ a | .variant _ a => tyNames a
  | .arrow a ea b eb => tyNames a ++ rowNames ea ++ tyNames b ++ rowNames eb

def atomNames : Atom Nat → List Nat
  | .tyLe a b => tyNames a ++ tyNames b
  | .rowLe a b => rowNames a ++ rowNames b

structure Source where
  program : Program
  atoms : List (Atom Nat)

def names (src : Source) : List Nat :=
  (src.program.flatMap (fun q => [q.receiver,q.output]) ++ src.atoms.flatMap atomNames).eraseDups

def capacity (src : Source) := (names src).length + 1

def slot (src : Source) (name : Nat) : Fin (capacity src) :=
  ⟨(names src).idxOf name,Nat.lt_succ_of_le List.idxOf_le_length⟩

def readName (src : Source) (i : Fin (capacity src)) : Nat := ((names src)[i.val]?).getD 0

theorem slot_present (src : Source) (name : Nat) (present : name ∈ names src) :
    (slot src name).val < (names src).length := List.idxOf_lt_length_of_mem present

theorem read_slot (src : Source) (name : Nat) (present : name ∈ names src) :
    readName src (slot src name) = name := by
  simp only [readName,slot,List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem present),Option.getD_some]
  exact List.getElem_idxOf _

/-- Present source identities neither merge nor use the unused internal slot. -/
theorem slot_injective (src : Source) (a b : Nat) (ha : a ∈ names src) (hb : b ∈ names src) :
    slot src a = slot src b ↔ a = b := by
  constructor
  · intro same
    have equal := congrArg (readName src) same
    simpa only [read_slot src a ha,read_slot src b hb] using equal
  · intro same; subst b; rfl

theorem atom_names_present (src : Source) (a : Atom Nat) (member : a ∈ src.atoms)
    (name : Nat) (present : name ∈ atomNames a) : name ∈ names src := by
  simp only [names,List.mem_eraseDups,List.mem_append,List.mem_flatMap]
  exact Or.inr ⟨a,member,present⟩

theorem occurrence_names_present (src : Source) (q : CommonRoleStructuralAssociatedTemplates.Occurrence)
    (member : q ∈ src.program) : q.receiver ∈ names src ∧ q.output ∈ names src := by
  constructor <;> simp only [names,List.mem_eraseDups,List.mem_append,List.mem_flatMap]
  · exact Or.inl ⟨q,member,by simp⟩
  · exact Or.inl ⟨q,member,by simp⟩

/-- The actual ordinary compiler is just the established capture-free rename. -/
def atoms (src : Source) := src.atoms.map (Atom.rename (slot src))

theorem row_eval_congr (t : RowTerm Nat) (v w : Nat → Comp Common.model)
    (same : ∀ a ∈ rowNames t, v a = w a) : t.eval Common.model v = t.eval Common.model w := by
  induction t with
  | var a => exact congrArg Prod.snd (same a (by simp [rowNames]))
  | empty => rfl
  | join a b ia ib =>
    simp only [RowTerm.eval]
    rw [ia (fun x h => same x (List.mem_append_left _ h)),
      ib (fun x h => same x (List.mem_append_right _ h))]

theorem ty_eval_congr (t : TyTerm Nat) (v w : Nat → Comp Common.model)
    (same : ∀ a ∈ tyNames t, v a = w a) : t.eval Common.model v = t.eval Common.model w := by
  induction t with
  | var a => exact congrArg Prod.fst (same a (by simp [tyNames]))
  | arrow a ea b eb ia ib =>
    simp only [TyTerm.eval]
    rw [ia (fun x h => same x (by simp [tyNames,h])),
      row_eval_congr ea v w (fun x h => same x (by simp [tyNames,h])),
      ib (fun x h => same x (by simp [tyNames,h])),
      row_eval_congr eb v w (fun x h => same x (by simp [tyNames,h]))]
  | _ => simp_all [TyTerm.eval,tyNames]

theorem atom_holds_congr (a : Atom Nat) (v w : Nat → Comp Common.model)
    (same : ∀ name ∈ atomNames a, v name = w name) :
    a.Holds Common.model v ↔ a.Holds Common.model w := by
  cases a with
  | tyLe a b =>
    simp only [Atom.Holds]
    rw [ty_eval_congr a v w (fun x h => same x (List.mem_append_left _ h)),
      ty_eval_congr b v w (fun x h => same x (List.mem_append_right _ h))]
  | rowLe a b =>
    simp only [Atom.Holds]
    rw [row_eval_congr a v w (fun x h => same x (List.mem_append_left _ h)),
      row_eval_congr b v w (fun x h => same x (List.mem_append_right _ h))]

/-- Every named model restricts to an allocated model, including rows; no
identity coincidence or unused-slot value is used to justify a constraint. -/
theorem allocated_models (src : Source) (v : Nat → Comp Common.model) :
    All Common.model (v ∘ readName src) (atoms src) ↔ All Common.model v src.atoms := by
  rw [atoms,PresenceNormalForm.all_rename]
  apply forall_congr'
  intro a
  apply forall_congr'
  intro member
  exact atom_holds_congr a _ v (fun x hx => by
    simp only [Function.comp_apply,read_slot src x (atom_names_present src a member x hx)])

/-- Conversely every finite assignment defines a named model of the original
ordinary atoms. Source names not present in the input have no obligations. -/
theorem source_models (src : Source) (v : Fin (capacity src) → Comp Common.model) :
    All Common.model v (atoms src) ↔ All Common.model (v ∘ slot src) src.atoms :=
  PresenceNormalForm.all_rename Common.model v (slot src) src.atoms

def grammarAtom (all : List (Atom Nat)) : Atom Nat → Bool
  | .tyLe a b => PresenceGeneratedChildGrammar.lower a && PresenceGeneratedChildGrammar.upper b &&
      PresenceSourceConstraintSupport.simpleTyRows a && PresenceSourceConstraintSupport.simpleTyRows b &&
      match PresenceGeneratedWidth.widthTail a with
      | none => true | some tail => decide (Atom.tyLe tail .emptyRecord ∈ all)
  | .rowLe _ b => PresenceSourceConstraintSupport.simpleRow b

def grammar (src : Source) := src.atoms.all (grammarAtom src.atoms)
def Good (src : Source) := PresenceGeneratedChildGrammar.GoodAtoms src.atoms ∧
  PresenceGeneratedWidth.WidthAtoms src.atoms ∧ PresenceSourceConstraintSupport.GoodAtoms src.atoms

/-- This checker recognizes exactly the existing ordinary State grammar. It
does not add a new language rejection rule for other syntax. -/
theorem grammar_exact (src : Source) : grammar src = true ↔ Good src := by
  simp only [grammar,List.all_eq_true]
  constructor
  · intro checked
    refine ⟨?_,?_,?_⟩
    · intro a member
      have h := checked a member
      cases a <;> simp_all [grammarAtom,PresenceGeneratedChildGrammar.GoodAtom,Bool.and_eq_true]
    · intro a b member tail found
      have h := checked (.tyLe a b) member
      simp only [grammarAtom,found,Bool.and_eq_true,decide_eq_true_eq] at h
      exact h.2
    · intro a member
      have h := checked a member
      cases a <;> simp_all [grammarAtom,PresenceSourceConstraintSupport.GoodAtom,Bool.and_eq_true]
  · rintro ⟨child,width,rows⟩ a member
    have hc := child a member
    have hr := rows a member
    cases a with
    | rowLe a b => exact hr
    | tyLe a b =>
      simp only [grammarAtom,Bool.and_eq_true]
      refine ⟨⟨⟨⟨hc.1,hc.2⟩,hr.1⟩,hr.2⟩,?_⟩
      cases found : PresenceGeneratedWidth.widthTail a with
      | none => rfl
      | some tail => exact decide_eq_true (width a b member tail found)

def prepare (src : Source) : Option (State (capacity src)) :=
  if accepted : grammar src = true then
    let good := (grammar_exact src).mp accepted
    some ⟨atoms src,good.1.rename _,good.2.1.rename _,good.2.2.rename _⟩
  else none

theorem prepare_exact (src : Source) (s : State (capacity src)) :
    prepare src = some s ↔ Good src ∧ s.atoms = atoms src := by
  unfold prepare
  split
  · rename_i good
    constructor
    · intro h; cases h; exact ⟨(grammar_exact src).mp good,rfl⟩
    · rintro ⟨_,same⟩; cases s; simp_all
  · rename_i bad
    constructor
    · intro h; cases h
    · rintro ⟨good,_⟩; exact False.elim (bad ((grammar_exact src).mpr good))

/-- Receiver goals come from the existing checked structural template syntax. -/
def occurrence (src : Source) (q : CommonRoleStructuralAssociatedTemplates.Occurrence) :
    CommonRoleFiniteAssociatedClosure.Occurrence (capacity src) :=
  ⟨slot src q.receiver,slot src q.output,q.name,CommonRoleStructuralAssociatedTemplates.generate q.template⟩
def occurrences (src : Source) := src.program.map (occurrence src)

/-- Complete raw named input through the actual ordinary solver. Success means
ordinary consistency after mixed closure, not discharge of every source role. -/
def run (env : Roles.AssocEnv) (roles : Roles.RoleDecls) (wf : Roles.WellFormed env.cores) (src : Source) :
    Option (State (capacity src)) :=
  (prepare src).bind fun initial =>
    let final := CommonRoleStructuralAssociatedSolver.completeState env roles wf (occurrences src) initial
    if CommonRoleOpenPropagation.consistent final then some final else none

/-- No external State, dimension, slot map, carrier, batch, or model premise.
Independent derivation exactness remains on the compiled finite source carrier;
full named parser adequacy is deliberately not claimed. -/
theorem run_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls) (wf : Roles.WellFormed env.cores)
    (awf : Roles.AssocWellFormed env roles) (src : Source) :
    (run env roles wf src).isSome = true ↔ Good src ∧
      ∃ v : Fin (capacity src) → Comp Common.model, ∀ a,
        CommonRoleStructuralAssociatedClosure.Derives env roles (occurrences src) (atoms src) a →
          a.Holds Common.model v := by
  unfold run
  cases prepared : prepare src with
  | none =>
    simp only [Option.bind_none,Option.isSome_none,Bool.false_eq_true,false_iff,not_and]
    intro good _
    unfold prepare at prepared
    rw [dite_eq_left ((grammar_exact src).mpr good)] at prepared
    cases prepared
  | some initial =>
    obtain ⟨good,same⟩ := (prepare_exact src initial).mp prepared
    simp only [Option.bind_some]
    by_cases checked : CommonRoleOpenPropagation.consistent
        (CommonRoleStructuralAssociatedSolver.completeState env roles wf (occurrences src) initial) = true
    · simp only [checked,ite_true,Option.isSome_some,true_iff]
      refine ⟨good,?_⟩
      have models := (CommonRoleStructuralAssociatedSolver.solver_exact env roles wf awf ..).mp checked
      simpa only [same] using models
    · simp only [checked,ite_false,Option.isSome_none,Bool.false_eq_true,false_iff,not_and]
      intro _ models
      apply checked
      apply (CommonRoleStructuralAssociatedSolver.solver_exact env roles wf awf ..).mpr
      simpa only [same] using models

/-- Declaration provenance is independent of the compiled output index. -/
theorem occurrence_step (env : Roles.AssocEnv) (roles : Roles.RoleDecls) (src : Source)
    (q : CommonRoleStructuralAssociatedTemplates.Occurrence) (head result : Inference.Base) :
    CommonRoleAssociatedDeclarationExact.DeclarativeComputed env roles
      (CommonRoleFiniteAssociatedClosure.request (occurrence src q) head) result ↔
      CommonRoleStructuralAssociatedTemplates.Step env roles q head result :=
  CommonRoleStructuralAssociatedTemplates.step_exact env roles q head result

/-- Knownness is independent structural/associated derivation on the computed
carrier. This is not yet a source-parser typing judgment. -/
def Known (env : Roles.AssocEnv) (roles : Roles.RoleDecls) (src : Source)
    (name : Nat) (head : Inference.Base) :=
  ∀ a ∈ CommonRoleCandidateStateFrontier.equality (slot src name) head,
    CommonRoleStructuralAssociatedClosure.Derives env roles (occurrences src) (atoms src) a

def SourceModels (env : Roles.AssocEnv) (roles : Roles.RoleDecls) (src : Source)
    (v : Fin (capacity src) → Comp Common.model) :=
  All Common.model (v ∘ slot src) src.atoms ∧
    ∀ q ∈ src.program, ∀ head result, Known env roles src q.receiver head →
      CommonRoleStructuralAssociatedTemplates.Step env roles q head result →
      Common.Equivalent (v (slot src q.output)).1 (.base result)

/-- Every final model retains all original named structural atoms and exactly
those named associated equations whose receiver is independently derivable.
Names and structural templates are not supplied by a separate correctness oracle. -/
theorem complete_source_models (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (src : Source) (initial : State (capacity src)) (prepared : prepare src = some initial)
    (v : Fin (capacity src) → Comp Common.model) :
    All Common.model v (CommonRoleStructuralAssociatedSolver.completeState env roles wf
      (occurrences src) initial).atoms ↔ SourceModels env roles src v := by
  have same := ((prepare_exact src initial).mp prepared).2
  rw [CommonRoleStructuralAssociatedSolver.completeState_models env roles wf awf,
    CommonRoleStructuralAssociatedClosure.models_exact env roles wf awf,same,source_models]
  apply and_congr_right
  intro _
  constructor
  · intro all q member head result known step
    apply (CommonRoleStructuralAssociatedSolver.equality_models (slot src q.output) result v).mp
    exact all (occurrence src q) (List.mem_map.mpr ⟨q,member,rfl⟩) head result known
      ((occurrence_step env roles src q head result).mpr step)
  · intro all q member head result known step
    obtain ⟨source,sourceMember,rfl⟩ := List.mem_map.mp member
    apply (CommonRoleStructuralAssociatedSolver.equality_models (slot src source.output) result v).mpr
    exact all source sourceMember head result known ((occurrence_step env roles src source head result).mp step)

/-- Exact all-model contract for the successful named public entry. No role
success is inferred merely from ordinary consistency. -/
theorem run_source_models (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (src : Source) (output : State (capacity src)) (returned : run env roles wf src = some output)
    (v : Fin (capacity src) → Comp Common.model) :
    All Common.model v output.atoms ↔ SourceModels env roles src v := by
  unfold run at returned
  cases prepared : prepare src with
  | none => simp [prepared] at returned
  | some initial =>
    simp only [prepared,Option.bind_some] at returned
    split at returned
    · cases returned
      exact complete_source_models env roles wf awf src initial prepared v
    · cases returned

/-- Final public existence contract in original-name model terms. The two
explicit requirements are the existing ordinary grammar and satisfiability
of all named ordinary atoms plus independently activated source equations.
This is not source-role selection or whole-language typing exactness. -/
theorem run_source_exists_iff (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles) (src : Source) :
    (run env roles wf src).isSome = true ↔ Good src ∧
      ∃ v : Fin (capacity src) → Comp Common.model, SourceModels env roles src v := by
  cases prepared : prepare src with
  | none =>
    have bad : ¬ Good src := by
      intro good
      unfold prepare at prepared
      rw [dite_eq_left ((grammar_exact src).mpr good)] at prepared
      cases prepared
    simp [run,prepared,bad]
  | some initial =>
    have good := ((prepare_exact src initial).mp prepared).1
    have equivalent : (CommonRoleStructuralAssociatedSolver.completeState env roles wf
        (occurrences src) initial).Models ↔ ∃ v, SourceModels env roles src v := by
      exact exists_congr (complete_source_models env roles wf awf src initial prepared)
    unfold run
    simp only [prepared,Option.bind_some]
    by_cases consistent : CommonRoleOpenPropagation.consistent
        (CommonRoleStructuralAssociatedSolver.completeState env roles wf (occurrences src) initial) = true
    · simp only [consistent,ite_true,Option.isSome_some,true_iff]
      exact ⟨good,equivalent.mp ((CommonRoleOpenPropagation.consistent_exact _).mp consistent)⟩
    · simp only [consistent,ite_false,Option.isSome_none,Bool.false_eq_true,false_iff,not_and]
      intro _ models
      exact consistent ((CommonRoleOpenPropagation.consistent_exact _).mpr (equivalent.mpr models))

end Yulang.CommonRoleStructuralNamedInputs
