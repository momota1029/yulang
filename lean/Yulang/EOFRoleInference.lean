import Yulang.ModuleVisibility
import Yulang.Methods

/-!
# Declaration-derived EOF inference for ground anchor heads

This executable fragment infers a finite tuple of remaining weak value types
from the impl declarations actually visible in a file. A residual anchor
predicate mentions every remaining type slot directly. Only the heads for that
anchor role must be ground; nested `where` obligations and the other residual
roles use the ordinary, possibly polymorphic, terminating resolver.

Rows have already been solved. A lossless first-order representation and an
executable check for the remaining ordinary constraints are explicit inputs.
The candidate type tuples are computed from the visible declaration heads;
there is no supplied finite universe or completeness assumption about it.

The result classifies fully resolving completions. In particular, `missing`
means no completion passes all the checks, not the resolver's `noImpl` error:
an overlapping concrete head may also prevent a completion. A unique *type
tuple*, rather than a unique impl declaration, is required for this fragment's
success. Success returns the inferred assignment and the actual `finishModule`
result, preserving the existing stored-scheme interpretation.

These restrictions describe this proved fragment, not language rejection
rules. General polymorphic heads can constrain a type's shape while leaving
weak components to the minimum-type solver; that connection is not implemented
here. Nor does this fragment discover an anchor or solve missing rows.
-/

namespace Yulang.EOFRoleInference

open Inference RoleConstraints QualifiedInference

structure TypeCodec (m : Model) where
  decode : m.Ty → Roles.Term
  encode : Roles.Term → m.Ty
  encode_decode : ∀ value, encode (decode value) = value
  decode_encode : ∀ term, decode (encode term) = term

theorem TypeCodec.decode_injective (codec : TypeCodec m) : Function.Injective codec.decode := by
  intro left right equal
  simpa only [codec.encode_decode] using congrArg codec.encode equal

mutual
  theorem closed_subst (term : Roles.Term) (closed : term.bound = 0) (subst : Roles.Subst) :
      term.subst subst = term := by
    cases term with
    | var name => simp [Roles.Term.bound] at closed
    | app name args =>
        exact congrArg (Roles.Term.app name) (closed_substArgs args closed subst)

  theorem closed_substArgs (args : List Roles.Term) (closed : Roles.argsBound args = 0)
      (subst : Roles.Subst) : Roles.substArgs subst args = args := by
    cases args with
    | nil => rfl
    | cons term rest =>
        have parts : term.bound = 0 ∧ Roles.argsBound rest = 0 := by
          simp only [Roles.argsBound] at closed
          omega
        simp only [Roles.substArgs, closed_subst term parts.1 subst,
          closed_substArgs rest parts.2 subst]
end

def GroundHeads (impls : List Roles.Impl) (role : Nat) : Prop :=
  ∀ implementation ∈ impls, implementation.role = role → Roles.argsBound implementation.head = 0

/-- An anchor can jointly constrain several weak types. Its order is the
ambient slot order, not a search order among impl declarations. -/
def anchor (k role : Nat) : Goal (Fin k) := ⟨role, List.ofFn TyTerm.var⟩

private def isSlot (expected : Fin k) : TyTerm (Fin k) → Bool
  | .var slot => decide (slot = expected)
  | _ => false

private theorem isSlot_exact (expected : Fin k) (type : TyTerm (Fin k)) :
    isSlot expected type = true ↔ type = .var expected := by
  cases type <;> simp [isSlot]

private def slotArguments : List (Fin k) → List (TyTerm (Fin k)) → Bool
  | [], [] => true
  | slot :: slots, type :: types => isSlot slot type && slotArguments slots types
  | _, _ => false

private theorem slotArguments_exact (slots : List (Fin k)) (types : List (TyTerm (Fin k))) :
    slotArguments slots types = true ↔ types = slots.map TyTerm.var := by
  induction slots generalizing types with
  | nil => cases types <;> simp [slotArguments]
  | cons slot slots ih => cases types <;> simp [slotArguments, isSlot_exact, ih]

def isAnchor (role : Nat) (goal : Goal (Fin k)) : Bool :=
  decide (goal.role = role) && slotArguments (List.finRange k) goal.args

theorem isAnchor_exact (role : Nat) (goal : Goal (Fin k)) :
    isAnchor role goal = true ↔ goal = anchor k role := by
  cases goal
  simp [isAnchor, slotArguments_exact, anchor, List.finRange, List.map_ofFn, Function.comp_def]

/-- A failed fragment check marks a case for the general solver; it is not a
language error and does not choose a default type for a polymorphic head. -/
def fragmentCheck (impls : List Roles.Impl) (role : Nat) (interface : Interface (Fin k) n) : Bool :=
  impls.all (fun implementation => decide (implementation.role = role → Roles.argsBound implementation.head = 0)) &&
    (pending interface.obligations).any (isAnchor role)

theorem fragmentCheck_exact (impls : List Roles.Impl) (role : Nat) (interface : Interface (Fin k) n) :
    fragmentCheck impls role interface = true ↔
      GroundHeads impls role ∧ anchor k role ∈ pending interface.obligations := by
  simp only [fragmentCheck, Bool.and_eq_true, List.all_eq_true, List.any_eq_true,
    decide_eq_true_eq, isAnchor_exact]
  constructor
  · rintro ⟨ground, goal, member, equal⟩
    exact ⟨ground, equal ▸ member⟩
  · rintro ⟨ground, anchored⟩
    exact ⟨ground, anchor k role, anchored, rfl⟩

def codes (codec : TypeCodec m) (assignment : Fin k → Comp m) : List Roles.Term :=
  List.ofFn (fun slot => codec.decode (assignment slot).1)

/-- The fallback is unreachable for every candidate: candidate construction
checks the head arity before this assignment is used. -/
def assignmentOf (codec : TypeCodec m) (rows : Fin k → m.Row)
    (types : List Roles.Term) : Fin k → Comp m :=
  fun slot => (codec.encode (types[slot.val]?.getD (.var 0)), rows slot)

theorem codes_length (codec : TypeCodec m) (assignment : Fin k → Comp m) :
    (codes codec assignment).length = k := by simp [codes]

theorem codes_assignmentOf (codec : TypeCodec m) (rows : Fin k → m.Row)
    (types : List Roles.Term) (arity : types.length = k) :
    codes codec (assignmentOf codec rows types) = types := by
  apply List.ext_getElem (by simpa only [codes_length] using arity.symm)
  intro index leftBound rightBound
  simp only [codes, List.getElem_ofFn, assignmentOf, List.getElem?_eq_getElem rightBound,
    Option.getD_some, codec.decode_encode]

theorem assignmentOf_codes (codec : TypeCodec m) (rows : Fin k → m.Row)
    (assignment : Fin k → Comp m) (fixedRows : ∀ slot, (assignment slot).2 = rows slot) :
    assignmentOf codec rows (codes codec assignment) = assignment := by
  funext slot
  apply Prod.ext
  · simp [assignmentOf, codes, codec.encode_decode]
  · exact (fixedRows slot).symm

theorem anchor_eval (codec : TypeCodec m) (assignment : Fin k → Comp m) (role : Nat) :
    (((anchor k role).eval m assignment).map codec.decode).toGoal =
      ⟨role, codes codec assignment⟩ := by
  simp [anchor, Goal.eval, Predicate.map, Predicate.toGoal, codes, TyTerm.eval, List.map_ofFn,
    Function.comp_def]

/-- Earlier type choices are retained; absent choices are the slots inferred
at EOF. Rows are supplied separately because this fragment does not solve them. -/
def compatible (codec : TypeCodec m) (known : Fin k → Option m.Ty)
    (assignment : Fin k → Comp m) : Bool :=
  (List.finRange k).all fun slot =>
    match known slot with
    | none => true
    | some expected => decide (codec.decode (assignment slot).1 = codec.decode expected)

theorem compatible_exact (codec : TypeCodec m) (known : Fin k → Option m.Ty)
    (assignment : Fin k → Comp m) :
    compatible codec known assignment = true ↔
      ∀ slot expected, known slot = some expected → (assignment slot).1 = expected := by
  simp only [compatible, List.all_eq_true, List.mem_finRange]
  constructor
  · intro checks slot expected present
    have checked := checks slot trivial
    rw [present, decide_eq_true_eq] at checked
    exact codec.decode_injective checked
  · intro agrees slot _
    cases present : known slot with
    | none => rfl
    | some expected => simp [agrees slot expected present]

def candidateTypes (impls : List Roles.Impl) (role k : Nat) : List (List Roles.Term) :=
  (impls.filter (fun implementation => decide (implementation.role = role ∧ implementation.head.length = k))).map
    Roles.Impl.head

theorem mem_candidateTypes (impls : List Roles.Impl) (role k : Nat) (types : List Roles.Term) :
    types ∈ candidateTypes impls role k ↔
      ∃ implementation ∈ impls, implementation.role = role ∧
        implementation.head.length = k ∧ implementation.head = types := by
  simp only [candidateTypes, List.mem_map, List.mem_filter, decide_eq_true_eq, and_assoc]

theorem candidate_arity (impls : List Roles.Impl) (role k : Nat) (types : List Roles.Term)
    (member : types ∈ candidateTypes impls role k) : types.length = k := by
  obtain ⟨implementation, _, _, arity, equal⟩ := (mem_candidateTypes impls role k types).mp member
  exact equal ▸ arity

/-- A completion has fixed rows, preserves previous type choices, passes the
ordinary-constraint check, and resolves every pending role in this database. -/
def Completion (codec : TypeCodec m) (impls : List Roles.Impl) (wf : Roles.WellFormed impls)
    (rows : Fin k → m.Row) (known : Fin k → Option m.Ty)
    (ordinary : (Fin k → Comp m) → Bool) (interface : Interface (Fin k) n)
    (assignment : Fin k → Comp m) : Prop :=
  (∀ slot, (assignment slot).2 = rows slot) ∧
    compatible codec known assignment = true ∧ ordinary assignment = true ∧
    pendingCheck m codec.decode impls wf assignment interface = true

def feasibleTypes (codec : TypeCodec m) (impls : List Roles.Impl) (wf : Roles.WellFormed impls)
    (role : Nat) (rows : Fin k → m.Row) (known : Fin k → Option m.Ty)
    (ordinary : (Fin k → Comp m) → Bool) (interface : Interface (Fin k) n) : List (List Roles.Term) :=
  (candidateTypes impls role k).filter fun types =>
    let assignment := assignmentOf codec rows types
    compatible codec known assignment && ordinary assignment &&
      pendingCheck m codec.decode impls wf assignment interface

theorem feasible_exact (codec : TypeCodec m) (impls : List Roles.Impl) (wf : Roles.WellFormed impls)
    (role : Nat) (rows : Fin k → m.Row) (known : Fin k → Option m.Ty)
    (ordinary : (Fin k → Comp m) → Bool) (interface : Interface (Fin k) n)
    (types : List Roles.Term) :
    types ∈ feasibleTypes codec impls wf role rows known ordinary interface ↔
      types ∈ candidateTypes impls role k ∧
      Completion codec impls wf rows known ordinary interface (assignmentOf codec rows types) := by
  simp [feasibleTypes, Completion, assignmentOf, and_assoc]

/-- Completeness of declaration-derived candidates. It ranges over arbitrary
semantic assignments, not assignments taken from a supplied finite universe. -/
theorem completion_is_candidate (codec : TypeCodec m) (impls : List Roles.Impl)
    (wf : Roles.WellFormed impls) (role : Nat) (ground : GroundHeads impls role)
    (rows : Fin k → m.Row) (known : Fin k → Option m.Ty)
    (ordinary : (Fin k → Comp m) → Bool) (interface : Interface (Fin k) n)
    (anchored : anchor k role ∈ pending interface.obligations) (assignment : Fin k → Comp m)
    (complete : Completion codec impls wf rows known ordinary interface assignment) :
    codes codec assignment ∈ candidateTypes impls role k := by
  have resolved := (List.all_eq_true.mp complete.2.2.2) (anchor k role) anchored
  simp only [decide_eq_true_eq, anchor_eval] at resolved
  have derives := Roles.resolve_sound impls wf _ resolved
  cases derives with
  | impl implementation subst member sameRole head children =>
      have closed := ground implementation member sameRole
      rw [closed_substArgs implementation.head closed subst] at head
      apply (mem_candidateTypes impls role k _).mpr
      exact ⟨implementation, member, sameRole, head ▸ codes_length codec assignment, head⟩

theorem completion_is_feasible (codec : TypeCodec m) (impls : List Roles.Impl)
    (wf : Roles.WellFormed impls) (role : Nat) (ground : GroundHeads impls role)
    (rows : Fin k → m.Row) (known : Fin k → Option m.Ty)
    (ordinary : (Fin k → Comp m) → Bool) (interface : Interface (Fin k) n)
    (anchored : anchor k role ∈ pending interface.obligations) (assignment : Fin k → Comp m)
    (complete : Completion codec impls wf rows known ordinary interface assignment) :
    codes codec assignment ∈ feasibleTypes codec impls wf role rows known ordinary interface := by
  apply (feasible_exact codec impls wf role rows known ordinary interface _).mpr
  exact ⟨completion_is_candidate codec impls wf role ground rows known ordinary interface anchored assignment complete,
    (assignmentOf_codes codec rows assignment complete.1).symm ▸ complete⟩

def infer (codec : TypeCodec m) (impls : List Roles.Impl) (wf : Roles.WellFormed impls)
    (role : Nat) (rows : Fin k → m.Row) (known : Fin k → Option m.Ty)
    (ordinary : (Fin k → Comp m) → Bool) (interface : Interface (Fin k) n) : Methods.Selection (List Roles.Term) :=
  Methods.select (feasibleTypes codec impls wf role rows known ordinary interface)

def UniqueCompletion (codec : TypeCodec m) (impls : List Roles.Impl) (wf : Roles.WellFormed impls)
    (rows : Fin k → m.Row) (known : Fin k → Option m.Ty)
    (ordinary : (Fin k → Comp m) → Bool) (interface : Interface (Fin k) n)
    (assignment : Fin k → Comp m) : Prop :=
  Completion codec impls wf rows known ordinary interface assignment ∧
    ∀ other, Completion codec impls wf rows known ordinary interface other → other = assignment

/-- The finite executable search is equivalent to uniqueness among all
assignments of the remaining weak types. No impl-count criterion is used. -/
theorem infer_unique_exact (codec : TypeCodec m) (impls : List Roles.Impl)
    (wf : Roles.WellFormed impls) (role : Nat) (ground : GroundHeads impls role)
    (rows : Fin k → m.Row) (known : Fin k → Option m.Ty)
    (ordinary : (Fin k → Comp m) → Bool) (interface : Interface (Fin k) n)
    (anchored : anchor k role ∈ pending interface.obligations) (types : List Roles.Term) :
    infer codec impls wf role rows known ordinary interface = .unique types ↔
      types.length = k ∧
        UniqueCompletion codec impls wf rows known ordinary interface (assignmentOf codec rows types) := by
  rw [infer, Methods.select_unique_iff]
  constructor
  · rintro ⟨member, unique⟩
    obtain ⟨candidate, complete⟩ := (feasible_exact codec impls wf role rows known ordinary interface types).mp member
    refine ⟨candidate_arity impls role k types candidate, complete, ?_⟩
    intro other otherComplete
    have equal := unique (codes codec other)
      (completion_is_feasible codec impls wf role ground rows known ordinary interface anchored other otherComplete)
    calc
      other = assignmentOf codec rows (codes codec other) :=
        (assignmentOf_codes codec rows other otherComplete.1).symm
      _ = assignmentOf codec rows types := congrArg (assignmentOf codec rows) equal
  · rintro ⟨arity, complete, unique⟩
    have member := completion_is_feasible codec impls wf role ground rows known ordinary interface anchored
      (assignmentOf codec rows types) complete
    rw [codes_assignmentOf codec rows types arity] at member
    refine ⟨member, ?_⟩
    intro other otherMember
    obtain ⟨otherCandidate, otherComplete⟩ :=
      (feasible_exact codec impls wf role rows known ordinary interface other).mp otherMember
    have equal := congrArg (codes codec) (unique (assignmentOf codec rows other) otherComplete)
    simpa only [codes_assignmentOf codec rows other (candidate_arity impls role k other otherCandidate),
      codes_assignmentOf codec rows types arity] using equal

theorem infer_missing_exact (codec : TypeCodec m) (impls : List Roles.Impl)
    (wf : Roles.WellFormed impls) (role : Nat) (ground : GroundHeads impls role)
    (rows : Fin k → m.Row) (known : Fin k → Option m.Ty)
    (ordinary : (Fin k → Comp m) → Bool) (interface : Interface (Fin k) n)
    (anchored : anchor k role ∈ pending interface.obligations) :
    infer codec impls wf role rows known ordinary interface = .missing ↔
      ¬ ∃ assignment, Completion codec impls wf rows known ordinary interface assignment := by
  rw [infer, Methods.select_missing_iff]
  constructor
  · rintro absent ⟨assignment, complete⟩
    exact absent (codes codec assignment)
      (completion_is_feasible codec impls wf role ground rows known ordinary interface anchored assignment complete)
  · intro absent types member
    exact absent ⟨assignmentOf codec rows types,
      ((feasible_exact codec impls wf role rows known ordinary interface types).mp member).2⟩

theorem infer_ambiguous_exact (codec : TypeCodec m) (impls : List Roles.Impl)
    (wf : Roles.WellFormed impls) (role : Nat) (ground : GroundHeads impls role)
    (rows : Fin k → m.Row) (known : Fin k → Option m.Ty)
    (ordinary : (Fin k → Comp m) → Bool) (interface : Interface (Fin k) n)
    (anchored : anchor k role ∈ pending interface.obligations) :
    infer codec impls wf role rows known ordinary interface = .ambiguous ↔
      ∃ first second, Completion codec impls wf rows known ordinary interface first ∧
        Completion codec impls wf rows known ordinary interface second ∧ first ≠ second := by
  rw [infer, Methods.select_ambiguous_iff]
  constructor
  · rintro ⟨first, firstMember, second, secondMember, unequal⟩
    obtain ⟨firstCandidate, firstComplete⟩ :=
      (feasible_exact codec impls wf role rows known ordinary interface first).mp firstMember
    obtain ⟨secondCandidate, secondComplete⟩ :=
      (feasible_exact codec impls wf role rows known ordinary interface second).mp secondMember
    refine ⟨assignmentOf codec rows first, assignmentOf codec rows second, firstComplete, secondComplete, ?_⟩
    intro equal
    apply unequal
    have sameCodes := congrArg (codes codec) equal
    simpa only [codes_assignmentOf codec rows first (candidate_arity impls role k first firstCandidate),
      codes_assignmentOf codec rows second (candidate_arity impls role k second secondCandidate)] using sameCodes
  · rintro ⟨first, second, firstComplete, secondComplete, unequal⟩
    refine ⟨codes codec first,
      completion_is_feasible codec impls wf role ground rows known ordinary interface anchored first firstComplete,
      codes codec second,
      completion_is_feasible codec impls wf role ground rows known ordinary interface anchored second secondComplete, ?_⟩
    intro equal
    apply unequal
    calc
      first = assignmentOf codec rows (codes codec first) := (assignmentOf_codes codec rows first firstComplete.1).symm
      _ = assignmentOf codec rows (codes codec second) := congrArg (assignmentOf codec rows) equal
      _ = second := assignmentOf_codes codec rows second secondComplete.1

structure Finished (m : Model) (k n : Nat) where
  assignment : Fin k → Comp m
  closed : ClosedInterface m n

def finalize (codec : TypeCodec m) (impls : List Roles.Impl) (wf : Roles.WellFormed impls)
    (role : Nat) (rows : Fin k → m.Row) (known : Fin k → Option m.Ty)
    (ordinary : (Fin k → Comp m) → Bool) (interface : Interface (Fin k) n) : Option (Finished m k n) :=
  match infer codec impls wf role rows known ordinary interface with
  | .unique types =>
      let assignment := assignmentOf codec rows types
      (finishModule m codec.decode impls wf (fun slot => some (assignment slot)) interface).map
        (fun closed => ⟨assignment, closed⟩)
  | .missing | .ambiguous => none

theorem finishModule_total (m : Model) (decode : m.Ty → Roles.Term) (impls : List Roles.Impl)
    (wf : Roles.WellFormed impls) (assignment : α → Comp m) (interface : Interface α n) :
    finishModule m decode impls wf (fun slot => some (assignment slot)) interface =
      if pendingCheck m decode impls wf assignment interface then some (interface.closeAt m assignment) else none := by
  have completed : completeAssignment m (fun slot => some (assignment slot)) = assignment := rfl
  simp [finishModule, Interface.known, completed]

theorem completion_finishes (codec : TypeCodec m) (impls : List Roles.Impl) (wf : Roles.WellFormed impls)
    (rows : Fin k → m.Row) (known : Fin k → Option m.Ty)
    (ordinary : (Fin k → Comp m) → Bool) (interface : Interface (Fin k) n)
    (assignment : Fin k → Comp m)
    (complete : Completion codec impls wf rows known ordinary interface assignment) :
    finishModule m codec.decode impls wf (fun slot => some (assignment slot)) interface =
      some (interface.closeAt m assignment) := by
  rw [finishModule_total, complete.2.2.2]
  rfl

theorem finalize_unique (codec : TypeCodec m) (impls : List Roles.Impl) (wf : Roles.WellFormed impls)
    (role : Nat) (rows : Fin k → m.Row) (known : Fin k → Option m.Ty)
    (ordinary : (Fin k → Comp m) → Bool) (interface : Interface (Fin k) n) (types : List Roles.Term)
    (selected : infer codec impls wf role rows known ordinary interface = .unique types) :
    finalize codec impls wf role rows known ordinary interface =
      some ⟨assignmentOf codec rows types, interface.closeAt m (assignmentOf codec rows types)⟩ := by
  obtain ⟨member, _⟩ := (Methods.select_unique_iff _ types).mp selected
  have complete := ((feasible_exact codec impls wf role rows known ordinary interface types).mp member).2
  simp only [finalize, selected,
    completion_finishes codec impls wf rows known ordinary interface (assignmentOf codec rows types) complete,
    Option.map_some]

theorem finalize_sound (codec : TypeCodec m) (impls : List Roles.Impl)
    (wf : Roles.WellFormed impls) (role : Nat) (ground : GroundHeads impls role)
    (rows : Fin k → m.Row) (known : Fin k → Option m.Ty)
    (ordinary : (Fin k → Comp m) → Bool) (interface : Interface (Fin k) n)
    (anchored : anchor k role ∈ pending interface.obligations) (finished : Finished m k n)
    (accepted : finalize codec impls wf role rows known ordinary interface = some finished) :
    UniqueCompletion codec impls wf rows known ordinary interface finished.assignment ∧
      finishModule m codec.decode impls wf (fun slot => some (finished.assignment slot)) interface =
        some finished.closed := by
  cases selected : infer codec impls wf role rows known ordinary interface with
  | missing => simp [finalize, selected] at accepted
  | ambiguous => simp [finalize, selected] at accepted
  | unique types =>
      rw [finalize_unique codec impls wf role rows known ordinary interface types selected] at accepted
      have equal := Option.some.inj accepted
      subst finished
      have unique := ((infer_unique_exact codec impls wf role ground rows known ordinary interface anchored types).mp selected).2
      exact ⟨unique, completion_finishes codec impls wf rows known ordinary interface _ unique.1⟩

theorem finalize_complete (codec : TypeCodec m) (impls : List Roles.Impl)
    (wf : Roles.WellFormed impls) (role : Nat) (ground : GroundHeads impls role)
    (rows : Fin k → m.Row) (known : Fin k → Option m.Ty)
    (ordinary : (Fin k → Comp m) → Bool) (interface : Interface (Fin k) n)
    (anchored : anchor k role ∈ pending interface.obligations) (assignment : Fin k → Comp m)
    (unique : UniqueCompletion codec impls wf rows known ordinary interface assignment) :
    finalize codec impls wf role rows known ordinary interface =
      some ⟨assignment, interface.closeAt m assignment⟩ := by
  have recovers := assignmentOf_codes codec rows assignment unique.1.1
  have selected : infer codec impls wf role rows known ordinary interface = .unique (codes codec assignment) := by
    apply (infer_unique_exact codec impls wf role ground rows known ordinary interface anchored _).mpr
    exact ⟨codes_length codec assignment, recovers.symm ▸ unique⟩
  rw [finalize_unique codec impls wf role rows known ordinary interface _ selected, recovers]

theorem finalize_exact (codec : TypeCodec m) (impls : List Roles.Impl)
    (wf : Roles.WellFormed impls) (role : Nat) (ground : GroundHeads impls role)
    (rows : Fin k → m.Row) (known : Fin k → Option m.Ty)
    (ordinary : (Fin k → Comp m) → Bool) (interface : Interface (Fin k) n)
    (anchored : anchor k role ∈ pending interface.obligations) (assignment : Fin k → Comp m) :
    finalize codec impls wf role rows known ordinary interface = some ⟨assignment, interface.closeAt m assignment⟩ ↔
      UniqueCompletion codec impls wf rows known ordinary interface assignment :=
  ⟨fun accepted => (finalize_sound codec impls wf role ground rows known ordinary interface anchored _ accepted).1,
    finalize_complete codec impls wf role ground rows known ordinary interface anchored assignment⟩

/-- The inferred type choices extend the partial type assignment available
before EOF. They never turn a weak slot into a generalized parameter. -/
theorem finalize_preserves_known (codec : TypeCodec m) (impls : List Roles.Impl)
    (wf : Roles.WellFormed impls) (role : Nat) (ground : GroundHeads impls role)
    (rows : Fin k → m.Row) (known : Fin k → Option m.Ty)
    (ordinary : (Fin k → Comp m) → Bool) (interface : Interface (Fin k) n)
    (anchored : anchor k role ∈ pending interface.obligations) (finished : Finished m k n)
    (accepted : finalize codec impls wf role rows known ordinary interface = some finished) :
    ∀ slot value, known slot = some value → finished.assignment slot = (value, rows slot) := by
  have complete := (finalize_sound codec impls wf role ground rows known ordinary interface anchored finished accepted).1.1
  intro slot value present
  exact Prod.ext ((compatible_exact codec known finished.assignment).mp complete.2.1 slot value present)
    (complete.1 slot)

theorem finalized_scheme_exact (codec : TypeCodec m) (impls : List Roles.Impl)
    (wf : Roles.WellFormed impls) (role : Nat) (ground : GroundHeads impls role)
    (rows : Fin k → m.Row) (known : Fin k → Option m.Ty)
    (ordinary : (Fin k → Comp m) → Bool) (interface : Interface (Fin k) n)
    (anchored : anchor k role ∈ pending interface.obligations) (finished : Finished m k n)
    (accepted : finalize codec impls wf role rows known ordinary interface = some finished)
    (theory : Theory m) (output : Comp m) :
    interface.scheme.Holds m theory (extend finished.assignment output) ↔
      BindingTyping m theory
        (.qualified n finished.closed.requirements (fun locals => Comp.pure m (finished.closed.value locals))) output := by
  have closed := (finalize_sound codec impls wf role ground rows known ordinary interface anchored finished accepted).2
  exact QualifiedInference.finalized_scheme_exact m codec.decode impls wf
    (fun slot => some (finished.assignment slot)) interface finished.closed closed theory finished.assignment
    (fun _ _ equal => Option.some.inj equal) output

inductive Attempt (m : Model) (k n : Nat) where
  | outsideFragment
  | noCompletion
  | multipleCompletions
  | finished : Finished m k n → Attempt m k n

/-- The checked public entry point never applies the finite ground-head search
to a polymorphic head or to an interface without the required anchor. -/
def checkedFinalize (codec : TypeCodec m) (impls : List Roles.Impl) (wf : Roles.WellFormed impls)
    (role : Nat) (rows : Fin k → m.Row) (known : Fin k → Option m.Ty)
    (ordinary : (Fin k → Comp m) → Bool) (interface : Interface (Fin k) n) : Attempt m k n :=
  if fragmentCheck impls role interface then
    match infer codec impls wf role rows known ordinary interface with
    | .missing => .noCompletion
    | .ambiguous => .multipleCompletions
    | .unique _ =>
        match finalize codec impls wf role rows known ordinary interface with
        | some finished => .finished finished
        | none => .noCompletion
  else .outsideFragment

theorem checkedFinalize_finished_exact (codec : TypeCodec m) (impls : List Roles.Impl)
    (wf : Roles.WellFormed impls) (role : Nat) (rows : Fin k → m.Row) (known : Fin k → Option m.Ty)
    (ordinary : (Fin k → Comp m) → Bool) (interface : Interface (Fin k) n) (finished : Finished m k n) :
    checkedFinalize codec impls wf role rows known ordinary interface = .finished finished ↔
      fragmentCheck impls role interface = true ∧
        finalize codec impls wf role rows known ordinary interface = some finished := by
  cases checked : fragmentCheck impls role interface with
  | false => simp [checkedFinalize, checked]
  | true =>
      cases selected : infer codec impls wf role rows known ordinary interface with
      | missing => simp [checkedFinalize, checked, selected, finalize]
      | ambiguous => simp [checkedFinalize, checked, selected, finalize]
      | unique types =>
          rw [checkedFinalize, ite_eq_left checked, selected,
            finalize_unique codec impls wf role rows known ordinary interface types selected]
          simp

theorem checkedFinalize_sound (codec : TypeCodec m) (impls : List Roles.Impl)
    (wf : Roles.WellFormed impls) (role : Nat) (rows : Fin k → m.Row) (known : Fin k → Option m.Ty)
    (ordinary : (Fin k → Comp m) → Bool) (interface : Interface (Fin k) n) (finished : Finished m k n)
    (accepted : checkedFinalize codec impls wf role rows known ordinary interface = .finished finished) :
    UniqueCompletion codec impls wf rows known ordinary interface finished.assignment ∧
      finishModule m codec.decode impls wf (fun slot => some (finished.assignment slot)) interface = some finished.closed := by
  obtain ⟨checked, finalized⟩ := (checkedFinalize_finished_exact codec impls wf role rows known ordinary interface finished).mp accepted
  obtain ⟨ground, anchored⟩ := (fragmentCheck_exact impls role interface).mp checked
  exact finalize_sound codec impls wf role ground rows known ordinary interface anchored finished finalized

theorem checkedFinalize_complete (codec : TypeCodec m) (impls : List Roles.Impl)
    (wf : Roles.WellFormed impls) (role : Nat) (ground : GroundHeads impls role)
    (rows : Fin k → m.Row) (known : Fin k → Option m.Ty)
    (ordinary : (Fin k → Comp m) → Bool) (interface : Interface (Fin k) n)
    (anchored : anchor k role ∈ pending interface.obligations) (assignment : Fin k → Comp m)
    (unique : UniqueCompletion codec impls wf rows known ordinary interface assignment) :
    checkedFinalize codec impls wf role rows known ordinary interface =
      .finished ⟨assignment, interface.closeAt m assignment⟩ := by
  apply (checkedFinalize_finished_exact codec impls wf role rows known ordinary interface _).mpr
  exact ⟨(fragmentCheck_exact impls role interface).mpr ⟨ground, anchored⟩,
    finalize_complete codec impls wf role ground rows known ordinary interface anchored assignment unique⟩

theorem infer_congr (codec : TypeCodec m) {left right : List Roles.Impl}
    (same : ∀ implementation, implementation ∈ left ↔ implementation ∈ right)
    (leftWF : Roles.WellFormed left) (rightWF : Roles.WellFormed right)
    (role : Nat) (rows : Fin k → m.Row) (known : Fin k → Option m.Ty)
    (ordinary : (Fin k → Comp m) → Bool) (interface : Interface (Fin k) n) :
    infer codec left leftWF role rows known ordinary interface =
      infer codec right rightWF role rows known ordinary interface := by
  apply Methods.select_ext
  intro types
  simp only [feasible_exact, Completion]
  rw [ModuleVisibility.pendingCheck_congr m codec.decode same leftWF rightWF]
  have candidates : types ∈ candidateTypes left role k ↔ types ∈ candidateTypes right role k := by
    simp only [mem_candidateTypes]
    constructor
    · rintro ⟨implementation, member, properties⟩
      exact ⟨implementation, (same implementation).mp member, properties⟩
    · rintro ⟨implementation, member, properties⟩
      exact ⟨implementation, (same implementation).mpr member, properties⟩
  rw [candidates]

theorem finalize_congr (codec : TypeCodec m) {left right : List Roles.Impl}
    (same : ∀ implementation, implementation ∈ left ↔ implementation ∈ right)
    (leftWF : Roles.WellFormed left) (rightWF : Roles.WellFormed right)
    (role : Nat) (rows : Fin k → m.Row) (known : Fin k → Option m.Ty)
    (ordinary : (Fin k → Comp m) → Bool) (interface : Interface (Fin k) n) :
    finalize codec left leftWF role rows known ordinary interface =
      finalize codec right rightWF role rows known ordinary interface := by
  unfold finalize
  rw [infer_congr codec same leftWF rightWF]
  cases selected : infer codec right rightWF role rows known ordinary interface with
  | missing | ambiguous => rfl
  | unique types =>
      dsimp only
      rw [finishModule_total, finishModule_total,
        ModuleVisibility.pendingCheck_congr m codec.decode same leftWF rightWF]

theorem fragmentCheck_congr {left right : List Roles.Impl}
    (same : ∀ implementation, implementation ∈ left ↔ implementation ∈ right)
    (role : Nat) (interface : Interface (Fin k) n) :
    fragmentCheck left role interface = fragmentCheck right role interface := by
  apply Bool.eq_iff_iff.mpr
  rw [fragmentCheck_exact, fragmentCheck_exact]
  have ground : GroundHeads left role ↔ GroundHeads right role := by
    exact ⟨fun leftGround implementation member => leftGround implementation ((same implementation).mpr member),
      fun rightGround implementation member => rightGround implementation ((same implementation).mp member)⟩
  rw [ground]

theorem checkedFinalize_congr (codec : TypeCodec m) {left right : List Roles.Impl}
    (same : ∀ implementation, implementation ∈ left ↔ implementation ∈ right)
    (leftWF : Roles.WellFormed left) (rightWF : Roles.WellFormed right)
    (role : Nat) (rows : Fin k → m.Row) (known : Fin k → Option m.Ty)
    (ordinary : (Fin k → Comp m) → Bool) (interface : Interface (Fin k) n) :
    checkedFinalize codec left leftWF role rows known ordinary interface =
      checkedFinalize codec right rightWF role rows known ordinary interface := by
  unfold checkedFinalize
  rw [fragmentCheck_congr same, infer_congr codec same leftWF rightWF, finalize_congr codec same leftWF rightWF]

def finishFile [DecidableEq File] (codec : TypeCodec m) (scope : ModuleVisibility.FileScope File)
    (catalog : List (ModuleVisibility.Declaration File)) (wf : Roles.WellFormed (scope.select catalog))
    (role : Nat) (rows : Fin k → m.Row) (known : Fin k → Option m.Ty)
    (ordinary : (Fin k → Comp m) → Bool) (interface : Interface (Fin k) n) : Attempt m k n :=
  checkedFinalize codec (scope.select catalog) wf role rows known ordinary interface

/-- Hidden declarations, visible declaration order, and duplicate imports cannot
affect the inferred assignment or the actual finalized interface. -/
theorem finishFile_congr [DecidableEq File] (codec : TypeCodec m) (scope : ModuleVisibility.FileScope File)
    {left right : List (ModuleVisibility.Declaration File)} (same : ModuleVisibility.SameVisible scope left right)
    (leftWF : Roles.WellFormed (scope.select left)) (rightWF : Roles.WellFormed (scope.select right))
    (role : Nat) (rows : Fin k → m.Row) (known : Fin k → Option m.Ty)
    (ordinary : (Fin k → Comp m) → Bool) (interface : Interface (Fin k) n) :
    finishFile codec scope left leftWF role rows known ordinary interface =
      finishFile codec scope right rightWF role rows known ordinary interface :=
  checkedFinalize_congr codec (ModuleVisibility.selected_membership_congr scope same) leftWF rightWF
    role rows known ordinary interface

namespace Examples

open QualifiedExamples

def codec : TypeCodec model := ⟨id, id, fun _ => rfl, fun _ => rfl⟩
def rows : Fin 1 → model.Row := fun _ => ()
def unknown : Fin 1 → Option model.Ty := fun _ => none
def ordinary : (Fin 1 → Comp model) → Bool := fun _ => true

def weakInterface : Interface (Fin 1) 0 where
  value := .var (.inl 0)
  obligations := [⟨0, [.var (.inl 0)]⟩]

private theorem pending_single (impls : List Roles.Impl) (wf : Roles.WellFormed impls) (type : Roles.Term) :
    pendingCheck model codec.decode impls wf (assignmentOf codec rows [type]) weakInterface =
      decide (Roles.resolve impls wf ⟨0, [type]⟩ = .resolved) := by
  change (decide (Roles.resolve impls wf ⟨0, [type]⟩ = .resolved) && true) = _
  simp

theorem integer_resolved : Roles.resolve [addIntImpl] addInt_wf ⟨0, [Roles.Term.app 0 []]⟩ = .resolved := by
  rw [Roles.resolve_one _ _ _ addIntImpl (by decide)]
  rfl

theorem infer_unknown_integer :
    infer codec [addIntImpl] addInt_wf 0 rows unknown ordinary weakInterface = .unique [Roles.Term.app 0 []] := by
  change Methods.select (bif pendingCheck model codec.decode [addIntImpl] addInt_wf
    (assignmentOf codec rows [Roles.Term.app 0 []]) weakInterface then [[Roles.Term.app 0 []]] else []) = _
  rw [pending_single, integer_resolved]
  rfl

theorem eof_infers_and_finishes_integer :
    checkedFinalize codec [addIntImpl] addInt_wf 0 rows unknown ordinary weakInterface =
      .finished ⟨assignmentOf codec rows [Roles.Term.app 0 []],
        weakInterface.closeAt model (assignmentOf codec rows [Roles.Term.app 0 []])⟩ := by
  apply (checkedFinalize_finished_exact codec [addIntImpl] addInt_wf 0 rows unknown ordinary weakInterface _).mpr
  exact ⟨rfl, finalize_unique codec [addIntImpl] addInt_wf 0 rows unknown ordinary weakInterface _ infer_unknown_integer⟩

theorem inferred_integer_is_exported :
    (weakInterface.closeAt model (assignmentOf codec rows [Roles.Term.app 0 []])).value Fin.elim0 = Roles.Term.app 0 [] := rfl

theorem unknown_without_any_visible_impl :
    checkedFinalize codec [] empty_impls_wellFormed 0 rows unknown ordinary weakInterface = .noCompletion := rfl

theorem known_string_is_not_overwritten :
    checkedFinalize codec [addIntImpl] addInt_wf 0 rows (fun _ => some (Roles.Term.app 1 [])) ordinary weakInterface =
      .noCompletion := rfl

theorem ordinary_constraint_is_not_ignored :
    checkedFinalize codec [addIntImpl] addInt_wf 0 rows unknown (fun _ => false) weakInterface = .noCompletion := rfl

theorem duplicateWF : Roles.WellFormed [addIntImpl, addIntImpl] := by
  intro implementation member
  apply addInt_wf implementation
  simpa using member

theorem duplicate_import_does_not_create_type_ambiguity :
    infer codec [addIntImpl, addIntImpl] duplicateWF
      0 rows unknown ordinary weakInterface = .unique [Roles.Term.app 0 []] := by
  rw [infer_congr codec (right := [addIntImpl]) (fun _ => by simp) _ addInt_wf]
  exact infer_unknown_integer

def addStringImpl : Roles.Impl := ⟨0, [Roles.Term.app 1 []], [], 21⟩

theorem twoTypesWF : Roles.WellFormed [addIntImpl, addStringImpl] := by
  simp [Roles.WellFormed, Roles.Impl.WellFormed, addIntImpl, addStringImpl]

theorem two_types_are_not_defaulted :
    checkedFinalize codec [addIntImpl, addStringImpl] twoTypesWF 0 rows unknown ordinary weakInterface =
      .multipleCompletions := by
  have integer : Roles.resolve [addIntImpl, addStringImpl] twoTypesWF ⟨0, [Roles.Term.app 0 []]⟩ = .resolved := by
    rw [Roles.resolve_one _ _ _ addIntImpl (by decide)]
    rfl
  have string : Roles.resolve [addIntImpl, addStringImpl] twoTypesWF ⟨0, [Roles.Term.app 1 []]⟩ = .resolved := by
    rw [Roles.resolve_one _ _ _ addStringImpl (by decide)]
    rfl
  have selected : infer codec [addIntImpl, addStringImpl] twoTypesWF 0 rows unknown ordinary weakInterface = .ambiguous := by
    change Methods.select (bif pendingCheck model codec.decode _ twoTypesWF (assignmentOf codec rows [Roles.Term.app 0 []]) weakInterface
      then [Roles.Term.app 0 []] :: (bif pendingCheck model codec.decode _ twoTypesWF (assignmentOf codec rows [Roles.Term.app 1 []]) weakInterface
        then [[Roles.Term.app 1 []]] else [])
      else bif pendingCheck model codec.decode _ twoTypesWF (assignmentOf codec rows [Roles.Term.app 1 []]) weakInterface
        then [[Roles.Term.app 1 []]] else []) = _
    simp only [pending_single, integer, string]
    rfl
  change (if true then _ else _) = _
  simp [selected]

def anotherIntegerImpl : Roles.Impl := ⟨0, [Roles.Term.app 0 []], [], 22⟩

theorem overlapWF : Roles.WellFormed [addIntImpl, anotherIntegerImpl] := by
  simp [Roles.WellFormed, Roles.Impl.WellFormed, addIntImpl, anotherIntegerImpl]

/-- One candidate type does not make two distinct dictionaries coherent. -/
theorem one_type_with_two_impls_is_not_accepted :
    checkedFinalize codec [addIntImpl, anotherIntegerImpl] overlapWF 0 rows unknown ordinary weakInterface =
      .noCompletion := by
  have overlapping : Roles.resolve [addIntImpl, anotherIntegerImpl] overlapWF ⟨0, [Roles.Term.app 0 []]⟩ = .ambiguous :=
    Roles.resolve_many _ _ _ addIntImpl anotherIntegerImpl [] (by decide)
  have selected : infer codec [addIntImpl, anotherIntegerImpl] overlapWF 0 rows unknown ordinary weakInterface = .missing := by
    change Methods.select (bif pendingCheck model codec.decode _ overlapWF (assignmentOf codec rows [Roles.Term.app 0 []]) weakInterface
      then [Roles.Term.app 0 []] :: (bif pendingCheck model codec.decode _ overlapWF (assignmentOf codec rows [Roles.Term.app 0 []]) weakInterface
        then [[Roles.Term.app 0 []]] else [])
      else bif pendingCheck model codec.decode _ overlapWF (assignmentOf codec rows [Roles.Term.app 0 []]) weakInterface
        then [[Roles.Term.app 0 []]] else []) = _
    simp only [pending_single, overlapping]
    rfl
  change (if true then _ else _) = _
  simp [selected]

/-- The general solver may still determine the shape `list ?a`; this checked
fragment reports `outsideFragment`, without treating the impl's parameter as a rigid result. -/
theorem polymorphic_head_is_outside_this_fragment :
    checkedFinalize codec Roles.Examples.goodImpls Roles.Examples.goodImpls_wellFormed
      0 rows unknown ordinary weakInterface = .outsideFragment := rfl

theorem other_roles_may_have_polymorphic_heads :
    fragmentCheck [addIntImpl, ⟨1, [.var 0], [], 24⟩] 0 weakInterface = true := rfl

def unanchoredInterface : Interface (Fin 1) 0 where
  value := .var (.inl 0)
  obligations := [⟨0, [.base .int]⟩]

theorem unanchored_weak_slot_is_not_defaulted :
    checkedFinalize codec [addIntImpl] addInt_wf 0 rows unknown ordinary unanchoredInterface = .outsideFragment := rfl

def twoSlotInterface : Interface (Fin 2) 0 where
  value := .pair (.var (.inl 0)) (.var (.inl 1))
  obligations := [⟨2, [.var (.inl 0), .var (.inl 1)]⟩]

def tupleImpl : Roles.Impl := ⟨2, [Roles.Term.app 0 [], Roles.Term.app 1 []], [], 23⟩

theorem tupleWF : Roles.WellFormed [tupleImpl] := by
  simp [Roles.WellFormed, Roles.Impl.WellFormed, tupleImpl]

theorem jointly_infers_two_weak_types :
    checkedFinalize codec [tupleImpl] tupleWF 2 (fun _ : Fin 2 => ()) (fun _ => none) (fun _ => true) twoSlotInterface =
      .finished ⟨assignmentOf codec (fun _ : Fin 2 => ()) [Roles.Term.app 0 [], Roles.Term.app 1 []],
        twoSlotInterface.closeAt model (assignmentOf codec (fun _ : Fin 2 => ()) [Roles.Term.app 0 [], Roles.Term.app 1 []])⟩ := by
  have resolved : Roles.resolve [tupleImpl] tupleWF ⟨2, [Roles.Term.app 0 [], Roles.Term.app 1 []]⟩ = .resolved := by
    rw [Roles.resolve_one _ _ _ tupleImpl (by decide)]
    rfl
  have checked : pendingCheck model codec.decode [tupleImpl] tupleWF
      (assignmentOf codec (fun _ : Fin 2 => ()) [Roles.Term.app 0 [], Roles.Term.app 1 []]) twoSlotInterface = true := by
    change (decide (Roles.resolve [tupleImpl] tupleWF ⟨2, [Roles.Term.app 0 [], Roles.Term.app 1 []]⟩ = .resolved) && true) = true
    rw [resolved]
    rfl
  have selected : infer codec [tupleImpl] tupleWF 2 (fun _ : Fin 2 => ()) (fun _ => none) (fun _ => true) twoSlotInterface =
      .unique [Roles.Term.app 0 [], Roles.Term.app 1 []] := by
    change Methods.select (bif pendingCheck model codec.decode [tupleImpl] tupleWF
      (assignmentOf codec (fun _ : Fin 2 => ()) [Roles.Term.app 0 [], Roles.Term.app 1 []]) twoSlotInterface then [[Roles.Term.app 0 [], Roles.Term.app 1 []]] else []) = _
    rw [checked]
    rfl
  apply (checkedFinalize_finished_exact codec [tupleImpl] tupleWF 2 _ _ _ twoSlotInterface _).mpr
  exact ⟨rfl, finalize_unique codec [tupleImpl] tupleWF 2 _ _ _ twoSlotInterface _ selected⟩

def fileCatalog : List (ModuleVisibility.Declaration Nat) := [⟨0, addIntImpl⟩]

theorem ownFileWF : Roles.WellFormed ((ModuleVisibility.Examples.scope 0 []).select fileCatalog) := addInt_wf
theorem otherFileWF : Roles.WellFormed ((ModuleVisibility.Examples.scope 1 []).select fileCatalog) := empty_impls_wellFormed
theorem loadedFileWF : Roles.WellFormed ((ModuleVisibility.Examples.scope 1 [0]).select fileCatalog) := addInt_wf

theorem eof_own_file_infers_integer :
    finishFile codec (ModuleVisibility.Examples.scope 0 []) fileCatalog ownFileWF 0 rows unknown ordinary weakInterface =
      .finished ⟨assignmentOf codec rows [Roles.Term.app 0 []], weakInterface.closeAt model (assignmentOf codec rows [Roles.Term.app 0 []])⟩ :=
  eof_infers_and_finishes_integer

theorem eof_other_file_cannot_use_hidden_integer :
    finishFile codec (ModuleVisibility.Examples.scope 1 []) fileCatalog otherFileWF
      0 rows unknown ordinary weakInterface = .noCompletion := rfl

theorem eof_loaded_file_infers_integer :
    finishFile codec (ModuleVisibility.Examples.scope 1 [0]) fileCatalog loadedFileWF 0 rows unknown ordinary weakInterface =
      .finished ⟨assignmentOf codec rows [Roles.Term.app 0 []], weakInterface.closeAt model (assignmentOf codec rows [Roles.Term.app 0 []])⟩ :=
  eof_infers_and_finishes_integer

end Examples

end Yulang.EOFRoleInference
