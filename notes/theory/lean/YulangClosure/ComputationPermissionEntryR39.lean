import Std

/-!
R39 finite constructor model. Keys denote complete branded source identities,
never spellings or unbranded ordinals. Every table and row is a finite list.
The model covers the owner-local FormalEntry validation, exact copied record,
existing symbolic equality links and successful publication. It does not model
allocation, constraint propagation, provider arrival, Catch or subtraction.
The supplied action is the actual source action payload; no duplicate source
annotation table is invented. Correspondence with Rust requires separate review.
-/
namespace YulangClosure.ComputationPermissionEntryR39

inductive Role where
  | value | computation
  deriving DecidableEq

structure Row (Id : Type) where
  position : Id
  concrete : List Id
  variables : List Id
  deriving DecidableEq

structure Annotation (Id : Type) where
  owner : Id
  position : Id
  row : Option (Row Id)
  deriving DecidableEq

structure Registration (Id : Type) where
  owner : Id
  lambda : Nat
  parameter : Id
  recipe : Nat
  scope : Id
  role : Role
  entry : Option Id
  deriving DecidableEq

structure Action (Id : Type) where
  registration : Nat
  annotation : Annotation Id
  occurrence : Id
  scope : Id
  deriving DecidableEq

inductive SourceExpr (Id : Type) where
  | lambda (occurrence parameter : Id)
  | other (occurrence : Id)
  deriving DecidableEq

structure Inputs (Id : Type) where
  formals : List (Registration Id)
  recipes : List Id
  /-- Execution schedule, retained only to exhibit the rejected old guard. -/
  schedules : List Id
  /-- Authentic LocalSource expressions keyed by exact source owner. -/
  sources : List (Id × List (SourceExpr Id))
  owners : List (Id × Id)
  occupiedDomains : List Nat
  retainedRegistrations : List Nat

structure Permission (Id : Type) where
  registration : Nat
  parameter : Nat
  formalIdentity : Id
  occurrence : Id
  owner : Id
  scope : Id
  annotationPosition : Id
  rowPosition : Id
  entry : Id
  concrete : List Id
  deriving DecidableEq

variable {Id : Type} [DecidableEq Id]

def ownerLookup : List (Id × Id) → Id → Option Id
  | [], _ => none
  | (occurrence, owner) :: rest, key =>
      if occurrence = key then some owner else ownerLookup rest key

def localSource : List (Id × List (SourceExpr Id)) → Id → Option (List (SourceExpr Id))
  | [], _ => none
  | (owner, expressions) :: rest, key =>
      if owner = key then some expressions else localSource rest key

/-- Registration.lambda indexes this owner's LocalSource, never the execution
schedule. The returned formal is derived only from a Lambda constructor. -/
def sourceLambda (e : Inputs Id) (f : Registration Id) : Option (Id × Id) := do
  let expressions ← localSource e.sources f.owner
  let expression ← expressions[f.lambda]?
  match expression with
  | .lambda occurrence parameter => some (occurrence, parameter)
  | .other _ => none

theorem source_lambda_exact (e : Inputs Id) (f : Registration Id) (occurrence parameter : Id) :
    sourceLambda e f = some (occurrence, parameter) ↔
      ∃ expressions, localSource e.sources f.owner = some expressions ∧
        expressions[f.lambda]? = some (.lambda occurrence parameter) := by
  cases hs : localSource e.sources f.owner with
  | none => simp [sourceLambda, hs]
  | some expressions =>
    cases he : expressions[f.lambda]? with
    | none => simp [sourceLambda, hs, he]
    | some expression =>
      cases expression with
      | other other => simp [sourceLambda, hs, he]
      | lambda actual formal => simp [sourceLambda, hs, he]

/-- Historical invalid guard, used only for the correction counterexample. -/
def legacyScheduleGuard (e : Inputs Id) (f : Registration Id) (a : Action Id) : Bool :=
  decide (e.schedules[f.lambda]? = some a.occurrence)

/-- Exactly the source-owner and formal checks; no producer law is assumed. -/
def Valid (e : Inputs Id) (a : Action Id) (f : Registration Id) (r : Row Id) : Prop :=
  f.owner = a.annotation.owner ∧ f.role = .computation ∧ f.scope = a.scope ∧
  e.recipes[f.recipe]? = some f.parameter ∧
  ownerLookup e.owners a.occurrence = some f.owner ∧
  sourceLambda e f = some (a.occurrence, f.parameter) ∧
  f.recipe ∉ e.occupiedDomains ∧ a.registration ∉ e.retainedRegistrations ∧
  r.variables.length ≤ 1

instance (e : Inputs Id) (a : Action Id) (f : Registration Id) (r : Row Id) :
    Decidable (Valid e a f r) := inferInstanceAs (Decidable (_ ∧ _))

/-- The whole concrete vector is copied, without set conversion or filtering. -/
def build (a : Action Id) (f : Registration Id) (r : Row Id) (port : Id) : Permission Id :=
  ⟨a.registration, f.recipe, f.parameter, a.occurrence, a.annotation.owner, a.scope,
    a.annotation.position, r.position, port, r.concrete⟩

def prepare (e : Inputs Id) (a : Action Id) : Option (Registration Id × Row Id × Id) := do
  let f ← e.formals[a.registration]?
  let r ← a.annotation.row
  let port ← f.entry
  if Valid e a f r then some (f, r, port) else none

theorem prepare_exact (e : Inputs Id) (a : Action Id)
    (f : Registration Id) (r : Row Id) (port : Id) :
    prepare e a = some (f, r, port) ↔
      e.formals[a.registration]? = some f ∧ a.annotation.row = some r ∧
      f.entry = some port ∧ Valid e a f r := by
  constructor
  · intro success
    cases hf : e.formals[a.registration]? with
    | none => simp [prepare, hf] at success
    | some found =>
      cases hr : a.annotation.row with
      | none => simp [prepare, hf, hr] at success
      | some row =>
        cases hp : found.entry with
        | none => simp [prepare, hf, hr, hp] at success
        | some entry =>
          by_cases valid : Valid e a found row
          · have equal : found = f ∧ row = r ∧ entry = port := by
              simpa [prepare, hf, hr, hp, valid] using success
            rcases equal with ⟨rfl, rfl, rfl⟩
            exact ⟨rfl, rfl, hp, valid⟩
          · simp [prepare, hf, hr, hp, valid] at success
  · rintro ⟨hf, hr, hp, valid⟩
    simp [prepare, hf, hr, hp, valid]

/-- Empty/variable-only annotations remain admitted without creating permission. -/
def permissionFor (a : Action Id) (f : Registration Id) (r : Row Id) (port : Id) :
    Option (Permission Id) :=
  if r.concrete = [] then none else some (build a f r port)

theorem exact_row_retained (e : Inputs Id) (a : Action Id) (p : Permission Id)
    (f : Registration Id) (r : Row Id) (port : Id)
    (prepared : prepare e a = some (f, r, port))
    (retained : permissionFor a f r port = some p) :
      e.formals[a.registration]? = some f ∧ a.annotation.row = some r ∧
      f.entry = some port ∧ Valid e a f r ∧ r.concrete ≠ [] ∧
      p.registration = a.registration ∧ p.parameter = f.recipe ∧
      p.formalIdentity = f.parameter ∧
      p.occurrence = a.occurrence ∧ p.owner = a.annotation.owner ∧ p.scope = a.scope ∧
      p.annotationPosition = a.annotation.position ∧ p.rowPosition = r.position ∧
      p.entry = port ∧ p.concrete = r.concrete := by
  obtain ⟨hf, hr, hp, hv⟩ := (prepare_exact e a f r port).mp prepared
  by_cases empty : r.concrete = []
  · simp [permissionFor, empty] at retained
  · have equal : build a f r port = p := by simpa [permissionFor, empty] using retained
    subst p
    exact ⟨hf, hr, hp, hv, empty, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem prepare_of_valid (e : Inputs Id) (a : Action Id) (f : Registration Id)
    (r : Row Id) (port : Id)
    (hf : e.formals[a.registration]? = some f) (hr : a.annotation.row = some r)
    (hp : f.entry = some port) (valid : Valid e a f r) :
    prepare e a = some (f, r, port) :=
  (prepare_exact e a f r port).mpr ⟨hf, hr, hp, valid⟩

theorem invalid_registration_rejected (e : Inputs Id) (a : Action Id)
    (missing : e.formals[a.registration]? = none) : prepare e a = none := by
  simp [prepare, missing]

theorem mismatched_identity_rejected (e : Inputs Id) (a : Action Id)
    (f : Registration Id) (hf : e.formals[a.registration]? = some f)
    (mismatch : f.owner ≠ a.annotation.owner ∨ f.role ≠ .computation ∨
      f.scope ≠ a.scope ∨ e.recipes[f.recipe]? ≠ some f.parameter ∨
      ownerLookup e.owners a.occurrence ≠ some f.owner ∨
      sourceLambda e f ≠ some (a.occurrence, f.parameter)) : prepare e a = none := by
  have invalid (r : Row Id) : ¬ Valid e a f r := by
    intro h
    rcases h with ⟨ho, ht, hs, hp, hw, hl, _⟩
    rcases mismatch with h | h | h | h | h | h
    · exact h ho
    · exact h ht
    · exact h hs
    · exact h hp
    · exact h hw
    · exact h hl
  cases hr : a.annotation.row <;> cases hp : f.entry <;>
    simp [prepare, hf, hr, hp, invalid]

theorem owner_local_mismatch_rejected (e : Inputs Id) (a : Action Id)
    (f : Registration Id) (hf : e.formals[a.registration]? = some f)
    (mismatch : ¬ ∃ expressions, localSource e.sources f.owner = some expressions ∧
      expressions[f.lambda]? = some (.lambda a.occurrence f.parameter)) :
    prepare e a = none := by
  apply mismatched_identity_rejected e a f hf
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (fun equal => mismatch ((source_lambda_exact e f _ _).mp equal))))))

theorem duplicate_or_domain_rejected (e : Inputs Id) (a : Action Id)
    (f : Registration Id) (hf : e.formals[a.registration]? = some f)
    (occupied : f.recipe ∈ e.occupiedDomains ∨ a.registration ∈ e.retainedRegistrations) :
    prepare e a = none := by
  have invalid (r : Row Id) : ¬ Valid e a f r := by
    intro h
    rcases h with ⟨_, _, _, _, _, _, hd, hr, _⟩
    rcases occupied with h | h
    · exact hd h
    · exact hr h
  cases hr : a.annotation.row <;> cases hp : f.entry <;>
    simp [prepare, hf, hr, hp, invalid]

/-- Authentication compares every retained coordinate, including exact row and
port. It confers no provider/arrival authority. -/
def authenticates (expected actual : Permission Id) : Bool := decide (actual = expected)

theorem foreign_witness_rejected (expected actual : Permission Id)
    (different : actual ≠ expected) : authenticates expected actual = false := by
  simp [authenticates, different]

inductive Endpoint (Id : Type) where
  | entry (port : Id)
  | symbolic (scope name : Id)
  deriving DecidableEq

structure Link (Id : Type) where
  occurrence : Id
  slot : Nat
  lower : Endpoint Id
  upper : Endpoint Id
  deriving DecidableEq

def symbolicLinks (a : Action Id) (r : Row Id) (port : Id) :
    List (Link Id) :=
  match r.variables with
  | [] => []
  | name :: _ => [⟨a.occurrence, 45, .entry port, .symbolic a.scope name⟩,
      ⟨a.occurrence, 46, .symbolic a.scope name, .entry port⟩]

/-- Publication projection: links are the generated-constraint trace; inflow is
externally supplied contribution data. This is not the solver's lower-bound
store, and no claim about propagation of existing lowers is encoded here. -/
structure State (Id : Type) where
  permissions : List (Permission Id)
  links : List (Link Id)
  inflow : List Id
  deriving DecidableEq

/-- Local publication point after the existing symbolic constraint step.
`ready` denotes fallible preparation/constraint readiness, not the entire Rust
call's result: its final resource sample may fail after the record is pushed.
The links append records that step's generated constraints; inflow is supplied
separately. No propagation, failed-call rollback or private-state restoration
is asserted. -/
def publish (a : Action Id) (f : Registration Id) (r : Row Id) (port : Id)
    (ready : Bool) (s : State Id) : Option (State Id) :=
  if ready then some ⟨s.permissions ++ (permissionFor a f r port).toList,
    s.links ++ symbolicLinks a r port, s.inflow⟩
  else none

omit [DecidableEq Id] in
theorem publication_exact (a : Action Id) (f : Registration Id) (r : Row Id) (port : Id)
    (s : State Id) : publish a f r port true s =
      some ⟨s.permissions ++ (permissionFor a f r port).toList,
        s.links ++ symbolicLinks a r port, s.inflow⟩ := rfl

omit [DecidableEq Id] in
theorem failed_publication_unavailable (a : Action Id) (f : Registration Id) (r : Row Id)
    (port : Id) (s : State Id) : publish a f r port false s = none := rfl

omit [DecidableEq Id] in
theorem permission_no_inflow (a : Action Id) (f : Registration Id) (r : Row Id) (port : Id)
    (ready : Bool) (before after : State Id)
    (success : publish a f r port ready before = some after) : after.inflow = before.inflow := by
  cases ready <;> simp [publish] at success
  cases success
  rfl

omit [DecidableEq Id] in
theorem symbolic_link_preserved (a : Action Id) (f : Registration Id) (r : Row Id) (port : Id)
    (name : Id) (s : State Id) (symbolic : r.variables = [name]) :
    publish a f r port true s = some
      ⟨s.permissions ++ (permissionFor a f r port).toList,
        s.links ++ [⟨a.occurrence, 45, .entry port, .symbolic a.scope name⟩,
        ⟨a.occurrence, 46, .symbolic a.scope name, .entry port⟩], s.inflow⟩ := by
  simp [publish, symbolicLinks, symbolic]

/-- Direct application: source-validated input constructs the same shared
witness, preserves full ordered concrete data, and adds only the old symbolic
links. No producer law, typing predicate or downstream join is a hypothesis. -/
theorem constructed_entry_publication (e : Inputs Id) (a : Action Id)
    (f : Registration Id) (r : Row Id) (port : Id) (s : State Id)
    (hf : e.formals[a.registration]? = some f) (hr : a.annotation.row = some r)
    (hp : f.entry = some port) (valid : Valid e a f r) (nonempty : r.concrete ≠ []) :
    ∃ p, prepare e a = some (f, r, port) ∧ permissionFor a f r port = some p ∧
      p.concrete = r.concrete ∧ p.entry = port ∧
      publish a f r port true s = some
        ⟨s.permissions ++ [p], s.links ++ symbolicLinks a r port, s.inflow⟩ := by
  refine ⟨build a f r port, prepare_of_valid e a f r port hf hr hp valid, ?_, rfl, rfl, ?_⟩
  · simp [permissionFor, nonempty]
  · simp [publish, permissionFor, nonempty]

theorem empty_concrete_local_case (e : Inputs Id) (a : Action Id)
    (f : Registration Id) (r : Row Id) (port : Id) (s : State Id)
    (hf : e.formals[a.registration]? = some f) (hr : a.annotation.row = some r)
    (hp : f.entry = some port) (valid : Valid e a f r) (empty : r.concrete = []) :
    prepare e a = some (f, r, port) ∧ permissionFor a f r port = none ∧
      publish a f r port true s = some
        ⟨s.permissions, s.links ++ symbolicLinks a r port, s.inflow⟩ := by
  refine ⟨prepare_of_valid e a f r port hf hr hp valid, ?_, ?_⟩
  · simp [permissionFor, empty]
  · simp [publish, permissionFor, empty]

/-- A fully constructed finite instance with a repeated concrete member and a
symbolic row. This witnesses the model's inhabited successful branch, without
asserting source/native reachability of these abstract numeric keys. -/
theorem concrete_constructor_example :
    let f : Registration Nat := ⟨1, 0, 2, 0, 3, .computation, some 4⟩
    let r : Row Nat := ⟨5, [7, 7, 11], [13]⟩
    let a : Action Nat := ⟨0, ⟨1, 6, some r⟩, 17, 3⟩
    let e : Inputs Nat := ⟨[f], [2], [], [(1, [.lambda 17 2])], [(17, 1)], [], []⟩
    let p : Permission Nat := ⟨0, 0, 2, 17, 1, 3, 6, 5, 4, [7, 7, 11]⟩
    prepare e a = some (f, r, 4) ∧ permissionFor a f r 4 = some p ∧
      publish a f r 4 true ⟨[], [], []⟩ = some
        ⟨[p], [⟨17, 45, .entry 4, .symbolic 3 13⟩,
          ⟨17, 46, .symbolic 3 13, .entry 4⟩], []⟩ := by
  decide

/-- Definition ownership remains distinguished in the concrete regression
model; these are abstract exact keys, not a forged HIR/runtime receipt. -/
inductive ExampleId where
  | definition (ordinal : Nat)
  | key (ordinal : Nat)
  deriving DecidableEq

def definitionRegistration : Registration ExampleId :=
  ⟨.definition 1, 0, .key 2, 0, .key 3, .computation, some (.key 4)⟩

def definitionRow : Row ExampleId := ⟨.key 5, [.key 7, .key 7, .key 11], [.key 13]⟩

def definitionAction : Action ExampleId :=
  ⟨0, ⟨.definition 1, .key 6, some definitionRow⟩, .key 17, .key 3⟩

def definitionInputs : Inputs ExampleId :=
  ⟨[definitionRegistration], [.key 2], [],
    [(.definition 1, [.lambda (.key 17) (.key 2)])], [(.key 17, .definition 1)], [], []⟩

/-- Definition-backed source can have an empty execution schedule and an
authentic owner-local Lambda. The old guard rejects exactly that finite case. -/
theorem definition_empty_schedule_counterexample :
    definitionInputs.schedules = [] ∧
    legacyScheduleGuard definitionInputs definitionRegistration definitionAction = false ∧
    prepare definitionInputs definitionAction =
      some (definitionRegistration, definitionRow, .key 4) := by
  decide

theorem definition_owner_local_case :
    localSource definitionInputs.sources (.definition 1) =
      some [.lambda (.key 17) (.key 2)] ∧
    sourceLambda definitionInputs definitionRegistration = some (.key 17, .key 2) ∧
    permissionFor definitionAction definitionRegistration definitionRow (.key 4) =
      some ⟨0, 0, .key 2, .key 17, .definition 1, .key 3, .key 6, .key 5,
        .key 4, [.key 7, .key 7, .key 11]⟩ := by
  decide

end YulangClosure.ComputationPermissionEntryR39
