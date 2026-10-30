import YulangClosure.ComputationPermissionEntryR39

/-!
R41 finite constructor/capture/FreshUse model. `Id` denotes complete resolved
source identities, not spellings; a registration ordinal is retained together
with its owner and Lambda occurrence. The model constructs incidence rather
than assuming a registration-to-child law. The shared maps denote one capture
and one exact use, and are not required to be injective.

Rust correspondence is separate: its successful constructor must produce this
four-port shape, capture must use the same exact Function term and shared
interning maps, and FreshUse must use its own ordered terms/rows vectors.
No interpreter, allocation/rollback, provider arrival, Catch, subtraction,
whole-source theorem or production permission is supplied here.
-/
namespace YulangClosure.LambdaArgumentEffectIncidenceR41

structure Ports (T : Type) where
  argument : T
  argumentEffect : T
  resultEffect : T
  result : T
  deriving DecidableEq

def Ports.children {T : Type} (p : Ports T) : List T :=
  [p.argument, p.argumentEffect, p.resultEffect, p.result]

def Ports.map {T U : Type} (f : T → U) (p : Ports T) : Ports U :=
  ⟨f p.argument, f p.argumentEffect, f p.resultEffect, f p.result⟩

theorem function_child_one {T : Type} (p : Ports T) :
    p.children[1]? = some p.argumentEffect := rfl

/-- The label is formed at Lambda construction, before row canonicalization. -/
structure Label (Id : Type) where
  owner : Id
  registration : Nat
  lambda : Nat
  formal : Id
  recipe : Nat
  occurrence : Id
  scope : Id
  entry : Id
  deriving DecidableEq

def label {Id : Type} (a : ComputationPermissionEntryR39.Action Id) (f : ComputationPermissionEntryR39.Registration Id)
    (port : Id) : Label Id :=
  ⟨f.owner, a.registration, f.lambda, f.parameter, f.recipe, a.occurrence, f.scope, port⟩

/-- Positive Function's exact term key and ordered four-child projection. -/
structure LiveLambda (Id Term : Type) where
  origin : Label Id
  function : Term
  ports : Ports Term

/-- `negativeEffect` is the constructor's negative effect-term operation.
The argument-effect term is constructed from the registration's entry port. -/
def constructLambda {Id Term : Type} (a : ComputationPermissionEntryR39.Action Id)
    (f : ComputationPermissionEntryR39.Registration Id) (port : Id) (negativeEffect : Id → Term)
    (function argument returned result : Term) : LiveLambda Id Term :=
  ⟨label a f port, function, ⟨argument, negativeEffect port, returned, result⟩⟩

theorem lambda_origin {Id Term : Type} (a : ComputationPermissionEntryR39.Action Id)
    (f : ComputationPermissionEntryR39.Registration Id) (port : Id) (negativeEffect : Id → Term)
    (function argument returned result : Term) :
    let built := constructLambda a f port negativeEffect function argument returned result
    built.origin = label a f port ∧ built.function = function ∧
      built.ports.children[1]? = some (negativeEffect built.origin.entry) :=
  ⟨rfl, rfl, rfl⟩

structure Captured (Id : Type) where
  origin : Label Id
  function : Nat
  ports : Ports Nat
  entryRow : Nat

/-- One shared term-interning map and one shared row-index map. This models
only the successful exact-Function branch, without asserting its availability.
It does not assert that arbitrary Rust graphs satisfy this projection. -/
def capture {Id Term : Type} (nodes : Term → Nat) (rows : Id → Nat)
    (built : LiveLambda Id Term) : Captured Id :=
  ⟨built.origin, nodes built.function, built.ports.map nodes, rows built.origin.entry⟩

theorem capture_preserves {Id Term : Type} (nodes : Term → Nat)
    (rows : Id → Nat) (built : LiveLambda Id Term) :
    (capture nodes rows built).origin = built.origin ∧
      (capture nodes rows built).function = nodes built.function ∧
      (capture nodes rows built).ports.children[1]? =
        some (nodes built.ports.argumentEffect) ∧
      (capture nodes rows built).entryRow = rows built.origin.entry :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Definition use and FreshUse context stamp are both retained. Their types
stand for exact identities, not display names. -/
structure Use (DefinitionUse ContextUse : Type) where
  definitionUse : DefinitionUse
  contextUse : ContextUse
  deriving DecidableEq

structure Image (Id Term Row DefinitionUse ContextUse : Type) where
  origin : Label Id
  use : Use DefinitionUse ContextUse
  sourceFunction : Nat
  sourceArgumentEffect : Nat
  function : Term
  ports : Ports Term
  entryRow : Row

def freshen {Id Term Row DefinitionUse ContextUse : Type}
    (use : Use DefinitionUse ContextUse) (terms : Nat → Term) (rows : Nat → Row)
    (captured : Captured Id) : Image Id Term Row DefinitionUse ContextUse :=
  ⟨captured.origin, use, captured.function, captured.ports.argumentEffect,
    terms captured.function, captured.ports.map terms, rows captured.entryRow⟩

theorem freshuse_exact {Id Term Row DefinitionUse ContextUse : Type}
    (use : Use DefinitionUse ContextUse) (terms : Nat → Term) (rows : Nat → Row)
    (captured : Captured Id) :
    let image := freshen use terms rows captured
    image.origin = captured.origin ∧ image.use = use ∧
      image.sourceFunction = captured.function ∧
      image.sourceArgumentEffect = captured.ports.argumentEffect ∧
      image.function = terms captured.function ∧
      image.ports.children[1]? = some (terms captured.ports.argumentEffect) ∧
      image.entryRow = rows captured.entryRow :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem distinct_registration_images {Id Term Row DefinitionUse ContextUse : Type}
    (use : Use DefinitionUse ContextUse) (terms : Nat → Term) (rows : Nat → Row)
    (left right : Captured Id)
    (different : left.origin.registration ≠ right.origin.registration) :
    (freshen use terms rows left).origin ≠ (freshen use terms rows right).origin := by
  intro equal
  exact different (congrArg Label.registration equal)

/-- Even a shared mapped row gives no identification of the retained labels. -/
theorem shared_row_distinct_labels {Id Term Row DefinitionUse ContextUse : Type}
    (use : Use DefinitionUse ContextUse) (terms : Nat → Term) (rows : Nat → Row)
    (left right : Captured Id)
    (different : left.origin.registration ≠ right.origin.registration)
    (shared : rows left.entryRow = rows right.entryRow) :
    (freshen use terms rows left).entryRow = (freshen use terms rows right).entryRow ∧
      (freshen use terms rows left).origin ≠ (freshen use terms rows right).origin :=
  ⟨shared, distinct_registration_images use terms rows left right different⟩

/-- Application to R39's same constructed permission witness and R40's ordered
four-child image. All original R39 validation hypotheses remain explicit.
Native realization of these projections remains a separate source premise. -/
theorem entry_to_exact_use {Id Term Row DefinitionUse ContextUse : Type}
    [DecidableEq Id] (e : ComputationPermissionEntryR39.Inputs Id) (a : ComputationPermissionEntryR39.Action Id)
    (f : ComputationPermissionEntryR39.Registration Id) (r : ComputationPermissionEntryR39.Row Id) (port : Id) (s : ComputationPermissionEntryR39.State Id)
    (hf : e.formals[a.registration]? = some f) (hr : a.annotation.row = some r)
    (hp : f.entry = some port) (valid : ComputationPermissionEntryR39.Valid e a f r)
    (nonempty : r.concrete ≠ [])
    (negativeEffect : Id → Term) (function argument returned result : Term)
    (nodes : Term → Nat) (rowIndexes : Id → Nat)
    (use : Use DefinitionUse ContextUse) (terms : Nat → Term) (rows : Nat → Row) :
    let built := constructLambda a f port negativeEffect function argument returned result
    let image := freshen use terms rows (capture nodes rowIndexes built)
    ∃ p, ComputationPermissionEntryR39.prepare e a = some (f, r, port) ∧
      ComputationPermissionEntryR39.permissionFor a f r port = some p ∧
      ComputationPermissionEntryR39.publish a f r port true s = some
        ⟨s.permissions ++ [p], s.links ++ ComputationPermissionEntryR39.symbolicLinks a r port, s.inflow⟩ ∧
      p.concrete = r.concrete ∧ p.registration = image.origin.registration ∧
      p.owner = image.origin.owner ∧ p.occurrence = image.origin.occurrence ∧
      p.entry = image.origin.entry ∧ image.use = use ∧
      image.sourceFunction = nodes function ∧
      image.sourceArgumentEffect = nodes (negativeEffect port) ∧
      image.ports.children[1]? = some (terms (nodes (negativeEffect port))) ∧
      image.entryRow = rows (rowIndexes port) := by
  obtain ⟨p, prepared, retained, concrete, entry, published⟩ :=
    ComputationPermissionEntryR39.constructed_entry_publication e a f r port s hf hr hp valid nonempty
  have exact := ComputationPermissionEntryR39.exact_row_retained e a p f r port prepared retained
  rcases exact with ⟨_, _, _, _, _, registration, _, _, occurrence, owner, _, _, _, _, _⟩
  refine ⟨p, prepared, retained, published, concrete, registration, ?_, occurrence,
    entry, rfl, rfl, rfl, rfl, rfl⟩
  exact owner.trans valid.1.symm

/-- Empty/variable-only concrete annotations remain admitted by R39, with no
permission record. The Lambda construction and its labelled child still exist. -/
theorem empty_entry_incidence {Id Term : Type} [DecidableEq Id]
    (e : ComputationPermissionEntryR39.Inputs Id)
    (a : ComputationPermissionEntryR39.Action Id)
    (f : ComputationPermissionEntryR39.Registration Id)
    (r : ComputationPermissionEntryR39.Row Id) (port : Id)
    (s : ComputationPermissionEntryR39.State Id)
    (hf : e.formals[a.registration]? = some f) (hr : a.annotation.row = some r)
    (hp : f.entry = some port) (valid : ComputationPermissionEntryR39.Valid e a f r)
    (empty : r.concrete = []) (negativeEffect : Id → Term)
    (function argument returned result : Term) :
    ComputationPermissionEntryR39.prepare e a = some (f, r, port) ∧
      ComputationPermissionEntryR39.permissionFor a f r port = none ∧
      (constructLambda a f port negativeEffect function argument returned result).origin =
        label a f port ∧
      (constructLambda a f port negativeEffect function argument returned result).ports.children[1]? =
        some (negativeEffect port) := by
  obtain ⟨prepared, absent, _⟩ :=
    ComputationPermissionEntryR39.empty_concrete_local_case e a f r port s hf hr hp valid empty
  exact ⟨prepared, absent, rfl, rfl⟩

inductive Effect where
  | signal | write
  deriving DecidableEq

structure AnalyticPermission where
  registration : Nat
  tail : Nat
  concrete : List Effect
  deriving DecidableEq

structure AnalyticArrival where
  registration : Nat
  tail : Nat
  effect : Effect
  deriving DecidableEq

/-- Hypothetical consumer only: these predicates do not describe a Rust body. -/
def rowOnlyAuthorizes (p : AnalyticPermission) (a : AnalyticArrival) : Prop :=
  p.tail = a.tail ∧ a.effect ∈ p.concrete

def registrationAuthorizes (p : AnalyticPermission) (a : AnalyticArrival) : Prop :=
  p.registration = a.registration ∧ rowOnlyAuthorizes p a

/-- `{signal | e}` and `{write | e}` retain distinct registrations. If a signal
contribution actually arrives on the write registration's path, a consumer using
only the shared tail and concrete membership would misuse the signal permission.
No arrival/reachability or actual compiler defect is asserted. -/
theorem conditional_shared_tail_falsifier :
    let signalPermission : AnalyticPermission := ⟨0, 7, [.signal]⟩
    let writePermission : AnalyticPermission := ⟨1, 7, [.write]⟩
    let arrival : AnalyticArrival := ⟨1, 7, .signal⟩
    signalPermission.tail = writePermission.tail ∧
      signalPermission.registration ≠ writePermission.registration ∧
      signalPermission.concrete ≠ writePermission.concrete ∧
      arrival.registration = writePermission.registration ∧
      rowOnlyAuthorizes signalPermission arrival ∧
      ¬ registrationAuthorizes signalPermission arrival := by
  simp [rowOnlyAuthorizes, registrationAuthorizes]

end YulangClosure.LambdaArgumentEffectIncidenceR41
