import YulangClosure.UseScopedPermissionR43
import YulangClosure.EffectPermissionResidualR38

/-!
R44 finite route/publication and conditional guard model. Successful internal
admission uses original terms and creates only a receipt. Structured incoming
publication requires an already supplied captured/fresh route and first admits
the same full DefinitionUseId. These constructors model successful publication,
not allocation, rollback or all Rust return paths. Source extraction, initial
empty route inventory, and absence of other publishers remain explicit duties.
The supplied arrivalAtEntry relation must be independently established for the
actual terminal at the exact use/native entry; no implementation of it is
constructed here. The conditional guard is a proposed mathematical guard, NOT the current Rust
guard; R38 documents that Rust's native guard does not consult permissions.
-/
namespace YulangClosure.RouteCompatibilityR44

open LambdaArgumentEffectIncidenceR41 NativeIncidenceAdapterR42

inductive Kind where
  | internal | incomingInt | incomingBottomTrivial | incomingStructured
  deriving DecidableEq

structure Receipt (DefinitionUse Term : Type) where
  definitionUse : DefinitionUse
  kind : Kind
  lower : Term
  upper : Term

/-- Receiver owner and provider root are separate exact identities. An actual
captured graph, retained maps/context and native observations must be supplied
by the source owner; this record is not constructed from an Internal receipt. -/
structure FreshRoute (Id Term Row DefinitionUse ContextUse : Type) where
  use : Use DefinitionUse ContextUse
  sourceOwner : Id
  providerRoot : Id
  originalRoot : Term
  freshRoot : Term
  captured : Captured Id
  reads : Reads Term Row DefinitionUse ContextUse
  ordinal : Nat
  probe : Probe Term Row

structure State (Id Term Row DefinitionUse ContextUse : Type) where
  receipts : List (Receipt DefinitionUse Term)
  fresh : List (FreshRoute Id Term Row DefinitionUse ContextUse)

variable {Id Term Row DefinitionUse ContextUse : Type}

/-- Successful common admission projection. Rust's duplicate path asserts;
`none` here means no successful second admission, not graceful Rust recovery. -/
def admission [DecidableEq DefinitionUse]
    (s : State Id Term Row DefinitionUse ContextUse) (id : DefinitionUse)
    (kind : Kind) (lower upper : Term) : Option (State Id Term Row DefinitionUse ContextUse) :=
  if id ∈ s.receipts.map Receipt.definitionUse then none
  else some ⟨s.receipts ++ [⟨id, kind, lower, upper⟩], s.fresh⟩

def routeInternal [DecidableEq DefinitionUse]
    (s : State Id Term Row DefinitionUse ContextUse) (id : DefinitionUse)
    (originalLower originalUpper : Term) :=
  admission s id .internal originalLower originalUpper

/-- The argument `fr` presupposes successful capture, FreshUse reconstruction,
retained map ownership and resource readiness. No existence claim is made. -/
def routeIncoming [DecidableEq DefinitionUse]
    (s : State Id Term Row DefinitionUse ContextUse)
    (fr : FreshRoute Id Term Row DefinitionUse ContextUse) (upper : Term) :
    Option (State Id Term Row DefinitionUse ContextUse) := do
  let admitted ← admission s fr.use.definitionUse .incomingStructured fr.freshRoot upper
  some ⟨admitted.receipts, admitted.fresh ++ [fr]⟩

theorem admission_exact [DecidableEq DefinitionUse]
    (s next : State Id Term Row DefinitionUse ContextUse) (id : DefinitionUse)
    (kind : Kind) (lower upper : Term)
    (accepted : admission s id kind lower upper = some next) :
    id ∉ s.receipts.map Receipt.definitionUse ∧
      next.receipts = s.receipts ++ [⟨id, kind, lower, upper⟩] ∧ next.fresh = s.fresh := by
  unfold admission at accepted
  split at accepted
  · contradiction
  · cases accepted
    exact ⟨by assumption, rfl, rfl⟩

theorem single_admission [DecidableEq DefinitionUse]
    (s next : State Id Term Row DefinitionUse ContextUse) (id : DefinitionUse)
    (kind laterKind : Kind) (lower upper laterLower laterUpper : Term)
    (accepted : admission s id kind lower upper = some next) :
    admission next id laterKind laterLower laterUpper = none := by
  obtain ⟨_, receipts, _⟩ := admission_exact s next id kind lower upper accepted
  have present : id ∈ next.receipts.map Receipt.definitionUse := by rw [receipts]; simp
  simp [admission, present]

theorem internal_preserves_fresh [DecidableEq DefinitionUse]
    (s next : State Id Term Row DefinitionUse ContextUse) (id : DefinitionUse)
    (lower upper : Term) (accepted : routeInternal s id lower upper = some next) :
    next.fresh = s.fresh :=
  (admission_exact s next id .internal lower upper accepted).2.2

theorem internal_cannot_readmit_incoming [DecidableEq DefinitionUse]
    (s next : State Id Term Row DefinitionUse ContextUse) (id : DefinitionUse)
    (lower upper incomingUpper : Term)
    (fr : FreshRoute Id Term Row DefinitionUse ContextUse)
    (accepted : routeInternal s id lower upper = some next)
    (sameId : fr.use.definitionUse = id) : routeIncoming next fr incomingUpper = none := by
  have rejected := single_admission s next id .internal .incomingStructured lower upper
    fr.freshRoot incomingUpper accepted
  simp [routeIncoming, sameId, rejected]

/-- Exact R43 FreshRoute/native-incidence prerequisite, with full use AND
context identity. Equal use IDs, Terms or rows alone do not provide a witness. -/
def SameUseFresh [DecidableEq Term] [DecidableEq Row]
    [DecidableEq DefinitionUse] [DecidableEq ContextUse] (s : State Id Term Row DefinitionUse ContextUse)
    (use : Use DefinitionUse ContextUse)
    (c : Certificate Id Term Row DefinitionUse ContextUse) : Prop :=
  ∃ fr ∈ s.fresh, fr.use = use ∧
    extract fr.captured use fr.reads fr.ordinal fr.probe = some c

theorem internal_alone_no_r43_route [DecidableEq DefinitionUse]
    [DecidableEq Term] [DecidableEq Row] [DecidableEq ContextUse]
    (s next : State Id Term Row DefinitionUse ContextUse) (id : DefinitionUse)
    (lower upper : Term) (use : Use DefinitionUse ContextUse)
    (c : Certificate Id Term Row DefinitionUse ContextUse)
    (initiallyEmpty : s.fresh = [])
    (accepted : routeInternal s id lower upper = some next) :
    ¬ SameUseFresh next use c := by
  have empty : next.fresh = [] := (internal_preserves_fresh s next id lower upper accepted).trans initiallyEmpty
  simp [SameUseFresh, empty]

variable [DecidableEq Id] [DecidableEq Term] [DecidableEq Row]
  [DecidableEq DefinitionUse] [DecidableEq ContextUse]

def nativeAvailable (s : State Id Term Row DefinitionUse ContextUse)
    (use : Use DefinitionUse ContextUse)
    (c : Certificate Id Term Row DefinitionUse ContextUse) : Bool :=
  s.fresh.any fun fr => decide (fr.use = use) &&
    decide (extract fr.captured use fr.reads fr.ordinal fr.probe = some c)

theorem native_available_iff (s : State Id Term Row DefinitionUse ContextUse)
    (use : Use DefinitionUse ContextUse)
    (c : Certificate Id Term Row DefinitionUse ContextUse) :
    nativeAvailable s use c = true ↔ SameUseFresh s use c := by
  simp [nativeAvailable, SameUseFresh, List.any_eq_true]

def allows (p : ComputationPermissionEntryR39.Permission Id) :
    EffectPermissionResidualR38.Terminal Id → Bool
  | .member _ family _ => decide (family ∈ p.concrete)
  | .other _ => false

/-- Conditional mathematical consumer only. Every conjunct is necessary:
actual same-use FreshRoute/native extraction, exact R43 binding, actual arrived
terminal, source-owned exact-use/entry arrival relation, concrete permission, and the existing selected-Catch/native guard. -/
def consumerGuard (s : State Id Term Row DefinitionUse ContextUse)
    (permissions : List (ComputationPermissionEntryR39.Permission Id))
    (req : UseScopedPermissionR43.Request Id) (use : Use DefinitionUse ContextUse)
    (c : Certificate Id Term Row DefinitionUse ContextUse)
    (out : UseScopedPermissionR43.Binding Id Term Row DefinitionUse ContextUse)
    (assembly : EffectPermissionResidualR38.Assembly Id)
    (arrivals : List (EffectPermissionResidualR38.Terminal Id))
    (arrivalAtEntry : Use DefinitionUse ContextUse → Term → EffectPermissionResidualR38.Terminal Id → Bool)
    (t : EffectPermissionResidualR38.Terminal Id) : Bool :=
  nativeAvailable s use c && decide (UseScopedPermissionR43.bind permissions req use c = some out) &&
    decide (t ∈ arrivals) && arrivalAtEntry use c.child t && allows out.permission t && EffectPermissionResidualR38.nativeGuard assembly t

theorem suppression_iff (s : State Id Term Row DefinitionUse ContextUse)
    (permissions : List (ComputationPermissionEntryR39.Permission Id))
    (req : UseScopedPermissionR43.Request Id) (use : Use DefinitionUse ContextUse)
    (c : Certificate Id Term Row DefinitionUse ContextUse)
    (out : UseScopedPermissionR43.Binding Id Term Row DefinitionUse ContextUse)
    (assembly : EffectPermissionResidualR38.Assembly Id)
    (arrivals : List (EffectPermissionResidualR38.Terminal Id))
    (arrivalAtEntry : Use DefinitionUse ContextUse → Term → EffectPermissionResidualR38.Terminal Id → Bool)
    (t : EffectPermissionResidualR38.Terminal Id) :
    consumerGuard s permissions req use c out assembly arrivals arrivalAtEntry t = true ↔
      SameUseFresh s use c ∧ UseScopedPermissionR43.bind permissions req use c = some out ∧
      t ∈ arrivals ∧ arrivalAtEntry use c.child t = true ∧ allows out.permission t = true ∧
      EffectPermissionResidualR38.nativeGuard assembly t = true := by
  simp [consumerGuard, native_available_iff, and_assoc]

theorem suppression_requires_all (s : State Id Term Row DefinitionUse ContextUse)
    (permissions : List (ComputationPermissionEntryR39.Permission Id))
    (req : UseScopedPermissionR43.Request Id) (use : Use DefinitionUse ContextUse)
    (c : Certificate Id Term Row DefinitionUse ContextUse)
    (out : UseScopedPermissionR43.Binding Id Term Row DefinitionUse ContextUse)
    (assembly : EffectPermissionResidualR38.Assembly Id)
    (arrivals : List (EffectPermissionResidualR38.Terminal Id))
    (arrivalAtEntry : Use DefinitionUse ContextUse → Term → EffectPermissionResidualR38.Terminal Id → Bool)
    (t : EffectPermissionResidualR38.Terminal Id)
    (suppressed : consumerGuard s permissions req use c out assembly arrivals arrivalAtEntry t = true) :
    SameUseFresh s use c ∧ UseScopedPermissionR43.bind permissions req use c = some out ∧
    t ∈ arrivals ∧ arrivalAtEntry use c.child t = true ∧ ∃ origin family,
      t = .member origin family none ∧ family ∈ out.permission.concrete ∧
      assembly.handled = assembly.provider.operation ∧
      family = assembly.provider.operation.family ∧ origin = assembly.provider := by
  obtain ⟨fresh, bound, arrived, atEntry, permitted, native⟩ :=
    (suppression_iff s permissions req use c out assembly arrivals arrivalAtEntry t).mp suppressed
  obtain ⟨origin, family, tail, ht, selected, closed, familyExact, providerExact⟩ :=
    (EffectPermissionResidualR38.native_guard_sound assembly t).mp native
  subst tail
  subst t
  exact ⟨fresh, bound, arrived, atEntry, origin, family, rfl,
    by simpa [allows] using permitted, selected, familyExact, providerExact⟩

theorem unmatched_endpoint_preserved (s : State Id Term Row DefinitionUse ContextUse)
    (permissions : List (ComputationPermissionEntryR39.Permission Id))
    (req : UseScopedPermissionR43.Request Id) (use : Use DefinitionUse ContextUse)
    (c : Certificate Id Term Row DefinitionUse ContextUse)
    (out : UseScopedPermissionR43.Binding Id Term Row DefinitionUse ContextUse)
    (assembly : EffectPermissionResidualR38.Assembly Id)
    (arrivals : List (EffectPermissionResidualR38.Terminal Id))
    (arrivalAtEntry : Use DefinitionUse ContextUse → Term → EffectPermissionResidualR38.Terminal Id → Bool)
    (t : EffectPermissionResidualR38.Terminal Id)
    (arrived : t ∈ arrivals)
    (unmatched : consumerGuard s permissions req use c out assembly arrivals arrivalAtEntry t = false) :
    t ∈ EffectPermissionResidualR38.residual
      (consumerGuard s permissions req use c out assembly arrivals arrivalAtEntry) arrivals :=
  EffectPermissionResidualR38.unmatched_preserved _ _ _ arrived unmatched

theorem internal_only_no_suppression (s next : State Id Term Row DefinitionUse ContextUse)
    (id : DefinitionUse) (lower upper : Term)
    (permissions : List (ComputationPermissionEntryR39.Permission Id))
    (req : UseScopedPermissionR43.Request Id) (use : Use DefinitionUse ContextUse)
    (c : Certificate Id Term Row DefinitionUse ContextUse)
    (out : UseScopedPermissionR43.Binding Id Term Row DefinitionUse ContextUse)
    (assembly : EffectPermissionResidualR38.Assembly Id)
    (arrivals : List (EffectPermissionResidualR38.Terminal Id))
    (arrivalAtEntry : Use DefinitionUse ContextUse → Term → EffectPermissionResidualR38.Terminal Id → Bool)
    (t : EffectPermissionResidualR38.Terminal Id)
    (initiallyEmpty : s.fresh = [])
    (accepted : routeInternal s id lower upper = some next) :
    consumerGuard next permissions req use c out assembly arrivals arrivalAtEntry t = false := by
  have empty := (internal_preserves_fresh s next id lower upper accepted).trans initiallyEmpty
  simp [consumerGuard, nativeAvailable, empty]

/-- Applies the R38 ordered fold without changing or claiming its Rust guard.
All unmatched endpoints retain their original identity and order in residual. -/
theorem conditional_fold_exact (s : State Id Term Row DefinitionUse ContextUse)
    (permissions : List (ComputationPermissionEntryR39.Permission Id))
    (req : UseScopedPermissionR43.Request Id) (use : Use DefinitionUse ContextUse)
    (c : Certificate Id Term Row DefinitionUse ContextUse)
    (out : UseScopedPermissionR43.Binding Id Term Row DefinitionUse ContextUse)
    (assembly : EffectPermissionResidualR38.Assembly Id)
    (arrivals : List (EffectPermissionResidualR38.Terminal Id))
    (arrivalAtEntry : Use DefinitionUse ContextUse → Term → EffectPermissionResidualR38.Terminal Id → Bool) :
    let guard := consumerGuard s permissions req use c out assembly arrivals arrivalAtEntry
    EffectPermissionResidualR38.sourceFold guard arrivals ⟨[], []⟩ =
      ⟨EffectPermissionResidualR38.residual guard arrivals,
        arrivals.map (fun t => (t, EffectPermissionResidualR38.outcome guard t))⟩ := by
  exact EffectPermissionResidualR38.fold_correspondence _ _ ⟨[], []⟩

end YulangClosure.RouteCompatibilityR44
