import Std

/-!
R38 bounded finite guard/fold mathematics. Identifiers are arbitrary exact keys,
never spelling, ranges or just families. This standalone model represents the
terminal fold in candidate_receiver.rs at the frozen R38 baseline. It does not
assert that Rust constructed any value of these records or that a graph walk
returned its terminal list. The permission checker below authenticates retained
metadata only; it neither issues an arrival witness nor changes nativeGuard.
The source has no authenticated FormalPermission-to-arrival join. In particular,
these theorems do not justify deploying a strengthened subtraction guard.
-/
namespace YulangClosure.EffectPermissionResidualR38

inductive PortStep where
  | argument | result | element (index : Nat)
  deriving DecidableEq

/-- Coordinates retained by candidate_effect::FormalPermission. Scope is kept
separate from owner, and the full path and row position remain significant. -/
structure FormalSite (Id : Type) where
  parameter : Nat
  occurrence : Id
  owner : Id
  scope : Id
  path : List PortStep
  row : Id
  deriving DecidableEq

structure Permission (Id : Type) where
  site : FormalSite Id
  concrete : List Id
  deriving DecidableEq

variable {Id : Type}

/-- Metadata authentication only, with no provider/arrival interpretation. -/
def permissionGuard [DecidableEq Id]
    (site : FormalSite Id) (family : Id) (p : Permission Id) : Bool :=
  decide (p.site = site ∧ family ∈ p.concrete)

/-- SourceOperationId retains both family and operation identity. -/
structure Operation (Id : Type) where
  family : Id
  declaration : Id
  deriving DecidableEq

/-- Exact operation-view provenance, not just an allowed family. Occurrence
identifies the source provider boundary in this bounded assembly. -/
structure Origin (Id : Type) where
  occurrence : Id
  operation : Operation Id
  deriving DecidableEq

inductive Terminal (Id : Type) where
  | member (origin : Origin Id) (family : Id) (tail : Option Id)
  | other (endpoint : Id)
  deriving DecidableEq

structure Assembly (Id : Type) where
  provider : Origin Id
  handled : Operation Id
  deriving DecidableEq

/-- This is the existing native suppression test, *without* any invented
permission join. selected is derived from exact operation equality. -/
def nativeGuard [DecidableEq Id] (s : Assembly Id) : Terminal Id → Bool
  | .member origin family tail =>
      decide (s.handled = s.provider.operation ∧ tail = none ∧
        family = s.provider.operation.family ∧ origin = s.provider)
  | .other _ => false

variable [DecidableEq Id]

theorem permission_guard_sound (site : FormalSite Id) (family : Id) (p : Permission Id) :
    permissionGuard site family p = true ↔ p.site = site ∧ family ∈ p.concrete := by
  simp [permissionGuard]

theorem foreign_formal_rejected (site : FormalSite Id) (family : Id) (p : Permission Id)
    (different : p.site ≠ site) : permissionGuard site family p = false := by
  simp [permissionGuard, different]

theorem absent_family_rejected (site : FormalSite Id) (family : Id) (p : Permission Id)
    (absent : family ∉ p.concrete) : permissionGuard site family p = false := by
  simp [permissionGuard, absent]

theorem native_guard_sound (s : Assembly Id) (t : Terminal Id) :
    nativeGuard s t = true ↔ ∃ origin family tail,
      t = .member origin family tail ∧
      s.handled = s.provider.operation ∧ tail = none ∧
      family = s.provider.operation.family ∧ origin = s.provider := by
  cases t with
  | other endpoint => simp [nativeGuard]
  | member origin family tail =>
    simp only [nativeGuard, decide_eq_true_eq]
    constructor
    · intro checked
      exact ⟨origin, family, tail, rfl, checked⟩
    · rintro ⟨o, f, t, equal, checked⟩
      cases equal
      exact checked

theorem other_boundary_rejected (s : Assembly Id) (o : Origin Id) (f : Id) (tail : Option Id)
    (different : o.occurrence ≠ s.provider.occurrence) :
    nativeGuard s (.member o f tail) = false := by
  have no : o ≠ s.provider := fun eq => different (congrArg Origin.occurrence eq)
  simp [nativeGuard, no]

theorem other_operation_rejected (s : Assembly Id) (o : Origin Id) (f : Id) (tail : Option Id)
    (different : o.operation ≠ s.provider.operation) :
    nativeGuard s (.member o f tail) = false := by
  have no : o ≠ s.provider := fun eq => different (congrArg Origin.operation eq)
  simp [nativeGuard, no]

theorem symbolic_not_suppressed (s : Assembly Id) (o : Origin Id) (f tail : Id) :
    nativeGuard s (.member o f (some tail)) = false := by
  simp [nativeGuard]

/-- Pure terminal refinement: it adds no member from permission metadata.
Actual traversal/constraint availability is treated separately below. -/
def residual (guard : Terminal Id → Bool) (input : List (Terminal Id)) : List (Terminal Id) :=
  input.filter fun t => !guard t

omit [DecidableEq Id] in
theorem empty_inflow (guard : Terminal Id → Bool) : residual guard [] = [] := rfl

omit [DecidableEq Id] in
theorem residual_exact (guard : Terminal Id → Bool) (input : List (Terminal Id)) (t : Terminal Id) :
    t ∈ residual guard input ↔ t ∈ input ∧ guard t = false := by
  simp [residual]

omit [DecidableEq Id] in
theorem unmatched_preserved (guard : Terminal Id → Bool) (input : List (Terminal Id))
    (t : Terminal Id) (arrived : t ∈ input) (unmatched : guard t = false) :
    t ∈ residual guard input := (residual_exact guard input t).mpr ⟨arrived, unmatched⟩

omit [DecidableEq Id] in
theorem no_permission_injection (guard : Terminal Id → Bool) (input : List (Terminal Id))
    (t : Terminal Id) (out : t ∈ residual guard input) : t ∈ input :=
  ((residual_exact guard input t).mp out).1

theorem same_family_other_boundary_preserved
    (s : Assembly Id) (input : List (Terminal Id)) (o : Origin Id) (tail : Option Id)
    (arrived : Terminal.member o s.provider.operation.family tail ∈ input)
    (different : o.occurrence ≠ s.provider.occurrence) :
    Terminal.member o s.provider.operation.family tail ∈ residual (nativeGuard s) input :=
  unmatched_preserved _ _ _ arrived (other_boundary_rejected s o _ tail different)

omit [DecidableEq Id] in
theorem residual_append (guard : Terminal Id → Bool) (left right : List (Terminal Id)) :
    residual guard (left ++ right) = residual guard left ++ residual guard right := by
  simp [residual]

inductive Outcome where
  | suppress | forward
  deriving DecidableEq

structure FoldState (Id : Type) where
  forwarded : List (Terminal Id)
  outcomes : List (Terminal Id × Outcome)
  deriving DecidableEq

def outcome (guard : Terminal Id → Bool) (t : Terminal Id) : Outcome :=
  if guard t then .suppress else .forward

/-- Original loop's successful branch: forwarding retains the same endpoint;
outcomes are recorded once per terminal, in original order. This equation does
not verify constrain_live_effect or the prior graph traversal. -/
def step (guard : Terminal Id → Bool) (state : FoldState Id) (t : Terminal Id) : FoldState Id :=
  if guard t then ⟨state.forwarded, state.outcomes ++ [(t, .suppress)]⟩
  else ⟨state.forwarded ++ [t], state.outcomes ++ [(t, .forward)]⟩

def sourceFold (guard : Terminal Id → Bool) (input : List (Terminal Id))
    (state : FoldState Id) : FoldState Id := input.foldl (step guard) state

omit [DecidableEq Id] in
theorem fold_correspondence (guard : Terminal Id → Bool) (input : List (Terminal Id))
    (state : FoldState Id) :
    sourceFold guard input state =
      ⟨state.forwarded ++ residual guard input,
        state.outcomes ++ input.map (fun t => (t, outcome guard t))⟩ := by
  induction input generalizing state with
  | nil => simp [sourceFold, residual]
  | cons t ts ih =>
    simp only [sourceFold, List.foldl_cons]
    change sourceFold guard ts (step guard state t) = _
    rw [ih]
    cases h : guard t <;> simp [step, residual, outcome, h, List.append_assoc]

theorem native_fold_correspondence (s : Assembly Id) (input : List (Terminal Id)) :
    sourceFold (nativeGuard s) input ⟨[], []⟩ =
      ⟨residual (nativeGuard s) input,
        input.map (fun t => (t, outcome (nativeGuard s) t))⟩ := by
  simpa using fold_correspondence (nativeGuard s) input ⟨[], []⟩

theorem native_fold_other_boundary (s : Assembly Id) (input : List (Terminal Id))
    (o : Origin Id) (tail : Option Id)
    (arrived : Terminal.member o s.provider.operation.family tail ∈ input)
    (different : o.occurrence ≠ s.provider.occurrence) :
    Terminal.member o s.provider.operation.family tail ∈
      (sourceFold (nativeGuard s) input ⟨[], []⟩).forwarded := by
  rw [native_fold_correspondence]
  exact same_family_other_boundary_preserved s input o tail arrived different

/-- Fallibility is a separate channel: none means traversal unavailable.
No partial list is accepted. Some [] is distinguished from unavailable. The
actual R38 source rejects an empty terminal list, modeled explicitly here. -/
def admittedFold (s : Assembly Id) : Option (List (Terminal Id)) → Option (FoldState Id)
  | none => none
  | some [] => none
  | some (t :: ts) => some (sourceFold (nativeGuard s) (t :: ts) ⟨[], []⟩)

theorem unavailable_no_partial (s : Assembly Id) : admittedFold s none = none := rfl

theorem actual_empty_unavailable (s : Assembly Id) : admittedFold s (some []) = none := rfl

theorem admitted_exact (s : Assembly Id) (input : List (Terminal Id)) (state : FoldState Id) :
    admittedFold s (some input) = some state ↔
      input ≠ [] ∧ state =
        ⟨residual (nativeGuard s) input,
          input.map (fun t => (t, outcome (nativeGuard s) t))⟩ := by
  cases input with
  | nil => simp [admittedFold]
  | cons t ts => simp [admittedFold, native_fold_correspondence, eq_comm]

/-- Direct empty-inflow application to the loop, distinct from its source
admission guard, which currently reports unavailable on empty terminals. -/
theorem native_fold_empty (s : Assembly Id) :
    sourceFold (nativeGuard s) [] ⟨[], []⟩ = ⟨[], []⟩ := rfl

/-- Exact obstruction: native suppression does not consult the permission
inventory. This is not an accepted source execution counterexample. It proves
that the current guard alone cannot establish the missing permission premise. -/
theorem native_suppresses_without_permission (o : Origin Id) :
    nativeGuard ⟨o, o.operation⟩ (.member o o.operation.family none) = true ∧
    ¬ ∃ p ∈ ([] : List (Permission Id)),
      permissionGuard p.site o.operation.family p = true := by
  simp [nativeGuard]

/-- Fully concrete guard-independence countermodel. This refutes the claim that
nativeGuard by itself certifies a retained permission; it does not claim native
reachability of these abstract records. -/
theorem concrete_missing_join :
    let op : Operation Nat := ⟨7, 11⟩
    let origin : Origin Nat := ⟨13, op⟩
    nativeGuard ⟨origin, op⟩ (.member origin 7 none) = true ∧
      ¬ ∃ p ∈ ([] : List (Permission Nat)), permissionGuard p.site 7 p = true := by
  exact native_suppresses_without_permission ⟨13, ⟨7, 11⟩⟩

end YulangClosure.EffectPermissionResidualR38
