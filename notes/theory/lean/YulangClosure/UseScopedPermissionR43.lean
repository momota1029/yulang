import YulangClosure.NativeIncidenceAdapterR42

/-!
R43 conditional read-only binding model. `permissions` must be the complete
owning FormalEntryPermission vector extracted from the pinned Rust state;
`Request` must be read from the authentic registration/action/annotation, and
`Certificate` must be the R42 native certificate for the same route. These
source-extraction equations are premises, not a verified Rust interpreter.
The full ordered permission record is retained as one witness. No row or Term
injectivity, arrival, consumer, propagation, Catch or subtraction is asserted.
-/
namespace YulangClosure.UseScopedPermissionR43

open LambdaArgumentEffectIncidenceR41
open NativeIncidenceAdapterR42

structure Request (Id : Type) where
  origin : Label Id
  annotationPosition : Id
  rowPosition : Id

def request {Id : Type} (a : ComputationPermissionEntryR39.Action Id)
    (f : ComputationPermissionEntryR39.Registration Id)
    (r : ComputationPermissionEntryR39.Row Id) (port : Id) : Request Id :=
  ⟨label a f port, a.annotation.position, r.position⟩

structure Binding (Id Term Row DefinitionUse ContextUse : Type) where
  permission : ComputationPermissionEntryR39.Permission Id
  incidence : Certificate Id Term Row DefinitionUse ContextUse
  deriving DecidableEq

variable {Id Term Row DefinitionUse ContextUse : Type}
  [DecidableEq Id]
  [DecidableEq DefinitionUse] [DecidableEq ContextUse]

/-- Filter by authentic registration before checking identity, so an ambiguous
registration cannot be hidden by a second record's mismatched payload. -/
def selected (permissions : List (ComputationPermissionEntryR39.Permission Id))
    (registration : Nat) : List (ComputationPermissionEntryR39.Permission Id) :=
  permissions.filter (fun p => p.registration == registration)

def lookup (permissions : List (ComputationPermissionEntryR39.Permission Id))
    (registration : Nat) : Option (ComputationPermissionEntryR39.Permission Id) :=
  match selected permissions registration with
  | [p] => some p
  | _ => none

omit [DecidableEq Id] in
theorem lookup_iff (permissions : List (ComputationPermissionEntryR39.Permission Id))
    (registration : Nat) (p : ComputationPermissionEntryR39.Permission Id) :
    lookup permissions registration = some p ↔ selected permissions registration = [p] := by
  generalize hs : selected permissions registration = found
  cases found with
  | nil => simp [lookup, hs]
  | cons first rest =>
    cases rest with
    | nil => simp [lookup, hs]
    | cons second tail => simp [lookup, hs]

/-- Every retained permission coordinate is checked against its source request;
Lambda and graph/native route identity are checked by full certificate label.
The use pair includes the exact DefinitionUseId and FreshUse context. -/
def Matches (req : Request Id) (use : Use DefinitionUse ContextUse)
    (p : ComputationPermissionEntryR39.Permission Id)
    (c : Certificate Id Term Row DefinitionUse ContextUse) : Prop :=
  p.registration = req.origin.registration ∧ p.parameter = req.origin.recipe ∧
  p.formalIdentity = req.origin.formal ∧ p.occurrence = req.origin.occurrence ∧
  p.owner = req.origin.owner ∧ p.scope = req.origin.scope ∧
  p.annotationPosition = req.annotationPosition ∧ p.rowPosition = req.rowPosition ∧
  p.entry = req.origin.entry ∧ c.origin = req.origin ∧ c.use = use

instance (req : Request Id) (use : Use DefinitionUse ContextUse)
    (p : ComputationPermissionEntryR39.Permission Id)
    (c : Certificate Id Term Row DefinitionUse ContextUse) :
    Decidable (Matches req use p c) := by unfold Matches; infer_instance

def bind (permissions : List (ComputationPermissionEntryR39.Permission Id))
    (req : Request Id) (use : Use DefinitionUse ContextUse)
    (c : Certificate Id Term Row DefinitionUse ContextUse) :
    Option (Binding Id Term Row DefinitionUse ContextUse) := do
  let p ← lookup permissions req.origin.registration
  if Matches req use p c then some ⟨p, c⟩ else none

theorem accepted_iff (permissions : List (ComputationPermissionEntryR39.Permission Id))
    (req : Request Id) (use : Use DefinitionUse ContextUse)
    (c : Certificate Id Term Row DefinitionUse ContextUse)
    (out : Binding Id Term Row DefinitionUse ContextUse) :
    bind permissions req use c = some out ↔
      selected permissions req.origin.registration = [out.permission] ∧
      Matches req use out.permission c ∧ out.incidence = c := by
  constructor
  · intro accepted
    cases hl : lookup permissions req.origin.registration with
    | none => simp [bind, hl] at accepted
    | some p =>
      by_cases hm : Matches req use p c
      · have equal : (⟨p, c⟩ : Binding Id Term Row DefinitionUse ContextUse) = out := by
          simpa [bind, hl, hm] using accepted
        subst out
        exact ⟨(lookup_iff permissions req.origin.registration p).mp hl, hm, rfl⟩
      · simp [bind, hl, hm] at accepted
  · rintro ⟨hs, hm, hc⟩
    have hl := (lookup_iff permissions req.origin.registration out.permission).mpr hs
    cases out with
    | mk permission incidence =>
      dsimp at hc
      subst incidence
      simp [bind, hl, hm]

/-- Full payload equality, including all source coordinates and concrete list.
No reconstructed, sorted, deduplicated or filtered payload is published. -/
theorem payload_preserved (permissions : List (ComputationPermissionEntryR39.Permission Id))
    (req : Request Id) (use : Use DefinitionUse ContextUse)
    (c : Certificate Id Term Row DefinitionUse ContextUse)
    (out : Binding Id Term Row DefinitionUse ContextUse)
    (accepted : bind permissions req use c = some out) :
    lookup permissions req.origin.registration = some out.permission ∧
      out.incidence = c ∧ out.permission ∈ permissions := by
  obtain ⟨hs, _, hc⟩ := (accepted_iff permissions req use c out).mp accepted
  refine ⟨(lookup_iff permissions req.origin.registration out.permission).mpr hs, hc, ?_⟩
  have member : out.permission ∈ selected permissions req.origin.registration := by rw [hs]; simp
  exact (List.mem_filter.mp member).1

theorem ordered_payload (permissions : List (ComputationPermissionEntryR39.Permission Id))
    (req : Request Id) (use : Use DefinitionUse ContextUse)
    (c : Certificate Id Term Row DefinitionUse ContextUse)
    (out : Binding Id Term Row DefinitionUse ContextUse)
    (p : ComputationPermissionEntryR39.Permission Id)
    (unique : selected permissions req.origin.registration = [p])
    (accepted : bind permissions req use c = some out) :
    out.permission = p ∧ out.permission.concrete = p.concrete ∧
      ∀ (i : Nat), out.permission.concrete[i]? = p.concrete[i]? := by
  obtain ⟨hs, _, _⟩ := (accepted_iff permissions req use c out).mp accepted
  have hp : out.permission = p := by simpa using hs.symm.trans unique
  exact ⟨hp, congrArg ComputationPermissionEntryR39.Permission.concrete hp,
    fun i => congrArg (fun q => q.concrete[i]?) hp⟩

theorem missing_or_ambiguous_rejected
    (permissions : List (ComputationPermissionEntryR39.Permission Id))
    (req : Request Id) (use : Use DefinitionUse ContextUse)
    (c : Certificate Id Term Row DefinitionUse ContextUse)
    (unavailable : lookup permissions req.origin.registration = none) :
    bind permissions req use c = none := by simp [bind, unavailable]

theorem absent_or_multiple_rejected
    (permissions : List (ComputationPermissionEntryR39.Permission Id))
    (req : Request Id) (use : Use DefinitionUse ContextUse)
    (c : Certificate Id Term Row DefinitionUse ContextUse)
    (shape : selected permissions req.origin.registration = [] ∨
      ∃ p q tail, selected permissions req.origin.registration = p :: q :: tail) :
    bind permissions req use c = none := by
  apply missing_or_ambiguous_rejected
  rcases shape with empty | ⟨p, q, tail, multiple⟩
  · simp [lookup, empty]
  · simp [lookup, multiple]

/-- Includes foreign/mismatched owner, recipe/formal, occurrence, scope,
annotation/row, entry, full registration/Lambda label and exact use/context. -/
theorem mismatch_rejected (permissions : List (ComputationPermissionEntryR39.Permission Id))
    (req : Request Id) (use : Use DefinitionUse ContextUse)
    (c : Certificate Id Term Row DefinitionUse ContextUse)
    (p : ComputationPermissionEntryR39.Permission Id)
    (unique : selected permissions req.origin.registration = [p])
    (mismatch : p.registration ≠ req.origin.registration ∨ p.parameter ≠ req.origin.recipe ∨
      p.formalIdentity ≠ req.origin.formal ∨ p.occurrence ≠ req.origin.occurrence ∨
      p.owner ≠ req.origin.owner ∨ p.scope ≠ req.origin.scope ∨
      p.annotationPosition ≠ req.annotationPosition ∨ p.rowPosition ≠ req.rowPosition ∨
      p.entry ≠ req.origin.entry ∨ c.origin ≠ req.origin ∨
      c.use.definitionUse ≠ use.definitionUse ∨ c.use.contextUse ≠ use.contextUse) :
    bind permissions req use c = none := by
  have invalid : ¬ Matches req use p c := by
    rintro ⟨hr, hp, hf, ho, hw, hs, ha, hn, he, hl, hu⟩
    have hd := congrArg Use.definitionUse hu
    have hc := congrArg Use.contextUse hu
    rcases mismatch with h | h | h | h | h | h | h | h | h | h | h | h <;> contradiction
  have hl := (lookup_iff permissions req.origin.registration p).mpr unique
  simp [bind, hl, invalid]

theorem shared_images_distinct_bindings
    (permissions : List (ComputationPermissionEntryR39.Permission Id))
    (left right : Request Id) (use : Use DefinitionUse ContextUse)
    (lc rc : Certificate Id Term Row DefinitionUse ContextUse)
    (lo ro : Binding Id Term Row DefinitionUse ContextUse)
    (la : bind permissions left use lc = some lo)
    (ra : bind permissions right use rc = some ro)
    (different : left.origin.registration ≠ right.origin.registration)
    (sameFunction : lc.function = rc.function) (sameChild : lc.child = rc.child)
    (sameRow : lc.mappedRow = rc.mappedRow) :
    lo.incidence.function = ro.incidence.function ∧
      lo.incidence.child = ro.incidence.child ∧
      lo.incidence.mappedRow = ro.incidence.mappedRow ∧
      lo.permission.registration ≠ ro.permission.registration ∧ lo.permission ≠ ro.permission := by
  obtain ⟨_, lm, le⟩ := (accepted_iff permissions left use lc lo).mp la
  obtain ⟨_, rm, re⟩ := (accepted_iff permissions right use rc ro).mp ra
  have hd : lo.permission.registration ≠ ro.permission.registration := by
    rw [lm.1, rm.1]
    exact different
  exact ⟨le ▸ re ▸ sameFunction, le ▸ re ▸ sameChild, le ▸ re ▸ sameRow,
    hd, fun equal => hd (congrArg ComputationPermissionEntryR39.Permission.registration equal)⟩

/-- Application to the original R39→R41→R42 chain with ONE permission witness.
`owningTable` is exact Rust table extraction/completeness, not a proven property
of Rust. All R39 validation and R42 actual-read premises remain unchanged. -/
theorem constructed_entry_binding [DecidableEq Term] [DecidableEq Row]
    (e : ComputationPermissionEntryR39.Inputs Id)
    (a : ComputationPermissionEntryR39.Action Id)
    (f : ComputationPermissionEntryR39.Registration Id)
    (r : ComputationPermissionEntryR39.Row Id) (port : Id)
    (s : ComputationPermissionEntryR39.State Id)
    (hf : e.formals[a.registration]? = some f) (hr : a.annotation.row = some r)
    (hp : f.entry = some port) (valid : ComputationPermissionEntryR39.Valid e a f r)
    (nonempty : r.concrete ≠ [])
    (negativeEffect : Id → Term) (function argument returned result : Term)
    (nodes : Term → Nat) (rowIndexes : Id → Nat)
    (use : Use DefinitionUse ContextUse) (terms : Nat → Term) (rows : Nat → Row)
    (reads : Reads Term Row DefinitionUse ContextUse) (ordinal : Nat)
    (probe : Probe Term Row) (c : Certificate Id Term Row DefinitionUse ContextUse)
    (accepted : extract (capture nodes rowIndexes
      (constructLambda a f port negativeEffect function argument returned result))
      use reads ordinal probe = some c)
    (functionRead : reads.terms (nodes function) = some (terms (nodes function)))
    (childRead : reads.terms (nodes (negativeEffect port)) = some (terms (nodes (negativeEffect port))))
    (rowRead : reads.rows (rowIndexes port) = some (rows (rowIndexes port)))
    (permissions : List (ComputationPermissionEntryR39.Permission Id))
    (owningTable : ∀ p, ComputationPermissionEntryR39.permissionFor a f r port = some p →
      selected permissions a.registration = [p]) :
    ∃ p, ComputationPermissionEntryR39.prepare e a = some (f, r, port) ∧
      ComputationPermissionEntryR39.permissionFor a f r port = some p ∧
      ComputationPermissionEntryR39.publish a f r port true s = some
        ⟨s.permissions ++ [p], s.links ++ ComputationPermissionEntryR39.symbolicLinks a r port, s.inflow⟩ ∧
      bind permissions (request a f r port) use c = some ⟨p, c⟩ ∧
      p.concrete = r.concrete ∧ c.function = terms (nodes function) ∧
      c.child = terms (nodes (negativeEffect port)) ∧
      c.mappedRow = rows (rowIndexes port) ∧
      reads.nativeFunction c.function = some probe.nativePorts ∧
      probe.nativePorts.argumentEffect = c.child := by
  obtain ⟨p, prepared, retained, published, concrete, _, _, _, _, _, fn, ch, row, native, field⟩ :=
    constructed_entry_to_native e a f r port s hf hr hp valid nonempty negativeEffect
      function argument returned result nodes rowIndexes use terms rows reads ordinal probe c
      accepted functionRead childRead rowRead
  obtain ⟨_, _, _, _, _, reg, recipe, formal, occurrence, owner, scope, ann, rowpos, entry, _⟩ :=
    ComputationPermissionEntryR39.exact_row_retained e a p f r port prepared retained
  obtain ⟨_, origin⟩ := (extraction_iff _ use reads ordinal probe c).mp accepted
  have originExact : c.origin = label a f port := congrArg Certificate.origin origin
  have useExact : c.use = use := congrArg Certificate.use origin
  have matched : Matches (request a f r port) use p c :=
    ⟨reg, recipe, formal, occurrence, owner.trans valid.1.symm,
      scope.trans valid.2.2.1.symm, ann, rowpos, entry, originExact, useExact⟩
  have bound := (accepted_iff permissions (request a f r port) use c ⟨p, c⟩).mpr
    ⟨owningTable p retained, matched, rfl⟩
  exact ⟨p, prepared, retained, published, bound, concrete, fn, ch, row, native, field⟩

/-- Fully instantiated finite cases, not source/runtime receipts. -/
def witnessPermission (registration : Nat) : ComputationPermissionEntryR39.Permission Nat :=
  ⟨registration, 40, 30, 50, 10, 60, 80, 90, 70, [7, 7, 11]⟩

def witnessRequest (registration : Nat) : Request Nat :=
  ⟨(witnessCaptured registration).origin, 80, 90⟩

def witnessCertificate (registration : Nat) : Certificate Nat Nat Nat Nat Nat :=
  certificate (witnessCaptured registration) ⟨100, 200⟩ witnessProbe

theorem shared_images_and_duplicate_order_witness :
    let ps := [witnessPermission 0, witnessPermission 1]
    bind ps (witnessRequest 0) ⟨100, 200⟩ (witnessCertificate 0) =
      some ⟨witnessPermission 0, witnessCertificate 0⟩ ∧
    bind ps (witnessRequest 1) ⟨100, 200⟩ (witnessCertificate 1) =
      some ⟨witnessPermission 1, witnessCertificate 1⟩ ∧
    (witnessCertificate 0).function = (witnessCertificate 1).function ∧
    (witnessCertificate 0).child = (witnessCertificate 1).child ∧
    (witnessCertificate 0).mappedRow = (witnessCertificate 1).mappedRow ∧
    witnessPermission 0 ≠ witnessPermission 1 ∧
    (witnessPermission 0).concrete = [7, 7, 11] := by decide

theorem foreign_and_ambiguous_witness :
    let ps := [witnessPermission 0]
    bind [] (witnessRequest 0) ⟨100, 200⟩ (witnessCertificate 0) = none ∧
    bind [witnessPermission 0, witnessPermission 0] (witnessRequest 0)
      ⟨100, 200⟩ (witnessCertificate 0) = none ∧
    bind ps (witnessRequest 0) ⟨101, 200⟩ (witnessCertificate 0) = none ∧
    bind ps (witnessRequest 0) ⟨100, 201⟩ (witnessCertificate 0) = none ∧
    bind ps (witnessRequest 0) ⟨100, 200⟩ (witnessCertificate 1) = none ∧
    bind ps { witnessRequest 0 with annotationPosition := 81 }
      ⟨100, 200⟩ (witnessCertificate 0) = none ∧
    bind ps { witnessRequest 0 with rowPosition := 91 }
      ⟨100, 200⟩ (witnessCertificate 0) = none ∧
    bind [{ witnessPermission 0 with owner := 12 }] (witnessRequest 0)
      ⟨100, 200⟩ (witnessCertificate 0) = none ∧
    bind [{ witnessPermission 0 with formalIdentity := 32 }] (witnessRequest 0)
      ⟨100, 200⟩ (witnessCertificate 0) = none ∧
    bind [{ witnessPermission 0 with scope := 62 }] (witnessRequest 0)
      ⟨100, 200⟩ (witnessCertificate 0) = none ∧
    bind ps (witnessRequest 0) ⟨100, 200⟩
      { witnessCertificate 0 with origin := { (witnessCertificate 0).origin with lambda := 21 } } = none := by
  decide

end YulangClosure.UseScopedPermissionR43
