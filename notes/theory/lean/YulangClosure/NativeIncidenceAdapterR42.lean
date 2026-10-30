import YulangClosure.LambdaArgumentEffectIncidenceR41

/-!
R42: conditional finite model of the private native-incidence extractor.
`Reads` denotes the exact retained route's partial maps and read-only native
observations. Instantiating these functions with Rust field reads, selecting
the actual registration and graph ports, and authenticating the rich R41 label
are explicit source-correspondence duties, not conclusions of this model.

`graphFunction` and `nativeFunction` return `some` only for positive Functions;
all other constructors and lookup errors give `none`. `graphRow` returns `some`
only for a Row node. A probe supplies possible decoded values, but acceptance
compares them with the actual reads. No total-map or injectivity premise is
needed for extraction. No permission consumer, provider arrival, Catch,
subtraction, allocation or verified Rust interpreter is represented.
-/
namespace YulangClosure.NativeIncidenceAdapterR42

open LambdaArgumentEffectIncidenceR41

structure Reads (Term Row DefinitionUse ContextUse : Type) where
  use : Use DefinitionUse ContextUse
  graphFunction : Nat → Option (Ports Nat)
  graphRow : Nat → Option Nat
  terms : Nat → Option Term
  rows : Nat → Option Row
  nativeFunction : Term → Option (Ports Term)

structure Probe (Term Row : Type) where
  function : Term
  child : Term
  mappedRow : Row
  nativePorts : Ports Term

structure Certificate (Id Term Row DefinitionUse ContextUse : Type) where
  origin : Label Id
  use : Use DefinitionUse ContextUse
  sourceFunction : Nat
  sourceChild : Nat
  sourceRow : Nat
  function : Term
  child : Term
  mappedRow : Row
  deriving DecidableEq

/-- `c.ports` is the actual positive graph Function projection selected at
`c.function`; `ordinal` is the separately retained child ordinal. In Rust only
registration/Lambda coordinates are stored here: identification with the full
R41 source label is an additional source extraction premise. -/
def Matches {Id Term Row DefinitionUse ContextUse : Type}
    (c : Captured Id) (supplied : Use DefinitionUse ContextUse)
    (reads : Reads Term Row DefinitionUse ContextUse) (ordinal : Nat)
    (p : Probe Term Row) : Prop :=
  reads.use = supplied ∧ ordinal = 1 ∧
    reads.graphFunction c.function = some c.ports ∧
    reads.graphRow c.ports.argumentEffect = some c.entryRow ∧
    reads.terms c.function = some p.function ∧
    reads.terms c.ports.argumentEffect = some p.child ∧
    reads.rows c.entryRow = some p.mappedRow ∧
    reads.nativeFunction p.function = some p.nativePorts ∧
    p.nativePorts.argumentEffect = p.child

instance {Id Term Row DefinitionUse ContextUse : Type}
    [DecidableEq Term] [DecidableEq Row] [DecidableEq DefinitionUse]
    [DecidableEq ContextUse] (c : Captured Id)
    (supplied : Use DefinitionUse ContextUse)
    (reads : Reads Term Row DefinitionUse ContextUse) (ordinal : Nat)
    (p : Probe Term Row) : Decidable (Matches c supplied reads ordinal p) := by
  unfold Matches
  infer_instance

def certificate {Id Term Row DefinitionUse ContextUse : Type}
    (c : Captured Id) (supplied : Use DefinitionUse ContextUse)
    (p : Probe Term Row) : Certificate Id Term Row DefinitionUse ContextUse :=
  ⟨c.origin, supplied, c.function, c.ports.argumentEffect, c.entryRow,
    p.function, p.child, p.mappedRow⟩

def extract {Id Term Row DefinitionUse ContextUse : Type}
    [DecidableEq Term] [DecidableEq Row] [DecidableEq DefinitionUse]
    [DecidableEq ContextUse] (c : Captured Id)
    (supplied : Use DefinitionUse ContextUse)
    (reads : Reads Term Row DefinitionUse ContextUse) (ordinal : Nat)
    (p : Probe Term Row) : Option (Certificate Id Term Row DefinitionUse ContextUse) :=
  if Matches c supplied reads ordinal p then some (certificate c supplied p) else none

theorem extraction_iff {Id Term Row DefinitionUse ContextUse : Type}
    [DecidableEq Term] [DecidableEq Row] [DecidableEq DefinitionUse]
    [DecidableEq ContextUse] (c : Captured Id)
    (supplied : Use DefinitionUse ContextUse)
    (reads : Reads Term Row DefinitionUse ContextUse) (ordinal : Nat)
    (p : Probe Term Row) (out : Certificate Id Term Row DefinitionUse ContextUse) :
    extract c supplied reads ordinal p = some out ↔
      Matches c supplied reads ordinal p ∧ out = certificate c supplied p := by
  unfold extract
  split <;> simp_all [eq_comm]

/-- Every accepted record uses the same graph child, native field, retained
maps and exact pair of supplied definition-use identity/context stamp. -/
theorem accepted_fields {Id Term Row DefinitionUse ContextUse : Type}
    [DecidableEq Term] [DecidableEq Row] [DecidableEq DefinitionUse]
    [DecidableEq ContextUse] (c : Captured Id)
    (supplied : Use DefinitionUse ContextUse)
    (reads : Reads Term Row DefinitionUse ContextUse) (ordinal : Nat)
    (p : Probe Term Row) (out : Certificate Id Term Row DefinitionUse ContextUse)
    (accepted : extract c supplied reads ordinal p = some out) :
    out.origin = c.origin ∧ out.sourceFunction = c.function ∧
      out.sourceChild = c.ports.argumentEffect ∧ out.sourceRow = c.entryRow ∧
      out.use.definitionUse = supplied.definitionUse ∧
      out.use.contextUse = supplied.contextUse ∧ reads.use = out.use ∧
      ordinal = 1 ∧ c.ports.children[ordinal]? = some out.sourceChild ∧
      reads.graphFunction out.sourceFunction = some c.ports ∧
      reads.graphRow out.sourceChild = some out.sourceRow ∧
      reads.terms out.sourceFunction = some out.function ∧
      reads.terms out.sourceChild = some out.child ∧
      reads.rows out.sourceRow = some out.mappedRow ∧
      reads.nativeFunction out.function = some p.nativePorts ∧
      p.nativePorts.argumentEffect = out.child := by
  obtain ⟨h, rfl⟩ := (extraction_iff c supplied reads ordinal p out).mp accepted
  rcases h with ⟨hu, ho, hg, hr, hf, hc, hm, hn, he⟩
  subst ordinal
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, hu, rfl, rfl,
    hg, hr, hf, hc, hm, hn, he⟩

/-- Covers foreign definition-use/context, wrong ordinal or graph shape,
missing/mismatched native terms/rows, non-positive native views, and an actual
Function argument-effect field different from the exact mapped child. -/
theorem reject_mismatch {Id Term Row DefinitionUse ContextUse : Type}
    [DecidableEq Term] [DecidableEq Row] [DecidableEq DefinitionUse]
    [DecidableEq ContextUse] (c : Captured Id)
    (supplied : Use DefinitionUse ContextUse)
    (reads : Reads Term Row DefinitionUse ContextUse) (ordinal : Nat)
    (p : Probe Term Row)
    (mismatch : reads.use ≠ supplied ∨ ordinal ≠ 1 ∨
      reads.graphFunction c.function ≠ some c.ports ∨
      reads.graphRow c.ports.argumentEffect ≠ some c.entryRow ∨
      reads.terms c.function ≠ some p.function ∨
      reads.terms c.ports.argumentEffect ≠ some p.child ∨
      reads.rows c.entryRow ≠ some p.mappedRow ∨
      reads.nativeFunction p.function ≠ some p.nativePorts ∨
      p.nativePorts.argumentEffect ≠ p.child) :
    extract c supplied reads ordinal p = none := by
  have invalid : ¬ Matches c supplied reads ordinal p := by
    intro h
    rcases h with ⟨hu, ho, hg, hr, hf, hc, hm, hn, he⟩
    rcases mismatch with h | h | h | h | h | h | h | h | h <;> contradiction
  simp only [extract, ite_eq_right invalid]

/-- Apply acceptance to R41's SAME shared term/row images. Only the three
relevant lookup coordinates need agree; every other map entry can be absent. -/
theorem accepted_r41_image {Id Term Row DefinitionUse ContextUse : Type}
    [DecidableEq Term] [DecidableEq Row] [DecidableEq DefinitionUse]
    [DecidableEq ContextUse] (c : Captured Id)
    (supplied : Use DefinitionUse ContextUse)
    (reads : Reads Term Row DefinitionUse ContextUse) (ordinal : Nat)
    (p : Probe Term Row) (out : Certificate Id Term Row DefinitionUse ContextUse)
    (accepted : extract c supplied reads ordinal p = some out)
    (terms : Nat → Term) (rows : Nat → Row)
    (functionRead : reads.terms c.function = some (terms c.function))
    (childRead : reads.terms c.ports.argumentEffect = some (terms c.ports.argumentEffect))
    (rowRead : reads.rows c.entryRow = some (rows c.entryRow)) :
    let image := freshen supplied terms rows c
    out.origin = image.origin ∧ out.use = image.use ∧
      out.sourceFunction = image.sourceFunction ∧
      out.sourceChild = image.sourceArgumentEffect ∧
      out.function = image.function ∧
      image.ports.children[1]? = some out.child ∧ out.mappedRow = image.entryRow ∧
      reads.nativeFunction out.function = some p.nativePorts ∧
      p.nativePorts.argumentEffect = out.child := by
  obtain ⟨h, rfl⟩ := (extraction_iff c supplied reads ordinal p out).mp accepted
  rcases h with ⟨_, _, _, _, hf, hc, hr, hn, he⟩
  have ef := Option.some.inj (hf.symm.trans functionRead)
  have ec := Option.some.inj (hc.symm.trans childRead)
  have er := Option.some.inj (hr.symm.trans rowRead)
  exact ⟨rfl, rfl, rfl, rfl, ef, congrArg some ec.symm, er, hn, he⟩

/-- Shared native Function, child and row images do not merge registrations.
The maps need not be injective and no equality-only permission follows. -/
theorem shared_images_distinct_labels {Id Term Row DefinitionUse ContextUse : Type}
    [DecidableEq Term] [DecidableEq Row] [DecidableEq DefinitionUse]
    [DecidableEq ContextUse] (left right : Captured Id)
    (supplied : Use DefinitionUse ContextUse)
    (reads : Reads Term Row DefinitionUse ContextUse) (li ri : Nat)
    (lp rp : Probe Term Row)
    (lo ro : Certificate Id Term Row DefinitionUse ContextUse)
    (la : extract left supplied reads li lp = some lo)
    (ra : extract right supplied reads ri rp = some ro)
    (different : left.origin.registration ≠ right.origin.registration)
    (sharedFunction : lp.function = rp.function)
    (sharedChild : lp.child = rp.child) (sharedRow : lp.mappedRow = rp.mappedRow) :
    lo.function = ro.function ∧ lo.child = ro.child ∧ lo.mappedRow = ro.mappedRow ∧
      lo.origin ≠ ro.origin ∧ lo ≠ ro := by
  obtain ⟨_, rfl⟩ := (extraction_iff left supplied reads li lp lo).mp la
  obtain ⟨_, rfl⟩ := (extraction_iff right supplied reads ri rp ro).mp ra
  have labels : left.origin ≠ right.origin := fun h => different (congrArg Label.registration h)
  refine ⟨sharedFunction, sharedChild, sharedRow, labels, ?_⟩
  intro equal
  exact labels (congrArg Certificate.origin equal)

/-- Compose with R41's original R39 application without changing its validation
premises or choosing a second permission witness. Actual source extraction and
the three lookup/image equations are still explicit premises. -/
theorem constructed_entry_to_native {Id Term Row DefinitionUse ContextUse : Type}
    [DecidableEq Id] [DecidableEq Term] [DecidableEq Row]
    [DecidableEq DefinitionUse] [DecidableEq ContextUse]
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
    (supplied : Use DefinitionUse ContextUse) (terms : Nat → Term) (rows : Nat → Row)
    (reads : Reads Term Row DefinitionUse ContextUse) (ordinal : Nat)
    (probe : Probe Term Row) (out : Certificate Id Term Row DefinitionUse ContextUse)
    (accepted : extract (capture nodes rowIndexes
      (constructLambda a f port negativeEffect function argument returned result))
      supplied reads ordinal probe = some out)
    (functionRead : reads.terms (nodes function) = some (terms (nodes function)))
    (childRead : reads.terms (nodes (negativeEffect port)) = some (terms (nodes (negativeEffect port))))
    (rowRead : reads.rows (rowIndexes port) = some (rows (rowIndexes port))) :
    ∃ permission,
      ComputationPermissionEntryR39.prepare e a = some (f, r, port) ∧
      ComputationPermissionEntryR39.permissionFor a f r port = some permission ∧
      ComputationPermissionEntryR39.publish a f r port true s = some
        ⟨s.permissions ++ [permission],
          s.links ++ ComputationPermissionEntryR39.symbolicLinks a r port, s.inflow⟩ ∧
      permission.concrete = r.concrete ∧
      permission.registration = out.origin.registration ∧ permission.owner = out.origin.owner ∧
      permission.occurrence = out.origin.occurrence ∧ permission.entry = out.origin.entry ∧
      out.use = supplied ∧ out.function = terms (nodes function) ∧
      out.child = terms (nodes (negativeEffect port)) ∧
      out.mappedRow = rows (rowIndexes port) ∧
      reads.nativeFunction out.function = some probe.nativePorts ∧
      probe.nativePorts.argumentEffect = out.child := by
  obtain ⟨permission, prepared, retained, published, concrete,
    registration, owner, occurrence, entry, _⟩ :=
    entry_to_exact_use e a f r port s hf hr hp valid nonempty negativeEffect
      function argument returned result nodes rowIndexes supplied terms rows
  obtain ⟨origin, useExact, _, _, functionExact, childExact, rowExact, native, field⟩ :=
    accepted_r41_image (capture nodes rowIndexes
      (constructLambda a f port negativeEffect function argument returned result))
      supplied reads ordinal probe out accepted terms rows functionRead childRead rowRead
  have child := Option.some.inj childExact
  exact ⟨permission, prepared, retained, published, concrete,
    registration.trans (congrArg Label.registration origin.symm),
    owner.trans (congrArg Label.owner origin.symm),
    occurrence.trans (congrArg Label.occurrence origin.symm),
    entry.trans (congrArg Label.entry origin.symm), useExact, functionExact,
    child.symm, rowExact, native, field⟩

/-- A fully instantiated successful non-node-1 child example. The same native
Function, child and row support two records distinguished by registration. -/
def witnessCaptured (registration : Nat) : Captured Nat :=
  ⟨⟨10, registration, 20, 30, 40, 50, 60, 70⟩, 2, ⟨3, 7, 8, 9⟩, 5⟩

def witnessReads : Reads Nat Nat Nat Nat :=
  ⟨⟨100, 200⟩,
    fun n => if n = 2 then some ⟨3, 7, 8, 9⟩ else none,
    fun n => if n = 7 then some 5 else none,
    fun n => if n = 2 then some 21 else if n = 7 then some 31 else none,
    fun n => if n = 5 then some 51 else none,
    fun n => if n = 21 then some ⟨30, 31, 32, 33⟩ else none⟩

def witnessProbe : Probe Nat Nat := ⟨21, 31, 51, ⟨30, 31, 32, 33⟩⟩

theorem shared_native_witness :
    extract (witnessCaptured 0) ⟨100, 200⟩ witnessReads 1 witnessProbe =
      some (certificate (witnessCaptured 0) ⟨100, 200⟩ witnessProbe) ∧
    extract (witnessCaptured 1) ⟨100, 200⟩ witnessReads 1 witnessProbe =
      some (certificate (witnessCaptured 1) ⟨100, 200⟩ witnessProbe) ∧
    (certificate (witnessCaptured 0) (Use.mk 100 200) witnessProbe).origin ≠
      (certificate (witnessCaptured 1) (Use.mk 100 200) witnessProbe).origin := by
  simp [extract, Matches, witnessCaptured, witnessReads, witnessProbe, certificate]

theorem foreign_and_native_mismatch_witness :
    extract (witnessCaptured 0) ⟨101, 200⟩ witnessReads 1 witnessProbe = none ∧
    extract (witnessCaptured 0) ⟨100, 201⟩ witnessReads 1 witnessProbe = none ∧
    extract (witnessCaptured 0) ⟨100, 200⟩ witnessReads 1
      { witnessProbe with nativePorts := ⟨30, 99, 32, 33⟩ } = none ∧
    extract (witnessCaptured 0) ⟨100, 200⟩ witnessReads 1
      { witnessProbe with child := 99 } = none := by
  simp [extract, Matches, witnessCaptured, witnessReads, witnessProbe,
    LambdaArgumentEffectIncidenceR41.Use.mk.injEq]

end YulangClosure.NativeIncidenceAdapterR42
