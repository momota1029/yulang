import YulangClosure.ComputationPermissionEntryR39

/-!
R45 conditional finite Internal-incidence model. This certificate has no
FreshRoute, FreshUse context, mapped row, provider arrival or consumer meaning.
Inputs are exact partial owner reads at the source revision recorded in the
handoff, not arbitrary equal canonical images. A supplied Probe is accepted
only after comparison with all owning records and source/native observations.
Instantiating those reads with Rust, and proving their completeness, is a
separate source-correspondence obligation. No Rust execution is asserted.
-/
namespace YulangClosure.InternalPermissionIncidenceR45

open ComputationPermissionEntryR39

structure UseId (Artifact Id : Type) where
  artifact : Artifact
  occurrence : Id
  deriving DecidableEq

inductive Kind where
  | internal | incomingInt | incomingBottomTrivial | incomingStructured
  deriving DecidableEq

structure Construction (Id Term : Type) where
  registration : Nat
  lambda : Id
  function : Term
  entry : Id
  deriving DecidableEq

structure Plan (Id Term : Type) where
  sourceOwner : Id
  targetOwner : Id
  targetRootComponent : Nat
  useValueComponent : Nat
  targetRoot : Term
  useValue : Term
  deriving DecidableEq

structure Receipt (Artifact Id Fact : Type) where
  use : UseId Artifact Id
  kind : Kind
  fact : Option Fact
  deriving DecidableEq

structure Query (Artifact Id : Type) where
  use : UseId Artifact Id
  sourceOwner : Id
  targetOwner : Id
  registration : Nat
  lambda : Id
  annotationPosition : Id
  rowPosition : Id
  deriving DecidableEq

structure Probe (Artifact Id Term Fact : Type) where
  formal : Registration Id
  registeredRoot : Term
  recipeRootComponent : Nat
  construction : Construction Id Term
  permission : Permission Id
  plan : Plan Id Term
  receipt : Receipt Artifact Id Fact
  fact : Fact
  child : Term
  deriving DecidableEq

structure Inputs (Artifact Id Term Fact : Type) where
  artifact : Artifact
  source : ComputationPermissionEntryR39.Inputs Id
  formals : Nat → Option (Registration Id × Term)
  constructions : List (Construction Id Term)
  permissions : List (Permission Id)
  receipts : List (Receipt Artifact Id Fact)
  plan : UseId Artifact Id → Option (Plan Id Term)
  /-- Actual admitted route-fact endpoints, not an unadmitted planned pair. -/
  routeFact : Fact → Option (Id × Term × Term)
  /-- Actual LambdaRecipe formal_registration and root_component fields. -/
  lambdaRecipe : Id → Option (Nat × Nat)
  componentTerm : Nat → Option Term
  /-- Actual admitted source-Lambda slot-2 fact endpoints. -/
  lambdaFact : Id → Option (Term × Term)
  /-- Returns some only for the actual positive Function's argument-effect. -/
  positiveFunctionChild : Term → Option Term
  /-- Returns some only for an actual negative effect-variable entry term. -/
  negativeEntry : Term → Option Id

structure Certificate (Artifact Id Term Fact : Type) where
  use : UseId Artifact Id
  sourceOwner : Id
  targetOwner : Id
  registration : Nat
  formal : Registration Id
  lambda : Id
  function : Term
  argumentEffect : Term
  originalRoot : Term
  useValue : Term
  fact : Fact
  permission : Permission Id
  deriving DecidableEq

variable {Artifact Id Term Fact : Type}
  [DecidableEq Artifact] [DecidableEq Id] [DecidableEq Term] [DecidableEq Fact]

def constructionsFor (e : Inputs Artifact Id Term Fact) (registration : Nat) :=
  e.constructions.filter (fun c => c.registration == registration)

def permissionsFor (e : Inputs Artifact Id Term Fact) (registration : Nat) :=
  e.permissions.filter (fun p => p.registration == registration)

def receiptsFor (e : Inputs Artifact Id Term Fact) (use : UseId Artifact Id) :=
  e.receipts.filter (fun r => r.use == use)

/-- Singleton selection comes from the owning registration/use labels BEFORE
any native equality check. Foreign equal images cannot select a witness. -/
def OwnerReads (e : Inputs Artifact Id Term Fact) (q : Query Artifact Id)
    (p : Probe Artifact Id Term Fact) : Prop :=
  e.formals q.registration = some (p.formal, p.registeredRoot) ∧
  e.source.formals[q.registration]? = some p.formal ∧
  constructionsFor e q.registration = [p.construction] ∧
  permissionsFor e q.registration = [p.permission] ∧
  receiptsFor e q.use = [p.receipt] ∧ e.plan q.use = some p.plan ∧
  sourceLambda e.source p.formal = some (q.lambda, p.formal.parameter) ∧
  e.routeFact p.fact = some (q.use.occurrence, p.plan.targetRoot, p.plan.useValue) ∧
  e.lambdaFact q.lambda = some (p.construction.function, p.registeredRoot) ∧
  e.positiveFunctionChild p.construction.function = some p.child ∧
  e.negativeEntry p.child = some p.construction.entry ∧
  e.lambdaRecipe q.lambda = some (q.registration, p.recipeRootComponent) ∧
  e.componentTerm p.plan.targetRootComponent = some p.plan.targetRoot ∧
  e.componentTerm p.plan.useValueComponent = some p.plan.useValue

/-- Complete identity checks; receiver source owner and target owner stay
separate. Constructor entry uses the ORIGINAL key, not its representative. -/
def Identity (e : Inputs Artifact Id Term Fact) (q : Query Artifact Id)
    (p : Probe Artifact Id Term Fact) : Prop :=
  q.use.artifact = e.artifact ∧ p.plan.sourceOwner = q.sourceOwner ∧
  p.plan.targetOwner = q.targetOwner ∧ p.formal.owner = q.targetOwner ∧
  p.formal.role = .computation ∧ p.formal.entry = some p.construction.entry ∧
  p.registeredRoot = p.plan.targetRoot ∧ p.construction.registration = q.registration ∧
  p.construction.lambda = q.lambda ∧ p.receipt.use = q.use ∧
  p.receipt.kind = .internal ∧ p.receipt.fact = some p.fact ∧
  p.permission.registration = q.registration ∧ p.permission.parameter = p.formal.recipe ∧
  p.permission.formalIdentity = p.formal.parameter ∧ p.permission.owner = p.formal.owner ∧
  p.permission.occurrence = q.lambda ∧ p.permission.scope = p.formal.scope ∧
  p.permission.annotationPosition = q.annotationPosition ∧
  p.permission.rowPosition = q.rowPosition ∧ p.permission.entry = p.construction.entry ∧
  p.permission.concrete ≠ [] ∧ p.recipeRootComponent = p.plan.targetRootComponent

instance (e : Inputs Artifact Id Term Fact) (q : Query Artifact Id)
    (p : Probe Artifact Id Term Fact) : Decidable (OwnerReads e q p) := by
  unfold OwnerReads; infer_instance

instance (e : Inputs Artifact Id Term Fact) (q : Query Artifact Id)
    (p : Probe Artifact Id Term Fact) : Decidable (Identity e q p) := by
  unfold Identity; infer_instance

def certificate (q : Query Artifact Id) (p : Probe Artifact Id Term Fact) :
    Certificate Artifact Id Term Fact :=
  ⟨q.use, q.sourceOwner, q.targetOwner, q.registration, p.formal, q.lambda,
    p.construction.function, p.child, p.registeredRoot, p.plan.useValue, p.fact, p.permission⟩

def extract (e : Inputs Artifact Id Term Fact) (q : Query Artifact Id)
    (p : Probe Artifact Id Term Fact) : Option (Certificate Artifact Id Term Fact) :=
  if OwnerReads e q p ∧ Identity e q p then some (certificate q p) else none

theorem accepted_iff (e : Inputs Artifact Id Term Fact) (q : Query Artifact Id)
    (p : Probe Artifact Id Term Fact) (out : Certificate Artifact Id Term Fact) :
    extract e q p = some out ↔
      OwnerReads e q p ∧ Identity e q p ∧ out = certificate q p := by
  unfold extract
  split <;> simp_all [eq_comm]

theorem accepted_identity (e : Inputs Artifact Id Term Fact) (q : Query Artifact Id)
    (p : Probe Artifact Id Term Fact) (out : Certificate Artifact Id Term Fact)
    (accepted : extract e q p = some out) :
    out.use = q.use ∧ out.use.artifact = e.artifact ∧
    out.sourceOwner = p.plan.sourceOwner ∧ out.targetOwner = p.plan.targetOwner ∧
    out.formal.owner = out.targetOwner ∧ out.registration = p.construction.registration ∧
    p.receipt.use = out.use ∧ p.receipt.kind = .internal ∧ p.receipt.fact = some out.fact := by
  obtain ⟨_, identity, rfl⟩ := (accepted_iff e q p out).mp accepted
  rcases identity with ⟨artifact, owner, target, formalOwner, _, _, _, registration,
    _, use, kind, fact, _⟩
  exact ⟨rfl, artifact, owner.symm, target.symm, formalOwner, registration.symm, use, kind, fact⟩

theorem accepted_constructor_and_endpoints (e : Inputs Artifact Id Term Fact)
    (q : Query Artifact Id) (p : Probe Artifact Id Term Fact)
    (out : Certificate Artifact Id Term Fact) (accepted : extract e q p = some out) :
    e.lambdaFact out.lambda = some (out.function, out.originalRoot) ∧
    e.positiveFunctionChild out.function = some out.argumentEffect ∧
    e.negativeEntry out.argumentEffect = some out.permission.entry ∧
    e.routeFact out.fact = some (out.use.occurrence, out.originalRoot, out.useValue) ∧
    out.permission.registration = out.registration := by
  obtain ⟨reads, identity, rfl⟩ := (accepted_iff e q p out).mp accepted
  rcases reads with ⟨_, _, _, _, _, _, _, route, lambda, function, entry, _⟩
  rcases identity with ⟨_, _, _, _, _, _, root, _, _, _, _, _, registration,
    _, _, _, _, _, _, _, permissionEntry, _⟩
  exact ⟨lambda, function, permissionEntry ▸ entry, (by simpa only [certificate, root] using route), registration⟩

theorem accepted_component_identity (e : Inputs Artifact Id Term Fact)
    (q : Query Artifact Id) (p : Probe Artifact Id Term Fact)
    (out : Certificate Artifact Id Term Fact) (accepted : extract e q p = some out) :
    e.lambdaRecipe out.lambda = some (out.registration, p.plan.targetRootComponent) ∧
      p.recipeRootComponent = p.plan.targetRootComponent ∧
      e.componentTerm p.plan.targetRootComponent = some out.originalRoot ∧
      e.componentTerm p.plan.useValueComponent = some out.useValue := by
  obtain ⟨reads, identity, rfl⟩ := (accepted_iff e q p out).mp accepted
  rcases reads with ⟨_, _, _, _, _, _, _, _, _, _, _, recipe, target, use⟩
  rcases identity with ⟨_, _, _, _, _, _, root, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rootIndex⟩
  exact ⟨by simpa only [certificate, rootIndex] using recipe, rootIndex,
    by simpa only [certificate, root] using target, use⟩

theorem accepted_payload (e : Inputs Artifact Id Term Fact) (q : Query Artifact Id)
    (p : Probe Artifact Id Term Fact) (out : Certificate Artifact Id Term Fact)
    (accepted : extract e q p = some out) :
    out.permission = p.permission ∧ out.permission ∈ e.permissions ∧
      out.permission.concrete = p.permission.concrete ∧
      ∀ (i : Nat), out.permission.concrete[i]? = p.permission.concrete[i]? := by
  obtain ⟨reads, _, rfl⟩ := (accepted_iff e q p out).mp accepted
  have unique := reads.2.2.2.1
  have member : p.permission ∈ permissionsFor e q.registration := by rw [unique]; simp
  exact ⟨rfl, (List.mem_filter.mp member).1, rfl, fun _ => rfl⟩

theorem unavailable_owner_rejected (e : Inputs Artifact Id Term Fact)
    (q : Query Artifact Id) (p : Probe Artifact Id Term Fact)
    (unavailable : ¬ OwnerReads e q p) : extract e q p = none := by
  simp [extract, unavailable]

theorem identity_mismatch_rejected (e : Inputs Artifact Id Term Fact)
    (q : Query Artifact Id) (p : Probe Artifact Id Term Fact)
    (mismatch : ¬ Identity e q p) : extract e q p = none := by
  simp [extract, mismatch]

theorem foreign_registration_rejected (e : Inputs Artifact Id Term Fact)
    (q : Query Artifact Id) (p : Probe Artifact Id Term Fact)
    (foreign : p.construction.registration ≠ q.registration ∨
      p.permission.registration ≠ q.registration) : extract e q p = none := by
  apply identity_mismatch_rejected
  intro identity
  rcases identity with ⟨_, _, _, _, _, _, _, construction, _, _, _, _, permission, _⟩
  rcases foreign with h | h
  · exact h construction
  · exact h permission

theorem foreign_use_or_kind_rejected (e : Inputs Artifact Id Term Fact)
    (q : Query Artifact Id) (p : Probe Artifact Id Term Fact)
    (foreign : q.use.artifact ≠ e.artifact ∨ p.receipt.use ≠ q.use ∨
      p.receipt.kind ≠ .internal ∨ p.receipt.fact ≠ some p.fact ∨
      p.plan.sourceOwner ≠ q.sourceOwner ∨ p.plan.targetOwner ≠ q.targetOwner ∨
      p.formal.owner ≠ q.targetOwner ∨ p.registeredRoot ≠ p.plan.targetRoot) :
    extract e q p = none := by
  apply identity_mismatch_rejected
  intro identity
  rcases identity with ⟨artifact, owner, target, formalOwner, _, _, root, _, _, use, kind, fact, _⟩
  rcases foreign with h | h | h | h | h | h | h | h <;> contradiction

theorem component_identity_mismatch_rejected (e : Inputs Artifact Id Term Fact)
    (q : Query Artifact Id) (p : Probe Artifact Id Term Fact)
    (different : p.recipeRootComponent ≠ p.plan.targetRootComponent) : extract e q p = none := by
  apply identity_mismatch_rejected
  intro identity
  rcases identity with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rootIndex⟩
  exact different rootIndex

theorem missing_or_duplicate_permission_rejected (e : Inputs Artifact Id Term Fact)
    (q : Query Artifact Id) (p : Probe Artifact Id Term Fact)
    (shape : permissionsFor e q.registration = [] ∨
      ∃ first second tail, permissionsFor e q.registration = first :: second :: tail) :
    extract e q p = none := by
  apply unavailable_owner_rejected
  intro reads
  have unique := reads.2.2.2.1
  rcases shape with empty | ⟨first, second, tail, multiple⟩
  · simp [empty] at unique
  · simp [multiple] at unique

/-- Even an actual native Function image cannot select a foreign registration.
This is independent of any equality/canonicalization/injectivity assumption. -/
theorem shared_images_do_not_authorize {Image : Type} (canonical : Id → Image)
    (e : Inputs Artifact Id Term Fact)
    (q : Query Artifact Id) (p foreign : Probe Artifact Id Term Fact)
    (sameFunction : foreign.construction.function = p.construction.function)
    (sameChild : foreign.child = p.child)
    (sameEntry : canonical foreign.construction.entry = canonical p.construction.entry)
    (different : foreign.permission.registration ≠ q.registration) :
    foreign.construction.function = p.construction.function ∧ foreign.child = p.child ∧
      canonical foreign.construction.entry = canonical p.construction.entry ∧ extract e q foreign = none :=
  ⟨sameFunction, sameChild, sameEntry, foreign_registration_rejected e q foreign (Or.inr different)⟩

/-- Apply R39 to the SAME permission retained in the Internal probe, keeping
all source-construction and owner-extraction hypotheses explicit. -/
theorem retained_entry_to_internal (e : Inputs Artifact Id Term Fact)
    (a : Action Id) (f : Registration Id) (r : Row Id) (port : Id)
    (before : ComputationPermissionEntryR39.State Id)
    (q : Query Artifact Id) (p : Probe Artifact Id Term Fact)
    (out : Certificate Artifact Id Term Fact)
    (prepared : prepare e.source a = some (f, r, port))
    (retained : permissionFor a f r port = some p.permission)
    (accepted : extract e q p = some out) :
    out.permission = p.permission ∧ out.permission.concrete = r.concrete ∧
      out.permission.registration = a.registration ∧
      publish a f r port true before = some
        ⟨before.permissions ++ [out.permission], before.links ++ symbolicLinks a r port, before.inflow⟩ ∧
      e.positiveFunctionChild out.function = some out.argumentEffect ∧
      e.negativeEntry out.argumentEffect = some out.permission.entry := by
  have exactRow := exact_row_retained e.source a p.permission f r port prepared retained
  have payload := accepted_payload e q p out accepted
  obtain ⟨_, child, entry, _, _⟩ := accepted_constructor_and_endpoints e q p out accepted
  rcases exactRow with ⟨_, _, _, _, _, registration, _, _, _, _, _, _, _, _, concrete⟩
  refine ⟨payload.1, payload.1 ▸ concrete, payload.1 ▸ registration, ?_, child, entry⟩
  have list : (permissionFor a f r port).toList = [out.permission] := by rw [retained, payload.1]; rfl
  simpa only [list] using publication_exact a f r port before

/-- Kernel-computed finite instance, not a native/source execution receipt. -/
def witnessFormal : Registration Nat := ⟨1, 0, 2, 0, 3, .computation, some 4⟩
def witnessRow : Row Nat := ⟨5, [7, 7, 11], [13]⟩
def witnessAction : Action Nat := ⟨0, ⟨1, 6, some witnessRow⟩, 17, 3⟩
def witnessQuery : Query Nat Nat := ⟨⟨99, 100⟩, 10, 1, 0, 17, 6, 5⟩
def witnessProbe : Probe Nat Nat Nat Nat :=
  ⟨witnessFormal, 300, 20, ⟨0, 17, 200, 4⟩,
    ⟨0, 0, 2, 17, 1, 3, 6, 5, 4, [7, 7, 11]⟩,
    ⟨10, 1, 20, 21, 300, 400⟩, ⟨⟨99, 100⟩, .internal, some 88⟩, 88, 201⟩
def witnessInputs : Inputs Nat Nat Nat Nat :=
  ⟨99, ⟨[witnessFormal], [2], [], [(1, [.lambda 17 2])], [(17, 1)], [], []⟩,
    (fun n => if n = 0 then some (witnessFormal, 300) else none),
    [witnessProbe.construction], [witnessProbe.permission], [witnessProbe.receipt],
    (fun u => if u = witnessQuery.use then some witnessProbe.plan else none),
    (fun f => if f = 88 then some (100, 300, 400) else none),
    (fun l => if l = 17 then some (0, 20) else none),
    (fun n => if n = 20 then some 300 else if n = 21 then some 400 else none),
    (fun l => if l = 17 then some (200, 300) else none),
    (fun f => if f = 200 then some 201 else none),
    (fun c => if c = 201 then some 4 else none)⟩

theorem concrete_internal_witness :
    extract witnessInputs witnessQuery witnessProbe = some (certificate witnessQuery witnessProbe) ∧
      (certificate witnessQuery witnessProbe).permission.concrete = [7, 7, 11] ∧
      prepare witnessInputs.source witnessAction = some (witnessFormal, witnessRow, 4) ∧
      permissionFor witnessAction witnessFormal witnessRow 4 = some witnessProbe.permission := by decide

theorem concrete_foreign_and_incoming_rejected :
    extract witnessInputs witnessQuery
      { witnessProbe with permission := { witnessProbe.permission with registration := 1 } } = none ∧
    extract witnessInputs { witnessQuery with use := ⟨98, 100⟩ } witnessProbe = none ∧
    extract witnessInputs witnessQuery
      { witnessProbe with receipt := { witnessProbe.receipt with kind := .incomingStructured } } = none ∧
    extract witnessInputs witnessQuery { witnessProbe with recipeRootComponent := 22 } = none := by decide

end YulangClosure.InternalPermissionIncidenceR45
