import YulangClosure.CurrentEmissionOwnershipR47

/-!
R48 conditional finite provider-arrival checker. Lower paths search owner to
lower item; actual contribution flow is the reverse orientation of that search.
All steps re-read current raw physical slots and their owning admission/emission.
The first entry step is the SAME R47 probe. Both paths share one exact native
AnnotationMember endpoint, not merely a family, row representative or spelling.
Rust extraction/completeness and concrete runtime success remain unproved.
-/
namespace YulangClosure.ProviderEntryArrivalR48

open CurrentEmissionOwnershipR47

inductive NativeAtom where
  | annotationMember (view member : Nat)
  | other
  deriving DecidableEq

inductive ViewOrigin (Id : Type) where
  | annotation
  | operation (occurrence declaration : Id)
  deriving DecidableEq

structure View (Id : Type) where
  origin : ViewOrigin Id
  position : Id
  allowed : List Id
  tail : Option Id
  deriving DecidableEq

structure Inputs (Artifact Id Fact : Type) where
  current : CurrentEmissionOwnershipR47.Inputs Artifact Id Fact
  /-- Complete candidates at the ORIGINAL source occurrence/slot 51, before
  endpoint comparison or provenance validation. -/
  catchCandidates : Id → List Fact
  factOrigin : Fact → Option (Id × Nat)
  factPair : Fact → Option (Endpoint Id × Endpoint Id)
  nativeAtom : Id → Option NativeAtom
  views : Nat → Option (View Id)
  /-- Exact retained declaration allocation/identity and its resolved family. -/
  sourceOperation : Id → Option (Id × Id)

structure Query (Id Fact : Type) where
  catchOccurrence : Id
  catchFact : Fact
  catchInput : Endpoint Id
  catchOutput : Endpoint Id
  provider : Id
  declaration : Id
  family : Id

structure Probe (Id : Type) where
  entryTail : List (CurrentEmissionOwnershipR47.Probe Id)
  catchPath : List (CurrentEmissionOwnershipR47.Probe Id)
  atom : Id
  viewIndex : Nat
  memberIndex : Nat
  view : View Id

structure Certificate (Artifact Id Fact : Type) where
  entry : CurrentEmissionOwnershipR47.Certificate Artifact Id Fact
  query : Query Id Fact
  evidence : Probe Id

variable {Artifact Id Fact : Type}
  [DecidableEq Artifact] [DecidableEq Id] [DecidableEq Fact]

/-- Every finite edge checks its own indexed records, not the entry's root
ancestry. Catch edges need not descend from that Internal root relation. -/
def EdgeReads (e : Inputs Artifact Id Fact) (root : Endpoint Id)
    (p : CurrentEmissionOwnershipR47.Probe Id) : Prop :=
  e.current.admissions[p.admissionIndex]? = some p.admission ∧
  e.current.emissions[p.emissionIndex]? = some p.emission ∧
  p.emission.admission = p.admissionIndex ∧
  emissionsForSlot e.current p.emission.physical = [p.emission] ∧
  p.emission.bound = p.admission.bound ∧
  p.emission.readback.slot = p.emission.physical ∧
  p.emission.readback.bound = p.admission.bound ∧
  currentBound e.current p.emission.physical = some p.admission.bound ∧
  p.emission.physical.owner = p.admission.bound.owner ∧
  (p.emission.physical.lane = .effectLowerRow ∨
    p.emission.physical.lane = .effectLowerAtom) ∧
  (match p.admission.bound.owner with | .effect _ => True | .value _ => False) ∧
  root = rowEndpoint p.admission.bound.owner ∧
  p.admission.bound.polarity = .positive ∧
  p.admission.relation = some p.relation ∧
  p.relation ∈ e.current.liveRelations ∧
  e.current.relationPair p.relation = some (boundPair p.admission.bound)

instance (e : Inputs Artifact Id Fact) (root : Endpoint Id)
    (p : CurrentEmissionOwnershipR47.Probe Id) : Decidable (EdgeReads e root p) := by
  unfold EdgeReads
  cases p.admission.bound.owner <;> infer_instance

/-- A bounded supplied path; no total search/completeness assertion. -/
def pathCheck (e : Inputs Artifact Id Fact) : Endpoint Id →
    List (CurrentEmissionOwnershipR47.Probe Id) → Endpoint Id → Bool
  | root, [], terminal => decide (root = terminal)
  | root, p :: rest, terminal => decide (EdgeReads e root p) &&
      pathCheck e p.admission.bound.item rest terminal

inductive LowerPath (e : Inputs Artifact Id Fact) : Endpoint Id → Endpoint Id → Prop where
  | refl {point} : LowerPath e point point
  | step {root terminal} (p : CurrentEmissionOwnershipR47.Probe Id) :
      EdgeReads e root p → LowerPath e p.admission.bound.item terminal →
      LowerPath e root terminal

/-- Contribution arrival runs item to owner, matching positive boundPair. -/
inductive Arrival (e : Inputs Artifact Id Fact) : Endpoint Id → Endpoint Id → Prop where
  | refl {point} : Arrival e point point
  | step {root terminal} (p : CurrentEmissionOwnershipR47.Probe Id) :
      EdgeReads e root p → Arrival e terminal p.admission.bound.item →
      Arrival e terminal root

omit [DecidableEq Artifact] [DecidableEq Fact] in
theorem path_sound (e : Inputs Artifact Id Fact) (root terminal : Endpoint Id)
    (path : List (CurrentEmissionOwnershipR47.Probe Id))
    (checked : pathCheck e root path terminal = true) : LowerPath e root terminal := by
  induction path generalizing root with
  | nil =>
    have h : root = terminal := by simpa [pathCheck] using checked
    cases h
    exact .refl
  | cons p rest ih =>
    have h : EdgeReads e root p ∧ pathCheck e p.admission.bound.item rest terminal = true := by
      simpa [pathCheck] using checked
    exact .step p h.1 (ih _ h.2)

omit [DecidableEq Artifact] [DecidableEq Fact] in
theorem lower_path_arrival (e : Inputs Artifact Id Fact) (root terminal : Endpoint Id)
    (path : LowerPath e root terminal) : Arrival e terminal root := by
  induction path with
  | refl => exact .refl
  | step p edge _ ih => exact .step p edge ih

/-- The checked source Fact is selected BEFORE comparing its native pair. -/
def CatchReads (e : Inputs Artifact Id Fact) (q : Query Id Fact) : Prop :=
  e.catchCandidates q.catchOccurrence = [q.catchFact] ∧
  e.factOrigin q.catchFact = some (q.catchOccurrence, 51) ∧
  e.current.sourceFact (q.catchOccurrence, 51) = some q.catchFact ∧
  e.factPair q.catchFact = some (q.catchInput, q.catchOutput)

instance (e : Inputs Artifact Id Fact) (q : Query Id Fact) : Decidable (CatchReads e q) := by
  unfold CatchReads; infer_instance

/-- Exact retained native constructor and original operation identity. Full
branded declaration keys retain allocation and resolved identity/type information.
Symbolic tails and original typed view positions are retained without imposing
a new closed-tail or root-position premise on operation arrival. -/
def TerminalReads (e : Inputs Artifact Id Fact) (q : Query Id Fact) (p : Probe Id) : Prop :=
  e.nativeAtom p.atom = some (.annotationMember p.viewIndex p.memberIndex) ∧
  e.views p.viewIndex = some p.view ∧
  p.view.origin = .operation q.provider q.declaration ∧
  p.view.allowed[p.memberIndex]? = some q.family ∧
  e.sourceOperation q.provider = some (q.declaration, q.family)

instance (e : Inputs Artifact Id Fact) (q : Query Id Fact) (p : Probe Id) :
    Decidable (TerminalReads e q p) := by unfold TerminalReads; infer_instance

def Matches (e : Inputs Artifact Id Fact)
    (entryQuery : CurrentEmissionOwnershipR47.Query Artifact Id Fact)
    (entryProbe : CurrentEmissionOwnershipR47.Probe Id) (q : Query Id Fact) (p : Probe Id) : Prop :=
  CurrentEmissionOwnershipR47.Matches e.current entryQuery entryProbe ∧
  pathCheck e (.effectRow entryQuery.rawEntry) (entryProbe :: p.entryTail) (.effectAtom p.atom) = true ∧
  CatchReads e q ∧
  pathCheck e q.catchInput p.catchPath (.effectAtom p.atom) = true ∧
  TerminalReads e q p

instance (e : Inputs Artifact Id Fact)
    (entryQuery : CurrentEmissionOwnershipR47.Query Artifact Id Fact)
    (entryProbe : CurrentEmissionOwnershipR47.Probe Id) (q : Query Id Fact) (p : Probe Id) :
    Decidable (Matches e entryQuery entryProbe q p) := by unfold Matches; infer_instance

def extract (e : Inputs Artifact Id Fact)
    (entryQuery : CurrentEmissionOwnershipR47.Query Artifact Id Fact)
    (entryProbe : CurrentEmissionOwnershipR47.Probe Id) (q : Query Id Fact) (p : Probe Id) :
    Option (Certificate Artifact Id Fact) :=
  if Matches e entryQuery entryProbe q p then some ⟨⟨entryQuery, entryProbe⟩, q, p⟩ else none

theorem accepted_iff (e : Inputs Artifact Id Fact)
    (entryQuery : CurrentEmissionOwnershipR47.Query Artifact Id Fact)
    (entryProbe : CurrentEmissionOwnershipR47.Probe Id) (q : Query Id Fact) (p : Probe Id)
    (out : Certificate Artifact Id Fact) : extract e entryQuery entryProbe q p = some out ↔
      Matches e entryQuery entryProbe q p ∧ out = ⟨⟨entryQuery, entryProbe⟩, q, p⟩ := by
  unfold extract
  split <;> simp_all [eq_comm]

theorem accepted_entry (e : Inputs Artifact Id Fact)
    (entryQuery : CurrentEmissionOwnershipR47.Query Artifact Id Fact)
    (entryProbe : CurrentEmissionOwnershipR47.Probe Id) (q : Query Id Fact) (p : Probe Id)
    (out : Certificate Artifact Id Fact) (accepted : extract e entryQuery entryProbe q p = some out) :
    CurrentEmissionOwnershipR47.extract e.current entryQuery entryProbe = some out.entry ∧
      LowerPath e (.effectRow out.entry.query.rawEntry) (.effectAtom out.evidence.atom) ∧
      Arrival e (.effectAtom out.evidence.atom) (.effectRow out.entry.query.rawEntry) := by
  obtain ⟨matched, rfl⟩ := (accepted_iff e entryQuery entryProbe q p out).mp accepted
  have path := path_sound e (.effectRow entryQuery.rawEntry) (.effectAtom p.atom)
    (entryProbe :: p.entryTail) matched.2.1
  exact ⟨(CurrentEmissionOwnershipR47.accepted_iff _ _ _ _).mpr ⟨matched.1, rfl⟩,
    path, lower_path_arrival _ _ _ path⟩

theorem accepted_common_endpoint (e : Inputs Artifact Id Fact)
    (entryQuery : CurrentEmissionOwnershipR47.Query Artifact Id Fact)
    (entryProbe : CurrentEmissionOwnershipR47.Probe Id) (q : Query Id Fact) (p : Probe Id)
    (out : Certificate Artifact Id Fact) (accepted : extract e entryQuery entryProbe q p = some out) :
    CatchReads e out.query ∧ TerminalReads e out.query out.evidence ∧
      LowerPath e (.effectRow out.entry.query.rawEntry) (.effectAtom out.evidence.atom) ∧
      LowerPath e out.query.catchInput (.effectAtom out.evidence.atom) ∧
      Arrival e (.effectAtom out.evidence.atom) out.query.catchInput := by
  have entry := accepted_entry e entryQuery entryProbe q p out accepted
  obtain ⟨matched, rfl⟩ := (accepted_iff e entryQuery entryProbe q p out).mp accepted
  have path := path_sound e q.catchInput (.effectAtom p.atom) p.catchPath matched.2.2.2.1
  exact ⟨matched.2.2.1, matched.2.2.2.2, entry.2.1, path, lower_path_arrival _ _ _ path⟩

/-- Composition retains the SAME R45 certificate, permission, R47 first
emission, native terminal and both checked path witnesses. The three extraction
identity equations remain explicit source premises, exactly as in R47. -/
theorem apply_to_internal {Term : Type} [DecidableEq Term]
    (internalInputs : InternalPermissionIncidenceR45.Inputs Artifact Id Term Fact)
    (internalQuery : InternalPermissionIncidenceR45.Query Artifact Id)
    (internalProbe : InternalPermissionIncidenceR45.Probe Artifact Id Term Fact)
    (internal : InternalPermissionIncidenceR45.Certificate Artifact Id Term Fact)
    (internalAccepted : InternalPermissionIncidenceR45.extract internalInputs internalQuery internalProbe = some internal)
    (e : Inputs Artifact Id Fact)
    (entryQuery : CurrentEmissionOwnershipR47.Query Artifact Id Fact)
    (entryProbe : CurrentEmissionOwnershipR47.Probe Id) (q : Query Id Fact) (p : Probe Id)
    (out : Certificate Artifact Id Fact) (accepted : extract e entryQuery entryProbe q p = some out)
    (sameUse : entryQuery.use = internal.use) (sameFact : entryQuery.internalFact = internal.fact)
    (sameRawEntry : entryQuery.rawEntry = internal.permission.entry) :
    out.entry.query.use = internal.use ∧ out.entry.query.internalFact = internal.fact ∧
      internal.permission = internalProbe.permission ∧
      internal.permission.concrete = internalProbe.permission.concrete ∧
      currentBound e.current out.entry.evidence.emission.physical = some out.entry.evidence.admission.bound ∧
      out.entry.evidence.emission.physical.owner = .effect internal.permission.entry ∧
      RelationPath e.current out.entry.query.rootRelation out.entry.evidence.relation ∧
      Arrival e (.effectAtom out.evidence.atom) (.effectRow internal.permission.entry) ∧
      CatchReads e out.query ∧ TerminalReads e out.query out.evidence ∧
      LowerPath e out.query.catchInput (.effectAtom out.evidence.atom) := by
  have entry := accepted_entry e entryQuery entryProbe q p out accepted
  have common := accepted_common_endpoint e entryQuery entryProbe q p out accepted
  have composed := CurrentEmissionOwnershipR47.apply_to_internal internalInputs internalQuery internalProbe
    internal internalAccepted e.current entryQuery entryProbe out.entry entry.1 sameUse sameFact sameRawEntry
  obtain ⟨matched, rfl⟩ := (accepted_iff e entryQuery entryProbe q p out).mp accepted
  rcases composed with ⟨use, fact, permission, concrete, current, owner, relation⟩
  exact ⟨use, fact, permission, concrete, current, owner, relation,
    sameRawEntry ▸ entry.2.2, common.1, common.2.1, common.2.2.2.1⟩

theorem mismatch_rejected (e : Inputs Artifact Id Fact)
    (entryQuery : CurrentEmissionOwnershipR47.Query Artifact Id Fact)
    (entryProbe : CurrentEmissionOwnershipR47.Probe Id) (q : Query Id Fact) (p : Probe Id)
    (mismatch : ¬ Matches e entryQuery entryProbe q p) : extract e entryQuery entryProbe q p = none := by
  simp [extract, mismatch]

/-- Local failures cannot be repaired by family or canonical-row equality. -/
theorem path_or_origin_mismatch_rejected (e : Inputs Artifact Id Fact)
    (entryQuery : CurrentEmissionOwnershipR47.Query Artifact Id Fact)
    (entryProbe : CurrentEmissionOwnershipR47.Probe Id) (q : Query Id Fact) (p : Probe Id)
    (bad : pathCheck e (.effectRow entryQuery.rawEntry) (entryProbe :: p.entryTail) (.effectAtom p.atom) ≠ true ∨
      ¬ CatchReads e q ∨ pathCheck e q.catchInput p.catchPath (.effectAtom p.atom) ≠ true ∨
      ¬ TerminalReads e q p) : extract e entryQuery entryProbe q p = none := by
  apply mismatch_rejected
  rintro ⟨_, entry, catchRoot, catchPath, terminal⟩
  rcases bad with h | h | h | h <;> contradiction

end YulangClosure.ProviderEntryArrivalR48
