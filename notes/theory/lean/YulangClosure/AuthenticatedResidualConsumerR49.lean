import YulangClosure.ProviderEntryArrivalR48

/-!
R49 conditional private consumer model. This extends R48's physical paths by
an explicitly logical SupportMember step. It does not alter ProviderEntryArrivalR48.extract.
Tables stand for exact retained source/native reads; their extraction,
completeness, live-State lifetime and the Rust execution remain obligations.
R50 repairs authenticated matching/known-unmatched/unavailable classification.
No theorem below establishes a source typing rule or Catch execution.
-/
namespace YulangClosure.AuthenticatedResidualConsumerR49

open CurrentEmissionOwnershipR47

structure SupportMember (Id : Type) where
  support : Id
  member : Id
  viewIndex : Nat
  ordinal : Nat
  family : Id
  view : ProviderEntryArrivalR48.View Id
  deriving DecidableEq

inductive Step (Id : Type) where
  | physical (probe : CurrentEmissionOwnershipR47.Probe Id)
  | supportMember (member : SupportMember Id)
  deriving DecidableEq

/-- Logical Support and physical member reads are kept separate. A native
Support operand has no fabricated admission/emission record. -/
structure Inputs (Artifact Id Fact : Type) where
  arrival : ProviderEntryArrivalR48.Inputs Artifact Id Fact
  supportView : Id → Option Nat
  /-- Bounded candidate search inventory. Completeness remains a source premise. -/
  pathCandidates : Endpoint Id → Endpoint Id → List (List (Step Id))
  providerCandidates : Id → Id → Id → List Id

variable {Artifact Id Fact : Type} [DecidableEq Artifact] [DecidableEq Id] [DecidableEq Fact]

def SupportReads (e : Inputs Artifact Id Fact) (s : SupportMember Id) : Prop :=
  e.supportView s.support = some s.viewIndex ∧
  e.arrival.views s.viewIndex = some s.view ∧
  e.arrival.nativeAtom s.member = some (.annotationMember s.viewIndex s.ordinal) ∧
  s.view.allowed[s.ordinal]? = some s.family ∧ s.view.tail = none

instance (e : Inputs Artifact Id Fact) (s : SupportMember Id) : Decidable (SupportReads e s) := by
  unfold SupportReads; infer_instance

def next {Id : Type} : Step Id → Endpoint Id
  | .physical p => p.admission.bound.item
  | .supportMember s => .effectAtom s.member

def StepReads (e : Inputs Artifact Id Fact) (root : Endpoint Id) : Step Id → Prop
  | .physical p => ProviderEntryArrivalR48.EdgeReads e.arrival root p
  | .supportMember s => root = .effectAtom s.support ∧ SupportReads e s

instance (e : Inputs Artifact Id Fact) (root : Endpoint Id) (s : Step Id) :
    Decidable (StepReads e root s) := by cases s <;> unfold StepReads <;> infer_instance

def pathCheck (e : Inputs Artifact Id Fact) : Endpoint Id → List (Step Id) → Endpoint Id → Bool
  | root, [], terminal => decide (root = terminal)
  | root, step :: rest, terminal => decide (StepReads e root step) && pathCheck e (next step) rest terminal

inductive LowerPath (e : Inputs Artifact Id Fact) : Endpoint Id → Endpoint Id → Prop where
  | refl {point} : LowerPath e point point
  | step {root terminal} (s : Step Id) : StepReads e root s →
      LowerPath e (next s) terminal → LowerPath e root terminal

inductive Arrival (e : Inputs Artifact Id Fact) : Endpoint Id → Endpoint Id → Prop where
  | refl {point} : Arrival e point point
  | step {root terminal} (s : Step Id) : StepReads e root s →
      Arrival e terminal (next s) → Arrival e terminal root

omit [DecidableEq Artifact] [DecidableEq Fact] in
/-- Soundness means these exact retained reads, not source execution. -/
theorem support_member_sound (e : Inputs Artifact Id Fact) (s : SupportMember Id)
    (checked : decide (SupportReads e s) = true) :
    e.supportView s.support = some s.viewIndex ∧
    e.arrival.views s.viewIndex = some s.view ∧
    e.arrival.nativeAtom s.member = some (.annotationMember s.viewIndex s.ordinal) ∧
    s.view.allowed[s.ordinal]? = some s.family ∧ s.view.tail = none ∧
    LowerPath e (.effectAtom s.support) (.effectAtom s.member) := by
  have reads : SupportReads e s := of_decide_eq_true checked
  exact ⟨reads.1, reads.2.1, reads.2.2.1, reads.2.2.2.1, reads.2.2.2.2,
    .step (.supportMember s) ⟨rfl, reads⟩ .refl⟩

omit [DecidableEq Artifact] [DecidableEq Fact] in
theorem path_sound (e : Inputs Artifact Id Fact) (root terminal : Endpoint Id)
    (steps : List (Step Id)) (checked : pathCheck e root steps terminal = true) :
    LowerPath e root terminal := by
  induction steps generalizing root with
  | nil =>
    have equal : root = terminal := by simpa [pathCheck] using checked
    cases equal; exact .refl
  | cons s rest ih =>
    have both : StepReads e root s ∧ pathCheck e (next s) rest terminal = true := by
      simpa [pathCheck] using checked
    exact .step s both.1 (ih _ both.2)

omit [DecidableEq Artifact] [DecidableEq Fact] in
theorem lower_path_arrival (e : Inputs Artifact Id Fact) (root terminal : Endpoint Id)
    (path : LowerPath e root terminal) : Arrival e terminal root := by
  induction path with
  | refl => exact .refl
  | step s reads _ ih => exact .step s reads ih

omit [DecidableEq Artifact] [DecidableEq Fact] in
/-- Conservative embedding: unchanged R48 physical paths remain accepted. -/
theorem physical_path_iff (e : Inputs Artifact Id Fact) (root terminal : Endpoint Id)
    (steps : List (CurrentEmissionOwnershipR47.Probe Id)) :
    pathCheck e root (steps.map Step.physical) terminal = ProviderEntryArrivalR48.pathCheck e.arrival root steps terminal := by
  induction steps generalizing root with
  | nil => rfl
  | cons p rest ih => simp only [List.map_cons, pathCheck, ProviderEntryArrivalR48.pathCheck, StepReads, next, ih]

inductive ValuePattern (Id : Type) where
  | wildcard | binder (identity : Id)
  deriving DecidableEq

inductive PayloadPattern (Id : Type) where
  /-- HIR empty-call syntax; this does NOT assert semantic Unit matching. -/
  | unitSyntax (source : Id)
  | value (pattern : ValuePattern Id)
  deriving DecidableEq

inductive Pattern (Id : Type) where
  | operation (source declaration family : Id) (payloads : List (PayloadPattern Id))
      (continuation : ValuePattern Id)
  | value (pattern : ValuePattern Id)
  deriving DecidableEq

structure Arm (Id : Type) where
  source : Id
  range : Nat × Nat
  pattern : Pattern Id
  deriving DecidableEq

structure SourceCatch (Id : Type) where
  occurrence : Id
  edgeScrutinee : Id
  arms : List (Arm Id)
  deriving DecidableEq

structure Selection (Id : Type) where
  catchOccurrence : Id
  position : Nat
  armSource : Id
  armRange : Nat × Nat
  operationSource : Id
  payloadSource : Id
  declaration : Id
  family : Id
  deriving DecidableEq

structure SourceInputs (Id : Type) where
  catchSource : Id → Option (SourceCatch Id)
  resolvedOperation : Id → Option (Id × Id)

/-- Exact source occurrence, list position, arm source and resolved declaration.
No supplied selected boolean or family-only authorization. The private supported
pattern is empty-call syntax and a wildcard continuation. -/
def SelectedArmReads (src : SourceInputs Id) (q : ProviderEntryArrivalR48.Query Id Fact) (s : Selection Id) : Prop :=
  s.position = 0 ∧ ∃ c ∈ (src.catchSource s.catchOccurrence).toList,
    c.occurrence = s.catchOccurrence ∧ c.edgeScrutinee = q.catchOccurrence ∧
    c.arms[s.position]? = some ⟨s.armSource, s.armRange,
      .operation s.operationSource s.declaration s.family [.unitSyntax s.payloadSource] .wildcard⟩ ∧
    src.resolvedOperation s.operationSource = some (s.declaration, s.family)

instance (src : SourceInputs Id) (q : ProviderEntryArrivalR48.Query Id Fact) (s : Selection Id) :
    Decidable (SelectedArmReads src q s) := by unfold SelectedArmReads; infer_instance

/-- Matching keeps the independent source read and the exact identity joins. -/
def ArmReads (src : SourceInputs Id) (q : ProviderEntryArrivalR48.Query Id Fact) (s : Selection Id) : Prop :=
  SelectedArmReads src q s ∧ s.declaration = q.declaration ∧ s.family = q.family

instance (src : SourceInputs Id) (q : ProviderEntryArrivalR48.Query Id Fact) (s : Selection Id) :
    Decidable (ArmReads src q s) := by unfold ArmReads; infer_instance

structure Probe (Id : Type) where
  entryTail : List (Step Id)
  catchPath : List (Step Id)
  terminal : ProviderEntryArrivalR48.Probe Id
  selection : Selection Id

/-- Only TerminalReads uses this retained R48 terminal; R49 path witnesses live
in the typed lists above. No claim is made that ProviderEntryArrivalR48.extract accepts these lists. -/
structure Context (Artifact Id Term Fact : Type) where
  internalInputs : InternalPermissionIncidenceR45.Inputs Artifact Id Term Fact
  internalQuery : InternalPermissionIncidenceR45.Query Artifact Id
  internalProbe : InternalPermissionIncidenceR45.Probe Artifact Id Term Fact
  internal : InternalPermissionIncidenceR45.Certificate Artifact Id Term Fact
  inputs : Inputs Artifact Id Fact
  source : SourceInputs Id
  entryQuery : CurrentEmissionOwnershipR47.Query Artifact Id Fact
  entryProbe : CurrentEmissionOwnershipR47.Probe Id
  query : ProviderEntryArrivalR48.Query Id Fact
  probe : Probe Id

variable {Term : Type} [DecidableEq Term]

def Authenticated (c : Context Artifact Id Term Fact) : Prop :=
  InternalPermissionIncidenceR45.extract c.internalInputs c.internalQuery c.internalProbe = some c.internal ∧
  CurrentEmissionOwnershipR47.Matches c.inputs.arrival.current c.entryQuery c.entryProbe ∧
  c.entryQuery.use = c.internal.use ∧ c.entryQuery.internalFact = c.internal.fact ∧
  c.entryQuery.rawEntry = c.internal.permission.entry ∧
  c.query.family ∈ c.internal.permission.concrete ∧
  c.inputs.providerCandidates c.query.provider c.query.declaration c.query.family = [c.probe.terminal.atom] ∧
  c.inputs.pathCandidates (.effectRow c.entryQuery.rawEntry) (.effectAtom c.probe.terminal.atom) =
    [.physical c.entryProbe :: c.probe.entryTail] ∧
  c.inputs.pathCandidates c.query.catchInput (.effectAtom c.probe.terminal.atom) = [c.probe.catchPath] ∧
  pathCheck c.inputs (.effectRow c.entryQuery.rawEntry)
    (.physical c.entryProbe :: c.probe.entryTail) (.effectAtom c.probe.terminal.atom) = true ∧
  ProviderEntryArrivalR48.CatchReads c.inputs.arrival c.query ∧
  pathCheck c.inputs c.query.catchInput c.probe.catchPath (.effectAtom c.probe.terminal.atom) = true ∧
  ProviderEntryArrivalR48.TerminalReads c.inputs.arrival c.query c.probe.terminal ∧
  c.probe.terminal.view.tail = none ∧
  ArmReads c.source c.query c.probe.selection

instance (c : Context Artifact Id Term Fact) : Decidable (Authenticated c) := by
  unfold Authenticated; infer_instance

def target (c : Context Artifact Id Term Fact) : Endpoint Id := .effectAtom c.probe.terminal.atom

def authenticate (c : Context Artifact Id Term Fact) : Bool := decide (Authenticated c)

/-- Both identities are independently authenticated at their owning source
reads before comparing complete declaration keys. Names/pointer inequality alone
supply neither read. Extraction completeness remains a source obligation. -/
def IdentityReads (c : Context Artifact Id Term Fact) : Prop :=
  SelectedArmReads c.source c.query c.probe.selection ∧
    c.inputs.arrival.sourceOperation c.query.provider = some (c.query.declaration, c.query.family)

instance (c : Context Artifact Id Term Fact) : Decidable (IdentityReads c) := by
  unfold IdentityReads; infer_instance

inductive Classification where
  | authenticatedMatch | knownUnmatched | unavailable
  deriving DecidableEq

def classifyIdentity (c : Context Artifact Id Term Fact) : Classification :=
  if IdentityReads c then
    if c.probe.selection.declaration = c.query.declaration then
      if c.probe.selection.family = c.query.family then .authenticatedMatch else .unavailable
    else .knownUnmatched
  else .unavailable

omit [DecidableEq Artifact] [DecidableEq Fact] [DecidableEq Term] in
theorem classification_match_iff (c : Context Artifact Id Term Fact) :
    classifyIdentity c = .authenticatedMatch ↔ IdentityReads c ∧
      c.probe.selection.declaration = c.query.declaration ∧ c.probe.selection.family = c.query.family := by
  by_cases reads : IdentityReads c <;>
    by_cases same : c.probe.selection.declaration = c.query.declaration <;>
    by_cases family : c.probe.selection.family = c.query.family <;>
    simp [classifyIdentity, reads, same, family]

omit [DecidableEq Artifact] [DecidableEq Fact] [DecidableEq Term] in
theorem classification_known_unmatched_iff (c : Context Artifact Id Term Fact) :
    classifyIdentity c = .knownUnmatched ↔ IdentityReads c ∧ c.probe.selection.declaration ≠ c.query.declaration := by
  by_cases reads : IdentityReads c <;>
    by_cases same : c.probe.selection.declaration = c.query.declaration <;>
    by_cases family : c.probe.selection.family = c.query.family <;>
    simp [classifyIdentity, reads, same, family]

theorem authenticated_identity_match (c : Context Artifact Id Term Fact)
    (accepted : authenticate c = true) : classifyIdentity c = .authenticatedMatch := by
  have h : Authenticated c := of_decide_eq_true accepted
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, terminal, _, arm⟩
  exact (classification_match_iff c).mpr ⟨⟨arm.1, terminal.2.2.2.2⟩, arm.2.1, arm.2.2⟩

/-- Match the Rust branch partition using exact provider/declaration origin,
member family and a closed retained view. Foreign members and contributions
are forwarded, including those with the same family. -/
def providerCandidate (c : Context Artifact Id Term Fact) : Endpoint Id → Option Bool
  | .effectAtom atom =>
      match c.inputs.arrival.nativeAtom atom with
      | some (.annotationMember viewIndex ordinal) =>
          match c.inputs.arrival.views viewIndex with
          | some view =>
              match view.allowed[ordinal]? with
              | some family => some (decide (view.origin = .operation c.query.provider c.query.declaration ∧
                  family = c.query.family ∧ view.tail = none))
              | none => none
          | none => none
      | some .other => some false
      | none => none
  | _ => some false

theorem authenticated_target_candidate (c : Context Artifact Id Term Fact)
    (accepted : authenticate c = true) : providerCandidate c (target c) = some true := by
  have h : Authenticated c := of_decide_eq_true accepted
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, terminal, closed, _⟩
  rcases terminal with ⟨native, view, origin, member, _⟩
  simp [providerCandidate, target, native, view, origin, member, closed]

/-- Accepted suppression reconstructs the SAME permission and original emission,
then the extended R48 common endpoint, and the exact selected source arm. -/
theorem authenticated_prerequisites (c : Context Artifact Id Term Fact)
    (accepted : authenticate c = true) :
    c.internal.permission = c.internalProbe.permission ∧
    c.query.family ∈ c.internal.permission.concrete ∧
    CurrentEmissionOwnershipR47.extract c.inputs.arrival.current c.entryQuery c.entryProbe = some ⟨c.entryQuery, c.entryProbe⟩ ∧
    c.entryQuery.use = c.internal.use ∧ c.entryQuery.internalFact = c.internal.fact ∧
    currentBound c.inputs.arrival.current c.entryProbe.emission.physical = some c.entryProbe.admission.bound ∧
    c.entryProbe.emission.physical.owner = .effect c.internal.permission.entry ∧
    RelationPath c.inputs.arrival.current c.entryQuery.rootRelation c.entryProbe.relation ∧
    Arrival c.inputs (target c) (.effectRow c.internal.permission.entry) ∧
    ProviderEntryArrivalR48.CatchReads c.inputs.arrival c.query ∧
    ProviderEntryArrivalR48.TerminalReads c.inputs.arrival c.query c.probe.terminal ∧
    Arrival c.inputs (target c) c.query.catchInput ∧ ArmReads c.source c.query c.probe.selection := by
  have h : Authenticated c := of_decide_eq_true accepted
  rcases h with ⟨internal, entry, use, fact, raw, family, _, _, _, entryPath, catchReads, catchPath, terminal, _, arm⟩
  have entryAccepted := (CurrentEmissionOwnershipR47.accepted_iff _ _ _ _).mpr ⟨entry, rfl⟩
  have composition := CurrentEmissionOwnershipR47.apply_to_internal c.internalInputs c.internalQuery c.internalProbe c.internal
    internal c.inputs.arrival.current c.entryQuery c.entryProbe ⟨c.entryQuery, c.entryProbe⟩
    entryAccepted use fact raw
  rcases composition with ⟨use, fact, permission, _, current, owner, relation⟩
  have arrival := lower_path_arrival _ _ _ (path_sound _ _ _ _ entryPath)
  have catchArrival := lower_path_arrival _ _ _ (path_sound _ _ _ _ catchPath)
  exact ⟨permission, family, entryAccepted, use, fact, current, owner, relation,
    raw ▸ arrival, catchReads, terminal, catchArrival, arm⟩

/-- R48 acceptance can supply the physical portion without altering its checker.
This theorem reuses its exact query/probe and explicitly requires arm/source and
permission identity checks; logical paths use Authenticated directly. -/
theorem lift_r48 (c : Context Artifact Id Term Fact)
    (accepted : ProviderEntryArrivalR48.extract c.inputs.arrival c.entryQuery c.entryProbe c.query c.probe.terminal =
      some ⟨⟨c.entryQuery, c.entryProbe⟩, c.query, c.probe.terminal⟩)
    (internal : InternalPermissionIncidenceR45.extract c.internalInputs c.internalQuery c.internalProbe = some c.internal)
    (use : c.entryQuery.use = c.internal.use) (fact : c.entryQuery.internalFact = c.internal.fact)
    (raw : c.entryQuery.rawEntry = c.internal.permission.entry)
    (family : c.query.family ∈ c.internal.permission.concrete)
    (entryTail : c.probe.entryTail = c.probe.terminal.entryTail.map Step.physical)
    (catchPath : c.probe.catchPath = c.probe.terminal.catchPath.map Step.physical)
    (closed : c.probe.terminal.view.tail = none)
    (providerUnique : c.inputs.providerCandidates c.query.provider c.query.declaration c.query.family =
      [c.probe.terminal.atom])
    (entryUnique : c.inputs.pathCandidates (.effectRow c.entryQuery.rawEntry) (.effectAtom c.probe.terminal.atom) =
      [.physical c.entryProbe :: c.probe.entryTail])
    (catchUnique : c.inputs.pathCandidates c.query.catchInput (.effectAtom c.probe.terminal.atom) = [c.probe.catchPath])
    (arm : ArmReads c.source c.query c.probe.selection) : authenticate c = true := by
  have h := ((ProviderEntryArrivalR48.accepted_iff _ _ _ _ _ _).mp accepted).1
  apply decide_eq_true
  refine ⟨internal, h.1, use, fact, raw, family, providerUnique, entryUnique, catchUnique, ?_, h.2.2.1, ?_, h.2.2.2.2, closed, arm⟩
  · simpa only [entryTail, ← List.map_cons, physical_path_iff] using h.2.1
  · simpa only [catchPath, physical_path_iff] using h.2.2.2.1

inductive Decision where
  | suppress | forward
  deriving DecidableEq

/-- Pure immutable planning. Every exact unmatched original endpoint forwards;
a matching endpoint needs all authentication checks, with no fallback. -/
def decideEndpoint (c : Context Artifact Id Term Fact) (endpoint : Endpoint Id) : Option Decision :=
  match classifyIdentity c, providerCandidate c endpoint with
  | .unavailable, _ => none
  | _, none => none
  | .knownUnmatched, some _ => some .forward
  | .authenticatedMatch, some false => some .forward
  | .authenticatedMatch, some true =>
      if endpoint = target c ∧ authenticate c = true then some .suppress else none

def plan (c : Context Artifact Id Term Fact) : List (Endpoint Id) → Option (List (Endpoint Id × Decision))
  | [] => some []
  | endpoint :: rest => do
      let decision ← decideEndpoint c endpoint
      let tail ← plan c rest
      some ((endpoint, decision) :: tail)

/-- Forward records are the exact native lower endpoint paired with the given
upper endpoint. This is an immutable projection, not a Rust mutation receipt. -/
def fold {Id : Type} (upper : Endpoint Id) : List (Endpoint Id × Decision) → List (Endpoint Id × Endpoint Id)
  | [] => []
  | (_endpoint, .suppress) :: rest => fold upper rest
  | (endpoint, .forward) :: rest => (endpoint, upper) :: fold upper rest

def publish (c : Context Artifact Id Term Fact) (original : List (Endpoint Id)) (upper : Endpoint Id) :
    Option (List (Endpoint Id × Endpoint Id)) := (plan c original).map (fold upper)

theorem suppression_iff (c : Context Artifact Id Term Fact) (endpoint : Endpoint Id) :
    decideEndpoint c endpoint = some .suppress ↔ endpoint = target c ∧ authenticate c = true := by
  constructor
  · intro accepted
    cases hi : classifyIdentity c with
    | unavailable => simp [decideEndpoint, hi] at accepted
    | knownUnmatched =>
      cases hc : providerCandidate c endpoint <;> simp [decideEndpoint, hi, hc] at accepted
    | authenticatedMatch =>
      cases hc : providerCandidate c endpoint with
      | none => simp [decideEndpoint, hi, hc] at accepted
      | some matching =>
        cases matching with
        | false => simp [decideEndpoint, hi, hc] at accepted
        | true =>
          by_cases checks : endpoint = target c ∧ authenticate c = true
          · exact checks
          · simp [decideEndpoint, hi, hc, checks] at accepted
  · rintro ⟨rfl, auth⟩
    simp [decideEndpoint, authenticated_identity_match c auth, authenticated_target_candidate c auth, auth]


theorem unmatched_decision (c : Context Artifact Id Term Fact) (endpoint : Endpoint Id)
    (unmatched : providerCandidate c endpoint = some false)
    (available : classifyIdentity c ≠ .unavailable) : decideEndpoint c endpoint = some .forward := by
  cases hi : classifyIdentity c <;> simp_all [decideEndpoint]

/-- Exact plan shape retains order, multiplicity and original endpoints. -/
theorem plan_correspondence (c : Context Artifact Id Term Fact) (original : List (Endpoint Id))
    (out : List (Endpoint Id × Decision)) (accepted : plan c original = some out) :
    out.map Prod.fst = original ∧
    ∀ endpoint decision, (endpoint, decision) ∈ out → decideEndpoint c endpoint = some decision := by
  induction original generalizing out with
  | nil =>
    simp [plan] at accepted
    subst out; simp
  | cons endpoint rest ih =>
    cases hd : decideEndpoint c endpoint with
    | none => simp [plan, hd] at accepted
    | some decision =>
      cases ht : plan c rest with
      | none => simp [plan, hd, ht] at accepted
      | some tail =>
        have equal : (endpoint, decision) :: tail = out := by simpa [plan, hd, ht] using accepted
        subst out
        have h := ih tail ht
        refine ⟨by simp only [List.map_cons, h.1], ?_⟩
        intro e d member
        rcases List.mem_cons.mp member with same | later
        · cases same; exact hd
        · exact h.2 e d later

omit [DecidableEq Id] in
/-- List position, rather than family membership, determines each folded row. -/
theorem fold_correspondence (upper : Endpoint Id) (out : List (Endpoint Id × Decision)) :
    fold upper out = out.filterMap (fun item =>
      match item.2 with | .suppress => none | .forward => some (item.1, upper)) := by
  induction out with
  | nil => rfl
  | cons item rest ih => cases item with | mk endpoint decision => cases decision <;> simp [fold, ih]

/-- Counts establish preservation even for repeated occurrences of the same
unmatched endpoint. No family equivalence or canonical image is consulted. -/
theorem unmatched_count (c : Context Artifact Id Term Fact) (original : List (Endpoint Id))
    (out : List (Endpoint Id × Decision)) (accepted : plan c original = some out)
    (upper endpoint : Endpoint Id) (different : endpoint ≠ target c) :
    (fold upper out).count (endpoint, upper) = original.count endpoint := by
  induction original generalizing out with
  | nil => simp [plan] at accepted; subst out; rfl
  | cons head rest ih =>
    cases hd : decideEndpoint c head with
    | none => simp [plan, hd] at accepted
    | some decision =>
      cases ht : plan c rest with
      | none => simp [plan, hd, ht] at accepted
      | some tail =>
        have equal : (head, decision) :: tail = out := by simpa [plan, hd, ht] using accepted
        subst out
        have inductionResult := ih tail ht
        cases decision with
        | suppress =>
          have same := ((suppression_iff c head).mp hd).1
          have distinct : head ≠ endpoint := fun equal => different (equal ▸ same)
          simp [fold, distinct, inductionResult]
        | forward =>
          by_cases same : head = endpoint
          · subst head; simp [fold, inductionResult]
          · simp [fold, same, inductionResult]

/-- A same-family sibling is preserved under its exact distinct native key. -/
theorem same_family_sibling_preserved (c : Context Artifact Id Term Fact)
    (original : List (Endpoint Id)) (out : List (Endpoint Id × Decision))
    (accepted : plan c original = some out) (upper sibling : Endpoint Id)
    (familyOf : Endpoint Id → Option Id) (sameFamily : familyOf sibling = some c.query.family)
    (different : sibling ≠ target c) :
    familyOf sibling = some c.query.family ∧
      (fold upper out).count (sibling, upper) = original.count sibling :=
  ⟨sameFamily, unmatched_count c original out accepted upper sibling different⟩

/-- If suppression cannot authenticate, a matching original endpoint prevents
all publication. The pure plan must finish before its fold is available. -/
theorem unavailable_no_publication (c : Context Artifact Id Term Fact)
    (original : List (Endpoint Id)) (upper : Endpoint Id)
    (present : target c ∈ original) (matching : providerCandidate c (target c) = some true)
    (unavailable : authenticate c = false)
    (selectedMatch : classifyIdentity c = .authenticatedMatch) :
    plan c original = none ∧ publish c original upper = none := by
  have failure : plan c original = none := by
    induction original with
    | nil => cases present
    | cons head rest ih =>
      rcases List.mem_cons.mp present with same | later
      · subst head; simp [plan, decideEndpoint, selectedMatch, matching, unavailable]
      · have tail := ih later
        simp [plan, tail]
  exact ⟨failure, by simp [publish, failure]⟩

/-- Direct parent use at a suppressed original occurrence. Authentication is
obtained from the accepted plan, not assumed from a family match. The remaining
parent premises are source extraction/rules and actual native execution. -/
theorem accepted_suppression_applies (c : Context Artifact Id Term Fact)
    (original : List (Endpoint Id)) (out : List (Endpoint Id × Decision))
    (accepted : plan c original = some out) (endpoint : Endpoint Id)
    (suppressed : (endpoint, .suppress) ∈ out) :
    endpoint = target c ∧ Authenticated c ∧
    c.internal.permission = c.internalProbe.permission ∧
    Arrival c.inputs endpoint (.effectRow c.internal.permission.entry) ∧
    Arrival c.inputs endpoint c.query.catchInput ∧ ArmReads c.source c.query c.probe.selection := by
  have decision := (plan_correspondence c original out accepted).2 endpoint .suppress suppressed
  obtain ⟨same, auth⟩ := (suppression_iff c endpoint).mp decision
  have prerequisites := authenticated_prerequisites c auth
  rcases prerequisites with ⟨permission, _, _, _, _, _, _, _, entry, _, _, catchArrival, arm⟩
  exact ⟨same, of_decide_eq_true auth, permission, same ▸ entry, same ▸ catchArrival, arm⟩

omit [DecidableEq Artifact] [DecidableEq Fact] in
/-- Open tails and stale/wrong views, ordinals or operands cannot authorize
a logical support step. Physical-emission evidence cannot repair these reads. -/
theorem invalid_support_rejected (e : Inputs Artifact Id Fact) (s : SupportMember Id)
    (bad : e.supportView s.support ≠ some s.viewIndex ∨
      e.arrival.views s.viewIndex ≠ some s.view ∨
      e.arrival.nativeAtom s.member ≠ some (.annotationMember s.viewIndex s.ordinal) ∨
      s.view.allowed[s.ordinal]? ≠ some s.family ∨ s.view.tail ≠ none) :
    pathCheck e (.effectAtom s.support) [.supportMember s] (.effectAtom s.member) = false := by
  have invalid : ¬ SupportReads e s := by
    rintro ⟨support, view, member, family, tail⟩
    rcases bad with h | h | h | h | h <;> contradiction
  simp [pathCheck, StepReads, invalid]

/-- The path inventory is an extracted input, not a proved complete search.
Within that input, a missing or ambiguous path or wrong arm is unavailable. -/
theorem evidence_gap_rejected (c : Context Artifact Id Term Fact)
    (bad : c.inputs.pathCandidates (.effectRow c.entryQuery.rawEntry) (.effectAtom c.probe.terminal.atom) ≠
        [.physical c.entryProbe :: c.probe.entryTail] ∨
      c.inputs.pathCandidates c.query.catchInput (.effectAtom c.probe.terminal.atom) ≠ [c.probe.catchPath] ∨
      ¬ ArmReads c.source c.query c.probe.selection) : authenticate c = false := by
  have invalid : ¬ Authenticated c := by
    rintro ⟨_, _, _, _, _, _, _, entry, catchPath, _, _, _, _, _, arm⟩
    rcases bad with h | h | h <;> contradiction
  simp [authenticate, invalid]

/-- Finite shared-witness instance. This constructs a logical Support step
on both paths, rather than assuming that any Rust run reached it. -/
def witnessView : ProviderEntryArrivalR48.View Nat := ⟨.operation 30 31, 32, [7], none⟩
def witnessSupport : SupportMember Nat := ⟨6, 7, 0, 0, 7, witnessView⟩
def witnessBound : Bound Nat := ⟨.effect 4, .positive, .effectAtom 6⟩
def witnessAdmission : Admission Nat := ⟨witnessBound, some 1⟩
def witnessEmission : Emission Nat :=
  ⟨0, witnessBound, CurrentEmissionOwnershipR47.witnessSlot,
    ⟨CurrentEmissionOwnershipR47.witnessSlot, witnessBound⟩⟩
def witnessEntry : CurrentEmissionOwnershipR47.Probe Nat :=
  ⟨0, 0, witnessAdmission, witnessEmission, 1, [1]⟩
def witnessSteps : List (Step Nat) := [.physical witnessEntry, .supportMember witnessSupport]
def witnessCurrent : CurrentEmissionOwnershipR47.Inputs Nat Nat Nat :=
  { CurrentEmissionOwnershipR47.witnessInputs with
    admissions := [witnessAdmission]
    emissions := [witnessEmission]
    effectRows := fun row => if row = 4 then some ⟨[], [], [6], []⟩ else none
    relationPair := fun relation => if relation = 1 then some (boundPair witnessBound) else none
    sourceFact := fun key => if key = (200, 51) then some 300 else
      CurrentEmissionOwnershipR47.witnessInputs.sourceFact key }
def witnessArrival : ProviderEntryArrivalR48.Inputs Nat Nat Nat :=
  ⟨witnessCurrent, (fun occurrence => if occurrence = 200 then [300] else []),
    (fun fact => if fact = 300 then some (200, 51) else none),
    (fun fact => if fact = 300 then some (.effectRow 4, .effectRow 9) else none),
    (fun atom => if atom = 7 then some (.annotationMember 0 0) else some .other),
    (fun view => if view = 0 then some witnessView else none),
    (fun provider => if provider = 30 then some (31, 7) else none)⟩
def witnessSelection : Selection Nat := ⟨400, 0, 401, (10, 20), 402, 403, 31, 7⟩
def witnessSource : SourceInputs Nat :=
  ⟨(fun occurrence => if occurrence = 400 then
      some ⟨400, 200, [⟨401, (10, 20), .operation 402 31 7 [.unitSyntax 403] .wildcard⟩,
        ⟨404, (21, 25), .value (.binder 405)⟩]⟩ else none),
    (fun source => if source = 402 then some (31, 7) else none)⟩
def witnessContext : Context Nat Nat Nat Nat :=
  ⟨InternalPermissionIncidenceR45.witnessInputs, InternalPermissionIncidenceR45.witnessQuery,
    InternalPermissionIncidenceR45.witnessProbe,
    InternalPermissionIncidenceR45.certificate InternalPermissionIncidenceR45.witnessQuery
      InternalPermissionIncidenceR45.witnessProbe,
    ⟨witnessArrival, (fun atom => if atom = 6 then some 0 else none),
      (fun root terminal => if root = .effectRow 4 ∧ terminal = .effectAtom 7 then [witnessSteps] else []),
      (fun provider declaration family => if provider = 30 ∧ declaration = 31 ∧ family = 7 then [7] else [])⟩,
    witnessSource, CurrentEmissionOwnershipR47.witnessQuery, witnessEntry,
    ⟨200, 300, .effectRow 4, .effectRow 9, 30, 31, 7⟩,
    ⟨[.supportMember witnessSupport], witnessSteps, ⟨[], [], 7, 0, 0, witnessView⟩, witnessSelection⟩⟩

/-- Same nominal family, distinct native atom 8, preserved twice. Neither the
family equality nor the provider's own suppression authorizes deleting it. -/
theorem concrete_support_and_sibling_witness :
    authenticate witnessContext = true ∧
    decide (SupportReads witnessContext.inputs witnessSupport) = true ∧
    pathCheck witnessContext.inputs (.effectRow 4) witnessSteps (.effectAtom 7) = true ∧
    (fun endpoint : Endpoint Nat => if endpoint = .effectAtom 7 ∨ endpoint = .effectAtom 8 then some 7 else none)
      (.effectAtom 8) = some witnessContext.query.family ∧
    (Endpoint.effectAtom 8 : Endpoint Nat) ≠ target witnessContext ∧
    plan witnessContext [.effectAtom 7, .effectAtom 8, .effectAtom 8] =
      some [(.effectAtom 7, .suppress), (.effectAtom 8, .forward), (.effectAtom 8, .forward)] ∧
    publish witnessContext [.effectAtom 7, .effectAtom 8, .effectAtom 8] (.effectRow 9) =
      some [(.effectAtom 8, .effectRow 9), (.effectAtom 8, .effectRow 9)] := by decide

/-- A successful projected publication has one complete accepted plan; no
prefix of an unavailable plan has a projected published result. -/
theorem publication_has_complete_plan (c : Context Artifact Id Term Fact)
    (original : List (Endpoint Id)) (upper : Endpoint Id)
    (constraints : List (Endpoint Id × Endpoint Id))
    (published : publish c original upper = some constraints) :
    ∃ out, plan c original = some out ∧ out.map Prod.fst = original ∧
      constraints = fold upper out ∧
      ∀ endpoint decision, (endpoint, decision) ∈ out → decideEndpoint c endpoint = some decision := by
  cases hp : plan c original with
  | none => simp [publish, hp] at published
  | some out =>
    have equal : fold upper out = constraints := by simpa [publish, hp] using published
    have correspondence := plan_correspondence c original out hp
    exact ⟨out, rfl, correspondence.1, equal.symm, correspondence.2⟩

theorem published_unmatched_count (c : Context Artifact Id Term Fact)
    (original : List (Endpoint Id)) (upper : Endpoint Id)
    (constraints : List (Endpoint Id × Endpoint Id))
    (published : publish c original upper = some constraints)
    (endpoint : Endpoint Id) (different : endpoint ≠ target c) :
    constraints.count (endpoint, upper) = original.count endpoint := by
  obtain ⟨out, accepted, _, rfl, _⟩ := publication_has_complete_plan c original upper constraints published
  exact unmatched_count c original out accepted upper endpoint different

/-- Finite negative instances: stale current storage, reversed owning polarity,
a disconnected typed path, duplicate inventory, wrong source-arm position, and
a same-family foreign provider never authorize matching-endpoint suppression. -/
theorem concrete_authentication_failures :
    authenticate { witnessContext with inputs := { witnessContext.inputs with
      arrival := { witnessArrival with current := { witnessCurrent with effectRows := fun _ => none } } } } = false ∧
    authenticate { witnessContext with entryProbe := { witnessEntry with
      admission := { witnessAdmission with bound := { witnessBound with polarity := .negative } } } } = false ∧
    authenticate { witnessContext with probe := { witnessContext.probe with entryTail := [] } } = false ∧
    authenticate { witnessContext with inputs := { witnessContext.inputs with
      pathCandidates := fun _ _ => [witnessSteps, witnessSteps] } } = false ∧
    authenticate { witnessContext with inputs := { witnessContext.inputs with
      providerCandidates := fun _ _ _ => [7, 8] } } = false ∧
    authenticate { witnessContext with probe := { witnessContext.probe with
      selection := { witnessSelection with position := 1 } } } = false ∧
    authenticate { witnessContext with query := { witnessContext.query with provider := 33 } } = false ∧
    authenticate { witnessContext with query := { witnessContext.query with declaration := 34 } } = false ∧
    publish { witnessContext with inputs := { witnessContext.inputs with
      providerCandidates := fun _ _ _ => [7, 8] } } [.effectAtom 7] (.effectRow 9) = none ∧
    pathCheck witnessContext.inputs (.effectAtom 6)
      [.supportMember { witnessSupport with view := { witnessView with tail := some 35 } }]
      (.effectAtom 7) = false ∧
    publish { witnessContext with probe := { witnessContext.probe with
      selection := { witnessSelection with position := 1 } } }
      [.effectAtom 8, .effectAtom 7] (.effectRow 9) = none := by decide

/-- Failure at any original endpoint blocks the whole immutable publication,
including a late failure after earlier forward decisions were constructed. -/
theorem unavailable_endpoint_blocks (c : Context Artifact Id Term Fact)
    (original : List (Endpoint Id)) (upper endpoint : Endpoint Id)
    (present : endpoint ∈ original) (unavailable : decideEndpoint c endpoint = none) :
    plan c original = none ∧ publish c original upper = none := by
  have failure : plan c original = none := by
    induction original with
    | nil => cases present
    | cons head rest ih =>
      rcases List.mem_cons.mp present with same | later
      · subst head; simp [plan, unavailable]
      · have tail := ih later
        simp [plan, tail]
  exact ⟨failure, by simp [publish, failure]⟩

/-- A matching provider-origin candidate has no successful fallback if it is
not the unique authenticated terminal, or if any authentication check fails. -/
theorem matching_gap_no_publication (c : Context Artifact Id Term Fact)
    (original : List (Endpoint Id)) (upper endpoint : Endpoint Id)
    (present : endpoint ∈ original) (matching : providerCandidate c endpoint = some true)
    (gap : endpoint ≠ target c ∨ authenticate c = false)
    (selectedMatch : classifyIdentity c = .authenticatedMatch) :
    plan c original = none ∧ publish c original upper = none := by
  apply unavailable_endpoint_blocks c original upper endpoint present
  rcases gap with different | unavailable
  · simp [decideEndpoint, selectedMatch, matching, different]
  · simp [decideEndpoint, selectedMatch, matching, unavailable]

/-- A known mismatch is usable only after both owner reads succeed. Every
valid native endpoint then forwards, including the exact provider terminal. -/
theorem known_unmatched_decision (c : Context Artifact Id Term Fact) (endpoint : Endpoint Id)
    (known : classifyIdentity c = .knownUnmatched) (candidate : Bool)
    (native : providerCandidate c endpoint = some candidate) :
    decideEndpoint c endpoint = some .forward := by simp [decideEndpoint, known, native]

theorem known_unmatched_plan (c : Context Artifact Id Term Fact) (original : List (Endpoint Id))
    (known : classifyIdentity c = .knownUnmatched)
    (valid : ∀ endpoint ∈ original, ∃ candidate, providerCandidate c endpoint = some candidate) :
    plan c original = some (original.map (fun endpoint => (endpoint, Decision.forward))) := by
  induction original with
  | nil => rfl
  | cons head rest ih =>
    obtain ⟨candidate, native⟩ := valid head (by simp)
    have tail := ih (fun endpoint member => valid endpoint (List.mem_cons_of_mem head member))
    simp [plan, known_unmatched_decision c head known candidate native, tail]

omit [DecidableEq Id] in
theorem fold_all_forward (upper : Endpoint Id) (original : List (Endpoint Id)) :
    fold upper (original.map (fun endpoint => (endpoint, Decision.forward))) =
      original.map (fun endpoint => (endpoint, upper)) := by
  induction original with
  | nil => rfl
  | cons head rest ih => simp [fold, ih]

theorem known_unmatched_publish (c : Context Artifact Id Term Fact) (original : List (Endpoint Id))
    (upper : Endpoint Id) (known : classifyIdentity c = .knownUnmatched)
    (valid : ∀ endpoint ∈ original, ∃ candidate, providerCandidate c endpoint = some candidate) :
    publish c original upper = some (original.map (fun endpoint => (endpoint, upper))) := by
  simp only [publish, known_unmatched_plan c original known valid, Option.map_some, fold_all_forward]

/-- Missing owner evidence never supplies either a mismatch or a successful
forward decision, independently of any native endpoint/family comparison. -/
theorem unknown_identity_unavailable (c : Context Artifact Id Term Fact)
    (missing : ¬ IdentityReads c) :
    classifyIdentity c = .unavailable ∧ classifyIdentity c ≠ .knownUnmatched ∧
    ∀ endpoint, decideEndpoint c endpoint = none := by
  have unavailable : classifyIdentity c = .unavailable := by simp [classifyIdentity, missing]
  exact ⟨unavailable, by simp [unavailable], fun endpoint => by simp [decideEndpoint, unavailable]⟩

theorem suppression_complete_authentication (c : Context Artifact Id Term Fact)
    (endpoint : Endpoint Id) (suppressed : decideEndpoint c endpoint = some .suppress) :
    classifyIdentity c = .authenticatedMatch ∧ Authenticated c ∧
    InternalPermissionIncidenceR45.extract c.internalInputs c.internalQuery c.internalProbe = some c.internal ∧
    CurrentEmissionOwnershipR47.extract c.inputs.arrival.current c.entryQuery c.entryProbe =
      some ⟨c.entryQuery, c.entryProbe⟩ ∧
    c.internal.permission = c.internalProbe.permission ∧
    Arrival c.inputs endpoint (.effectRow c.internal.permission.entry) ∧
    Arrival c.inputs endpoint c.query.catchInput ∧ ArmReads c.source c.query c.probe.selection := by
  obtain ⟨same, auth⟩ := (suppression_iff c endpoint).mp suppressed
  have h : Authenticated c := of_decide_eq_true auth
  have prerequisites := authenticated_prerequisites c auth
  rcases prerequisites with ⟨permission, _, entry, _, _, _, _, _, arrives, _, _, catches, arm⟩
  exact ⟨authenticated_identity_match c auth, h, h.1, entry, permission,
    same ▸ arrives, same ▸ catches, arm⟩

/-- Signal arm identity 40/family 41 and write provider identity 31/family 7
are both resolved, while the permission continues to allow the arm family. -/
def knownUnmatchedContext : Context Nat Nat Nat Nat :=
  let permission := { InternalPermissionIncidenceR45.witnessProbe.permission with concrete := [41] }
  let internalProbe := { InternalPermissionIncidenceR45.witnessProbe with permission }
  { witnessContext with
    internalInputs := { InternalPermissionIncidenceR45.witnessInputs with permissions := [permission] }
    internalProbe := internalProbe
    internal := InternalPermissionIncidenceR45.certificate InternalPermissionIncidenceR45.witnessQuery internalProbe
    source := ⟨(fun occurrence => if occurrence = 400 then
      some ⟨400, 200, [⟨401, (10, 20), .operation 402 40 41 [.unitSyntax 403] .wildcard⟩,
        ⟨404, (21, 25), .value (.binder 405)⟩]⟩ else none),
      (fun source => if source = 402 then some (40, 41) else none)⟩
    probe := { witnessContext.probe with selection := { witnessSelection with declaration := 40, family := 41 } } }

/-- Constructed before assuming any accepted plan: the provider terminal itself
survives twice, with a distinct sibling and complete original ordering retained. -/
theorem concrete_known_unmatched_forwarding :
    IdentityReads knownUnmatchedContext ∧
    InternalPermissionIncidenceR45.extract knownUnmatchedContext.internalInputs
      knownUnmatchedContext.internalQuery knownUnmatchedContext.internalProbe = some knownUnmatchedContext.internal ∧
    classifyIdentity knownUnmatchedContext = .knownUnmatched ∧
    providerCandidate knownUnmatchedContext (.effectAtom 7) = some true ∧
    authenticate knownUnmatchedContext = false ∧
    plan knownUnmatchedContext [.effectAtom 7, .effectAtom 8, .effectAtom 7] =
      some [(.effectAtom 7, .forward), (.effectAtom 8, .forward), (.effectAtom 7, .forward)] ∧
    publish knownUnmatchedContext [.effectAtom 7, .effectAtom 8, .effectAtom 7] (.effectRow 9) =
      some [(.effectAtom 7, .effectRow 9), (.effectAtom 8, .effectRow 9), (.effectAtom 7, .effectRow 9)] := by decide

/-- Equal spellings are immaterial to comparison of authenticated full keys. -/
theorem concrete_same_spelling_distinct_identities :
    (fun _ : Nat => "ping") knownUnmatchedContext.probe.selection.declaration =
      (fun _ : Nat => "ping") knownUnmatchedContext.query.declaration ∧
    knownUnmatchedContext.probe.selection.declaration ≠ knownUnmatchedContext.query.declaration ∧
    classifyIdentity knownUnmatchedContext = .knownUnmatched ∧
    publish knownUnmatchedContext [.effectAtom 7] (.effectRow 9) = some [(.effectAtom 7, .effectRow 9)] := by decide

/-- Missing source/arm reads are unavailable; a matching operation missing
permission or arrival stays unavailable; full matching suppression still works. -/
theorem concrete_r50_classification_boundaries :
    classifyIdentity { knownUnmatchedContext with inputs := { knownUnmatchedContext.inputs with
      arrival := { witnessArrival with sourceOperation := fun _ => none } } } = .unavailable ∧
    publish { knownUnmatchedContext with inputs := { knownUnmatchedContext.inputs with
      arrival := { witnessArrival with sourceOperation := fun _ => none } } }
      [.effectAtom 7] (.effectRow 9) = none ∧
    classifyIdentity { knownUnmatchedContext with source := { knownUnmatchedContext.source with
      catchSource := fun _ => none } } = .unavailable ∧
    classifyIdentity witnessContext = .authenticatedMatch ∧
    decideEndpoint { witnessContext with internalInputs := { witnessContext.internalInputs with permissions := [] } }
      (.effectAtom 7) = none ∧
    decideEndpoint { witnessContext with inputs := { witnessContext.inputs with pathCandidates := fun _ _ => [] } }
      (.effectAtom 7) = none ∧
    decideEndpoint witnessContext (.effectAtom 7) = some .suppress := by decide

end YulangClosure.AuthenticatedResidualConsumerR49
