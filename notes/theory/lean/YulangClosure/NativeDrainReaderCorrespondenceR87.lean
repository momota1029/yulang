import YulangClosure.NativeRootPremisesR85

/-!
R87 candidate. These are finite data readers, with separate relational
specifications. No failed R86 declaration is imported. Task, cause, replay
acknowledgement and reference identities remain arbitrary payloads. The full
receipt clone comparison includes drainIndex. Native extraction, pointer-token
authenticity and the non-receipt saved-consumer prelude remain open.
-/
namespace YulangClosure.NativeDrainReaderCorrespondenceR87

def selectSingleton {A : Type} : List A → Option A
  | [a] => some a
  | _ => none

theorem singleton_some_iff {A : Type} (xs : List A) (a : A) :
    selectSingleton xs = some a ↔ xs = [a] := by
  cases xs with
  | nil => simp [selectSingleton]
  | cons first rest =>
      cases rest with
      | nil => simp [selectSingleton]
      | cons second tail => simp [selectSingleton]

theorem singleton_multiple {A : Type} (a b : A) (rest : List A) :
    selectSingleton (a :: b :: rest) = none := rfl

def gate {A : Type} (condition : Prop) [Decidable condition] (a : A) : Option A :=
  if condition then some a else none

theorem gate_some_iff {A : Type} (condition : Prop) [Decidable condition] (a b : A) :
    gate condition a = some b ↔ condition ∧ a = b := by
  by_cases h : condition <;> simp [gate, h]

def enumerateFrom {A : Type} : Nat → List A → List (Nat × A)
  | _, [] => []
  | index, a :: rest => (index, a) :: enumerateFrom (index + 1) rest

structure Receipt (Cause Task Ack : Type) where
  drainIndex : Nat
  incoming : Option Nat
  replayAck : Option Ack
  createdSeed : Nat
  selectedRelation : Nat
  originIndex : Nat
  task : Task
  cause : Cause
  completed : Bool
  deriving DecidableEq

structure Attachment (Cause Task Ack Ref : Type) where
  identity : Ref
  receipt : Receipt Cause Task Ack

structure Origin (Occ Cause Task Ack Ref Meta : Type) where
  identity : Ref
  relation : Nat
  occurrence : Occ
  metadata : Meta
  attached : Option (Attachment Cause Task Ack Ref)

structure Context (Occ Cause Task Ack Ref Meta Pair Hir : Type) where
  origins : List (Origin Occ Cause Task Ack Ref Meta)
  completions : List (Receipt Cause Task Ack)
  relationPair : Nat → Option Pair
  taskPair : Task → Pair
  causeOccurrence : Cause → Occ
  hirOccurrence : Occ → Hir

variable {Occ Cause Task Ack Ref Meta Pair Hir : Type}
variable [DecidableEq Occ] [DecidableEq Cause] [DecidableEq Task]
variable [DecidableEq Ack] [DecidableEq Ref] [DecidableEq Pair]
variable [DecidableEq Hir]

local notation "Env" => Context Occ Cause Task Ack Ref Meta Pair Hir
local notation "NativeOrigin" => Origin Occ Cause Task Ack Ref Meta
local notation "NativeReceipt" => Receipt Cause Task Ack
local notation "NativeAttachment" => Attachment Cause Task Ack Ref

def clone (p : NativeReceipt) :=
  {p with completed := true}

theorem clone_pending_distinct
    (p : NativeReceipt)
    (pending : p.completed = false) : p ≠ clone p := by
  intro same
  have bit := congrArg Receipt.completed same
  rw [pending] at bit
  cases bit

theorem clone_fields (p : NativeReceipt) :
    (clone p).drainIndex = p.drainIndex ∧
    (clone p).incoming = p.incoming ∧ (clone p).replayAck = p.replayAck ∧
    (clone p).createdSeed = p.createdSeed ∧ (clone p).selectedRelation = p.selectedRelation ∧
    (clone p).originIndex = p.originIndex ∧ (clone p).task = p.task ∧
    (clone p).cause = p.cause ∧ (clone p).completed = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def originCandidates (e : Env) (occurrence : Occ) (pair : Pair) :=
  (enumerateFrom 0 e.origins).filter fun item =>
    decide (item.2.occurrence = occurrence ∧ e.relationPair item.2.relation = some pair)

def completionCandidates (e : Env) (p : NativeReceipt) :=
  (enumerateFrom 0 e.completions).filter fun item => decide (item.2 = clone p)

theorem completionCandidates_single_clone (e : Env) (p : NativeReceipt) :
    completionCandidates {e with completions := [clone p]} p = [(0, clone p)] := by
  simp [completionCandidates, enumerateFrom]

theorem completionCandidates_duplicate_clone (e : Env) (p : NativeReceipt) :
    completionCandidates {e with completions := [clone p, clone p]} p =
      [(0, clone p), (1, clone p)] := by
  simp [completionCandidates, enumerateFrom]

def publicationGuards (e : Env) (occurrence : Occ) (cause : Cause) (task : Task)
    (io : Nat × NativeOrigin) (p : NativeReceipt) : Prop :=
  p.originIndex = io.1 ∧ p.createdSeed = io.2.relation ∧
  p.selectedRelation = io.2.relation ∧ p.task = task ∧ p.cause = cause ∧
  e.causeOccurrence cause = occurrence

instance (e : Env) (occurrence : Occ) (cause : Cause) (task : Task)
    (io : Nat × NativeOrigin) (p : NativeReceipt) :
    Decidable (publicationGuards e occurrence cause task io p) := by
  unfold publicationGuards
  infer_instance

structure Publication (Cause Task Ack Ref : Type) where
  originIndex : Nat
  completionIndex : Nat
  relation : Nat
  attachment : Attachment Cause Task Ack Ref

/-- Pure shared implementation for publication readers. Its candidate lists
remain data; it contains no proof-bearing selector or dependent match. -/
def publicationData (origins : List (Nat × NativeOrigin))
    (completions : NativeReceipt → List (Nat × NativeReceipt))
    (guards : (Nat × NativeOrigin) → NativeReceipt → Prop)
    [∀ io p, Decidable (guards io p)] : Option (Publication Cause Task Ack Ref) := do
  let io ← selectSingleton origins
  let attachment ← io.2.attached
  let completion ← selectSingleton (completions attachment.receipt)
  gate (guards io attachment.receipt)
    ⟨io.1, completion.1, io.2.relation, attachment⟩

/-- Independent field-equation specification of a publication return. -/
def PublicationRel (origins : List (Nat × NativeOrigin))
    (completions : NativeReceipt → List (Nat × NativeReceipt))
    (guards : (Nat × NativeOrigin) → NativeReceipt → Prop)
    (out : Publication Cause Task Ack Ref) : Prop :=
  ∃ io, origins = [io] ∧ ∃ attachment, io.2.attached = some attachment ∧
    ∃ completion, completions attachment.receipt = [completion] ∧
      guards io attachment.receipt ∧
      (⟨io.1, completion.1, io.2.relation, attachment⟩ : Publication Cause Task Ack Ref) = out

theorem publicationData_iff (origins : List (Nat × NativeOrigin))
    (completions : NativeReceipt → List (Nat × NativeReceipt))
    (guards : (Nat × NativeOrigin) → NativeReceipt → Prop)
    [∀ io p, Decidable (guards io p)] (out : Publication Cause Task Ack Ref) :
    publicationData origins completions guards = some out ↔
      PublicationRel origins completions guards out := by
  simp only [publicationData, PublicationRel, Option.bind_eq_bind, Option.bind_eq_some_iff,
    singleton_some_iff, gate_some_iff]

theorem publication_origin_index_unique (origins : List (Nat × NativeOrigin))
    (completions : NativeReceipt → List (Nat × NativeReceipt))
    (guards : (Nat × NativeOrigin) → NativeReceipt → Prop)
    (out : Publication Cause Task Ack Ref) (lawful : PublicationRel origins completions guards out)
    (item : Nat × NativeOrigin) (member : item ∈ origins) : item.1 = out.originIndex := by
  rcases lawful with ⟨io, selected, attachment, attached, completion, completed, checked, same⟩
  subst out
  rw [selected] at member
  exact congrArg Prod.fst (List.mem_singleton.mp member)

theorem publication_completion_index_unique (origins : List (Nat × NativeOrigin))
    (completions : NativeReceipt → List (Nat × NativeReceipt))
    (guards : (Nat × NativeOrigin) → NativeReceipt → Prop)
    (out : Publication Cause Task Ack Ref) (lawful : PublicationRel origins completions guards out)
    (item : Nat × NativeReceipt) (member : item ∈ completions out.attachment.receipt) :
    item.1 = out.completionIndex := by
  rcases lawful with ⟨io, selected, attachment, attached, completion, completed, checked, same⟩
  subst out
  rw [completed] at member
  exact congrArg Prod.fst (List.mem_singleton.mp member)

theorem publicationData_no_origin
    (completions : NativeReceipt → List (Nat × NativeReceipt))
    (guards : (Nat × NativeOrigin) → NativeReceipt → Prop)
    [∀ io p, Decidable (guards io p)] :
    publicationData [] completions guards = none := rfl

theorem publicationData_multiple_origins (first second : Nat × NativeOrigin)
    (rest : List (Nat × NativeOrigin))
    (completions : NativeReceipt → List (Nat × NativeReceipt))
    (guards : (Nat × NativeOrigin) → NativeReceipt → Prop)
    [∀ io p, Decidable (guards io p)] :
    publicationData (first :: second :: rest) completions guards = none := rfl

theorem publicationData_missing_attachment (io : Nat × NativeOrigin)
    (completions : NativeReceipt → List (Nat × NativeReceipt))
    (guards : (Nat × NativeOrigin) → NativeReceipt → Prop)
    [∀ io p, Decidable (guards io p)] (missing : io.2.attached = none) :
    publicationData [io] completions guards = none := by
  simp [publicationData, selectSingleton, missing]

theorem publicationData_no_completion (io : Nat × NativeOrigin)
    (attachment : NativeAttachment)
    (completions : NativeReceipt → List (Nat × NativeReceipt))
    (guards : (Nat × NativeOrigin) → NativeReceipt → Prop)
    [∀ io p, Decidable (guards io p)]
    (attached : io.2.attached = some attachment)
    (missing : completions attachment.receipt = []) :
    publicationData [io] completions guards = none := by
  simp [publicationData, selectSingleton, attached, missing]

theorem publicationData_multiple_completions (io : Nat × NativeOrigin)
    (attachment : NativeAttachment) (first second : Nat × NativeReceipt)
    (rest : List (Nat × NativeReceipt))
    (completions : NativeReceipt → List (Nat × NativeReceipt))
    (guards : (Nat × NativeOrigin) → NativeReceipt → Prop)
    [∀ io p, Decidable (guards io p)]
    (attached : io.2.attached = some attachment)
    (ambiguous : completions attachment.receipt = first :: second :: rest) :
    publicationData [io] completions guards = none := by
  simp [publicationData, selectSingleton, attached, ambiguous]

theorem publicationData_singleton_equation (io : Nat × NativeOrigin)
    (attachment : NativeAttachment) (completion : Nat × NativeReceipt)
    (completions : NativeReceipt → List (Nat × NativeReceipt))
    (guards : (Nat × NativeOrigin) → NativeReceipt → Prop)
    [∀ io p, Decidable (guards io p)]
    (attached : io.2.attached = some attachment)
    (selected : completions attachment.receipt = [completion]) :
    publicationData [io] completions guards =
      gate (guards io attachment.receipt)
        (⟨io.1, completion.1, io.2.relation, attachment⟩ : Publication Cause Task Ack Ref) := by
  simp [publicationData, selectSingleton, attached, selected]

theorem uncut_guards_ignore_completed_bit (e : Env) (occurrence : Occ)
    (cause : Cause) (task : Task) (io : Nat × NativeOrigin) (p : NativeReceipt) :
    publicationGuards e occurrence cause task io (clone p) ↔
      publicationGuards e occurrence cause task io p := Iff.rfl

def readUncut (e : Env) (occurrence : Occ) (cause : Cause) (task : Task) :=
  publicationData (originCandidates e occurrence (e.taskPair task))
    (completionCandidates e) (publicationGuards e occurrence cause task)

def UncutRel (e : Env) (occurrence : Occ) (cause : Cause) (task : Task)
    (out : Publication Cause Task Ack Ref) : Prop :=
  PublicationRel (originCandidates e occurrence (e.taskPair task))
    (completionCandidates e) (publicationGuards e occurrence cause task) out

theorem uncut_sound_complete (e : Env) (occurrence : Occ) (cause : Cause) (task : Task)
    (out : Publication Cause Task Ack Ref) :
    readUncut e occurrence cause task = some out ↔ UncutRel e occurrence cause task out :=
  publicationData_iff _ _ _ out

structure Cuts where
  originCut : Nat
  originEnd : Nat
  completionCut : Nat
  completionEnd : Nat

def validCuts (e : Env) (w : Cuts) : Prop :=
  w.originCut ≤ w.originEnd ∧ w.originEnd ≤ e.origins.length ∧
  w.completionCut ≤ w.completionEnd ∧ w.completionEnd ≤ e.completions.length

instance (e : Env) (w : Cuts) : Decidable (validCuts e w) := by
  unfold validCuts
  infer_instance

def windowOrigins (e : Env) (w : Cuts) (occurrence : Occ) (pair : Pair) :=
  (originCandidates e occurrence pair).filter fun item =>
    decide (w.originCut ≤ item.1 ∧ item.1 < w.originEnd)

def windowCompletions (e : Env) (w : Cuts) (p : NativeReceipt) :=
  (completionCandidates e p).filter fun item =>
    decide (w.completionCut ≤ item.1 ∧ item.1 < w.completionEnd)

def cutGuards (e : Env) (occurrence : Occ) (cause : Cause) (task : Task)
    (io : Nat × NativeOrigin) (p : NativeReceipt) : Prop :=
  publicationGuards e occurrence cause task io p ∧ p.completed = false

instance (e : Env) (occurrence : Occ) (cause : Cause) (task : Task)
    (io : Nat × NativeOrigin) (p : NativeReceipt) :
    Decidable (cutGuards e occurrence cause task io p) := by
  unfold cutGuards
  infer_instance

def readCuts (e : Env) (w : Cuts) (occurrence : Occ) (cause : Cause) (task : Task) :=
  if validCuts e w then
    publicationData (windowOrigins e w occurrence (e.taskPair task))
      (windowCompletions e w) (cutGuards e occurrence cause task)
  else none

theorem readCuts_invalid (e : Env) (w : Cuts) (occurrence : Occ) (cause : Cause) (task : Task)
    (invalid : ¬ validCuts e w) : readCuts e w occurrence cause task = none := by
  simp [readCuts, invalid]

def CutRel (e : Env) (w : Cuts) (occurrence : Occ) (cause : Cause) (task : Task)
    (out : Publication Cause Task Ack Ref) : Prop :=
  validCuts e w ∧
    PublicationRel (windowOrigins e w occurrence (e.taskPair task))
      (windowCompletions e w) (cutGuards e occurrence cause task) out

theorem cuts_sound_complete (e : Env) (w : Cuts) (occurrence : Occ)
    (cause : Cause) (task : Task) (out : Publication Cause Task Ack Ref) :
    readCuts e w occurrence cause task = some out ↔ CutRel e w occurrence cause task out := by
  by_cases valid : validCuts e w
  · rw [readCuts, if_pos valid]
    simp only [CutRel, valid, true_and, publicationData_iff]
  · simp [readCuts, valid, CutRel]

/-- The Internal reader has a distinct bit and incoming/replay policy. -/
def internalGuards (e : Env) (occurrence : Occ) (pair : Pair)
    (io : Nat × NativeOrigin) (attachment : NativeAttachment) : Prop :=
  attachment.receipt.completed = true ∧ attachment.receipt.originIndex = io.1 ∧
  attachment.receipt.createdSeed = io.2.relation ∧
  attachment.receipt.selectedRelation = io.2.relation ∧
  attachment.receipt.incoming = none ∧ attachment.receipt.replayAck = none ∧
  e.causeOccurrence attachment.receipt.cause = occurrence ∧
  e.taskPair attachment.receipt.task = pair

instance (e : Env) (occurrence : Occ) (pair : Pair)
    (io : Nat × NativeOrigin) (attachment : NativeAttachment) :
    Decidable (internalGuards e occurrence pair io attachment) := by
  unfold internalGuards
  infer_instance

structure Internal (Occ Cause Task Ack Ref Meta : Type) where
  originIndex : Nat
  origin : Origin Occ Cause Task Ack Ref Meta
  attachment : Attachment Cause Task Ack Ref

inductive Gap where
  | missing | ambiguous
  deriving DecidableEq

/-- Exact missing/ambiguous branches before checking one Internal candidate. -/
def checkedCandidates {A B : Type} (xs : List A) (check : A → Option B) : Except Gap B :=
  match xs with
  | [] => .error .missing
  | [a] => match check a with
    | none => .error .missing
    | some b => .ok b
  | _ => .error .ambiguous

theorem checkedCandidates_missing {A B : Type} (check : A → Option B) :
    checkedCandidates [] check = .error .missing := rfl

theorem checkedCandidates_multiple {A B : Type} (first second : A) (rest : List A)
    (check : A → Option B) :
    checkedCandidates (first :: second :: rest) check = .error .ambiguous := rfl

theorem checkedCandidates_ok_iff {A B : Type} (xs : List A)
    (check : A → Option B) (b : B) :
    checkedCandidates xs check = .ok b ↔ ∃ a, xs = [a] ∧ check a = some b := by
  cases xs with
  | nil => simp [checkedCandidates]
  | cons a rest =>
      cases rest with
      | nil => cases h : check a <;> simp [checkedCandidates, h]
      | cons second tail => simp [checkedCandidates]

def internalAt (e : Env) (occurrence : Occ) (pair : Pair) (io : Nat × NativeOrigin) :
    Option (Internal Occ Cause Task Ack Ref Meta) := do
  let attachment ← io.2.attached
  gate (internalGuards e occurrence pair io attachment) ⟨io.1, io.2, attachment⟩

def readInternal (e : Env) (occurrence : Occ) (pair : Pair) :=
  checkedCandidates (originCandidates e occurrence pair) (internalAt e occurrence pair)

def InternalRel (e : Env) (occurrence : Occ) (pair : Pair)
    (out : Internal Occ Cause Task Ack Ref Meta) : Prop :=
  ∃ io, originCandidates e occurrence pair = [io] ∧
    ∃ attachment, io.2.attached = some attachment ∧
      internalGuards e occurrence pair io attachment ∧
      (⟨io.1, io.2, attachment⟩ : Internal Occ Cause Task Ack Ref Meta) = out

theorem internal_sound_complete (e : Env) (occurrence : Occ) (pair : Pair)
    (out : Internal Occ Cause Task Ack Ref Meta) :
    readInternal e occurrence pair = .ok out ↔ InternalRel e occurrence pair out := by
  simp only [readInternal, checkedCandidates_ok_iff, internalAt,
    Option.bind_eq_bind, Option.bind_eq_some_iff, gate_some_iff, InternalRel]

/-- Saved consumption supplies an original index, Origin reference and receipt
reference. It does not scan or establish a unique completion. Non-receipt
owner/formal/route/emission checks are an explicit, still-unextracted prelude. -/
structure Saved (Occ Cause Task Ack Ref Meta Hir : Type) where
  index : Nat
  origin : Origin Occ Cause Task Ack Ref Meta
  attachment : Attachment Cause Task Ack Ref
  relation : Nat
  occurrence : Hir
  otherChecks : Bool

def savedGuards (e : Env) (saved : Saved Occ Cause Task Ack Ref Meta Hir)
    (o : NativeOrigin) (attachment : NativeAttachment) : Prop :=
  saved.otherChecks = true ∧ o.identity = saved.origin.identity ∧
  attachment.identity = saved.attachment.identity ∧
  o.relation = saved.relation ∧ e.hirOccurrence o.occurrence = saved.occurrence ∧
  saved.attachment.receipt.originIndex = saved.index ∧
  saved.attachment.receipt.createdSeed = saved.relation ∧
  saved.attachment.receipt.selectedRelation = saved.relation ∧
  e.hirOccurrence (e.causeOccurrence saved.attachment.receipt.cause) = saved.occurrence ∧
  saved.attachment.receipt.completed = true

instance (e : Env) (saved : Saved Occ Cause Task Ack Ref Meta Hir)
    (o : NativeOrigin) (attachment : NativeAttachment) :
    Decidable (savedGuards e saved o attachment) := by
  unfold savedGuards
  infer_instance

def readSaved (e : Env) (saved : Saved Occ Cause Task Ack Ref Meta Hir) :
    Option (Internal Occ Cause Task Ack Ref Meta) := do
  let o ← e.origins[saved.index]?
  let attachment ← o.attached
  gate (savedGuards e saved o attachment) ⟨saved.index, o, attachment⟩

def SavedRel (e : Env) (saved : Saved Occ Cause Task Ack Ref Meta Hir)
    (out : Internal Occ Cause Task Ack Ref Meta) : Prop :=
  ∃ o, e.origins[saved.index]? = some o ∧
    ∃ attachment, o.attached = some attachment ∧ savedGuards e saved o attachment ∧
      (⟨saved.index, o, attachment⟩ : Internal Occ Cause Task Ack Ref Meta) = out

theorem saved_sound_complete (e : Env) (saved : Saved Occ Cause Task Ack Ref Meta Hir)
    (out : Internal Occ Cause Task Ack Ref Meta) :
    readSaved e saved = some out ↔ SavedRel e saved out := by
  simp only [readSaved, SavedRel, Option.bind_eq_bind, Option.bind_eq_some_iff, gate_some_iff]

theorem saved_identity_and_checked_bit (e : Env) (saved : Saved Occ Cause Task Ack Ref Meta Hir)
    (out : Internal Occ Cause Task Ack Ref Meta) (lawful : SavedRel e saved out) :
    out.attachment.identity = saved.attachment.identity ∧
      saved.attachment.receipt.completed = true := by
  rcases lawful with ⟨o, indexed, attachment, attached, guards, same⟩
  subst out
  rcases guards with ⟨other, originRef, receiptRef, relation, occurrence,
    index, created, selected, cause, completed⟩
  exact ⟨receiptRef, completed⟩

/-- Certificates are built only after the plain-data relational theorem. -/
structure PublicationCertificate (e : Env) (occurrence : Occ) (cause : Cause) (task : Task) where
  data : Publication Cause Task Ack Ref
  lawful : UncutRel e occurrence cause task data

def certifyUncut (e : Env) (occurrence : Occ) (cause : Cause) (task : Task)
    (out : Publication Cause Task Ack Ref)
    (success : readUncut e occurrence cause task = some out) :
    PublicationCertificate e occurrence cause task :=
  ⟨out, (uncut_sound_complete e occurrence cause task out).mp success⟩

structure CutCertificate (e : Env) (w : Cuts) (occurrence : Occ) (cause : Cause) (task : Task) where
  data : Publication Cause Task Ack Ref
  lawful : CutRel e w occurrence cause task data

def certifyCuts (e : Env) (w : Cuts) (occurrence : Occ) (cause : Cause) (task : Task)
    (out : Publication Cause Task Ack Ref)
    (success : readCuts e w occurrence cause task = some out) :
    CutCertificate e w occurrence cause task :=
  ⟨out, (cuts_sound_complete e w occurrence cause task out).mp success⟩

structure InternalCertificate (e : Env) (occurrence : Occ) (pair : Pair) where
  data : Internal Occ Cause Task Ack Ref Meta
  lawful : InternalRel e occurrence pair data

def certifyInternal (e : Env) (occurrence : Occ) (pair : Pair)
    (out : Internal Occ Cause Task Ack Ref Meta)
    (success : readInternal e occurrence pair = .ok out) :
    InternalCertificate e occurrence pair :=
  ⟨out, (internal_sound_complete e occurrence pair out).mp success⟩

structure SavedCertificate (e : Env) (saved : Saved Occ Cause Task Ack Ref Meta Hir) where
  data : Internal Occ Cause Task Ack Ref Meta
  lawful : SavedRel e saved data

def certifySaved (e : Env) (saved : Saved Occ Cause Task Ack Ref Meta Hir)
    (out : Internal Occ Cause Task Ack Ref Meta)
    (success : readSaved e saved = some out) : SavedCertificate e saved :=
  ⟨out, (saved_sound_complete e saved out).mp success⟩

theorem cut_receipt_pending (e : Env) (w : Cuts) (occurrence : Occ)
    (cause : Cause) (task : Task) (out : Publication Cause Task Ack Ref)
    (lawful : CutRel e w occurrence cause task out) :
    out.attachment.receipt.completed = false := by
  rcases lawful.2 with ⟨io, origins, attachment, attached, completion, completed, guards, same⟩
  subst out
  exact guards.2

theorem internal_receipt_completed (e : Env) (occurrence : Occ) (pair : Pair)
    (out : Internal Occ Cause Task Ack Ref Meta) (lawful : InternalRel e occurrence pair out) :
    out.attachment.receipt.completed = true := by
  rcases lawful with ⟨io, origins, attachment, attached, guards, same⟩
  subst out
  exact guards.1

theorem cut_and_internal_cannot_share_attachment (e : Env) (w : Cuts) (occurrence : Occ)
    (cause : Cause) (task : Task) (publication : Publication Cause Task Ack Ref)
    (internal : Internal Occ Cause Task Ack Ref Meta)
    (cut : CutRel e w occurrence cause task publication)
    (root : InternalRel e occurrence (e.taskPair task) internal) :
    publication.attachment ≠ internal.attachment := by
  intro same
  have pending := cut_receipt_pending e w occurrence cause task publication cut
  have completed := internal_receipt_completed e occurrence (e.taskPair task) internal root
  rw [same, completed] at pending
  cases pending

theorem uncut_selected_completion (e : Env) (occurrence : Occ) (cause : Cause) (task : Task)
    (out : Publication Cause Task Ack Ref) (lawful : UncutRel e occurrence cause task out) :
    ∃ item ∈ enumerateFrom 0 e.completions,
      item.1 = out.completionIndex ∧ item.2 = clone out.attachment.receipt := by
  rcases lawful with ⟨io, origins, attachment, attached, completion, selected, guards, same⟩
  subst out
  have member : completion ∈ completionCandidates e attachment.receipt := by
    rw [selected]
    simp
  have retained := List.mem_filter.mp member
  exact ⟨completion, retained.1, rfl, of_decide_eq_true retained.2⟩

theorem cuts_selected_completion (e : Env) (w : Cuts) (occurrence : Occ)
    (cause : Cause) (task : Task) (out : Publication Cause Task Ack Ref)
    (lawful : CutRel e w occurrence cause task out) :
    ∃ item ∈ enumerateFrom 0 e.completions,
      item.1 = out.completionIndex ∧ item.2 = clone out.attachment.receipt := by
  rcases lawful.2 with ⟨io, origins, attachment, attached, completion, selected, guards, same⟩
  subst out
  have member : completion ∈ windowCompletions e w attachment.receipt := by
    rw [selected]
    simp
  have full : completion ∈ completionCandidates e attachment.receipt :=
    (List.mem_filter.mp member).1
  have retained := List.mem_filter.mp full
  exact ⟨completion, retained.1, rfl, of_decide_eq_true retained.2⟩

theorem window_origin_competitor_retained (e : Env) (w : Cuts)
    (occurrence : Occ) (pair : Pair) (item : Nat × NativeOrigin)
    (member : item ∈ originCandidates e occurrence pair)
    (inside : w.originCut ≤ item.1 ∧ item.1 < w.originEnd) :
    item ∈ windowOrigins e w occurrence pair :=
  List.mem_filter.mpr ⟨member, by simpa only [decide_eq_true_eq] using inside⟩

theorem window_completion_competitor_retained (e : Env) (w : Cuts)
    (p : NativeReceipt) (item : Nat × NativeReceipt)
    (member : item ∈ completionCandidates e p)
    (inside : w.completionCut ≤ item.1 ∧ item.1 < w.completionEnd) :
    item ∈ windowCompletions e w p :=
  List.mem_filter.mpr ⟨member, by simpa only [decide_eq_true_eq] using inside⟩

/-- Original R84 application remains conditional on original native extraction.
The two-record relation supplies no completed attachment on unchanged Origins. -/
theorem original_R84_pending_obstruction
    {S T : Type} [DecidableEq S] [DecidableEq T]
    (s : OccurrenceQualifiedConsumerR66.Source S T)
    (inventory : OccurrenceQualifiedFactReadersR65.Inventory S T)
    (n : ProviderNativeContextR57.Native S T)
    (q : OccurrenceQualifiedConsumerR66.Request S T)
    (i : OccurrenceQualifiedConsumerR66.Incidence s inventory q) (index : Nat)
    (d : ConstructedPhysicalRootR84.Records S T)
    (pending : NativeRootPremisesR85.Pending n.origins) :
    ¬ ConstructedPhysicalRootR84.Primitive s inventory n q i index d :=
  NativeRootPremisesR85.pending_blocks_R84_primitive s inventory n q i index d pending

/-- Concrete finite forgetful map to unchanged R57 fields. Full native payloads
remain in the reader data; the meaning of these endpoint/cause maps and state
branding must be authenticated by the source owner before native application. -/
def toR57Receipt {T : Type} (state : Nat) (occurrenceOfCause : Cause → Occ)
    (slotOfCause : Cause → Nat)
    (lowerOfTask upperOfTask : Task → ProviderNativeContextR57.Endpoint T)
    (p : NativeReceipt) : ProviderNativeContextR57.Drain Occ T :=
  ⟨state, p.originIndex, p.createdSeed, p.selectedRelation,
    occurrenceOfCause p.cause, slotOfCause p.cause,
    lowerOfTask p.task, upperOfTask p.task, p.incoming, p.replayAck.isSome, p.completed⟩

theorem cut_projection_blocks_R84 {T : Type} [DecidableEq T]
    (e : Env) (w : Cuts) (occurrence : Occ) (cause : Cause) (task : Task)
    (out : Publication Cause Task Ack Ref) (lawful : CutRel e w occurrence cause task out)
    (state : Nat) (slotOfCause : Cause → Nat)
    (lowerOfTask upperOfTask : Task → ProviderNativeContextR57.Endpoint T)
    (s : OccurrenceQualifiedConsumerR66.Source Occ T)
    (inventory : OccurrenceQualifiedFactReadersR65.Inventory Occ T)
    (n : ProviderNativeContextR57.Native Occ T)
    (q : OccurrenceQualifiedConsumerR66.Request Occ T)
    (i : OccurrenceQualifiedConsumerR66.Incidence s inventory q) (index : Nat)
    (d : ConstructedPhysicalRootR84.Records Occ T)
    (sameAttachment : d.origin.drain = some (toR57Receipt state e.causeOccurrence
      slotOfCause lowerOfTask upperOfTask out.attachment.receipt)) :
    ¬ ConstructedPhysicalRootR84.Primitive s inventory n q i index d := by
  intro h
  rcases h with ⟨hs, he, hu, hocc, hstore, hem, ha, hunique, hb, hstate, hslot, hback,
    hcurrent, har, her, hpair, hestate, hastate, heowner, haowner, hpol, heffect,
    hread, hid, hcandidates, horigins, hostate, hoocc, hoslot, hdrain, hindexed,
    hdstate, hseed, hselected, hincoming, hreplay, hcause, hdslot, hdone,
    hlower, hupper, hsource, hslower, hsupper, hv1, hv2⟩
  have sameDrain := Option.some.inj (hdrain.symm.trans sameAttachment)
  have pending := cut_receipt_pending e w occurrence cause task out lawful
  have bit := congrArg ProviderNativeContextR57.Drain.completed sameDrain
  change d.drain.completed = out.attachment.receipt.completed at bit
  rw [hdone, pending] at bit
  cases bit

end YulangClosure.NativeDrainReaderCorrespondenceR87
