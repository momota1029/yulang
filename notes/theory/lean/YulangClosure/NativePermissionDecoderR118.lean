import YulangClosure.SuppressionPermissionR116

/-!
R118 CONSTRUCTED / UNCHECKED: no Lean/Lake/checker execution or axiom receipt.
This is finite conditional mathematics over interpreted owner reads, NOT an
operational interpretation of Rust. No source domain is defined here.

The R117 revision-2 consumer reads the native view/member, selects a unique
permission by registration, checks its separate packed storage index, and
runs concrete.iter().any. The following transcribes just those reads/guards.
All other R117 guards remain outside this partial model. In particular this
is NOT an acceptance predicate for Suppress or for the complete decoder.

First source bridge: reconstruct the PRE-state of candidate_formal_entry_annotation,
its exact Action::FormalEntry and the same source annotation row. The retained
POST-state cannot itself satisfy R39's no-previous-registration check. R45
owner/route/native-function reads, operation/declaration decoding and R54 pointer
interpretation remain open independently. No prepare/permissionFor/extract or
membership premise is used to claim these have been constructed.
-/
namespace YulangClosure.NativePermissionDecoderR118

open ComputationPermissionEntryR39
open OwnedResidualProjectionR54 (Owner)

structure Endpoint where
  view : Nat
  member : Nat
  deriving DecidableEq

variable {Id State Batch : Type} [DecidableEq Id]

/-- Recursive transcription of equality-based iter().any, without set conversion. -/
def contains : List Id → Id → Bool
  | [], _ => false
  | first :: rest, family => if first = family then true else contains rest family

theorem contains_member (xs : List Id) (family : Id)
    (checked : contains xs family = true) : family ∈ xs := by
  induction xs with
  | nil => simp [contains] at checked
  | cons first rest ih =>
    by_cases same : first = family
    · subst first; simp
    · have tail : contains rest family = true := by
        simpa only [contains, same, ↓reduceIte] using checked
      exact List.mem_cons_of_mem first (ih tail)

/-- The inventory ordinal is checked before indexing the allowed vector.
Endpoint.member is never interpreted as an effect-family identity. -/
def readFamily (views : List (Nat × List Id)) (endpoint : Endpoint) : Option Id := do
  let entry ← views[endpoint.view]?
  if entry.1 = endpoint.view then entry.2[endpoint.member]? else none

/-- Registration-keyed uniqueness; storage is a different coordinate. -/
def matching (permissions : List (Nat × Permission Id)) (registration : Nat) :=
  permissions.filter (fun entry => entry.2.registration == registration)

def readPermission (permissions : List (Nat × Permission Id))
    (registration storage : Nat) : Option (Permission Id) :=
  match matching permissions registration with
  | [(index, permission)] => if index = storage then some permission else none
  | _ => none

/-- Partial projection of the consumer guard, not the full Rust success predicate.
The selected value is read from the unique retained inventory record itself. -/
def decode [DecidableEq State] [DecidableEq Batch]
    (permissionOwner viewOwner : Owner State Batch)
    (views : List (Nat × List Id)) (permissions : List (Nat × Permission Id))
    (endpoint : Endpoint) (registration storage : Nat) : Option (Id × Permission Id) :=
  if permissionOwner = viewOwner then do
    let family ← readFamily views endpoint
    let permission ← readPermission permissions registration storage
    if contains permission.concrete family then some (family, permission) else none
  else none

theorem read_family_exact (views : List (Nat × List Id)) (endpoint : Endpoint)
    (family : Id) (read : readFamily views endpoint = some family) :
    ∃ allowed, views[endpoint.view]? = some (endpoint.view, allowed) ∧
      allowed[endpoint.member]? = some family := by
  cases found : views[endpoint.view]? with
  | none => simp [readFamily, found] at read
  | some entry =>
    rcases entry with ⟨index, allowed⟩
    by_cases same : index = endpoint.view
    · subst index
      exact ⟨allowed, rfl, by simpa [readFamily, found] using read⟩
    · simp [readFamily, found, same] at read

theorem read_permission_exact (permissions : List (Nat × Permission Id))
    (registration storage : Nat) (permission : Permission Id)
    (read : readPermission permissions registration storage = some permission) :
    matching permissions registration = [(storage, permission)] := by
  cases found : matching permissions registration with
  | nil => simp [readPermission, found] at read
  | cons first rest =>
    rcases first with ⟨index, value⟩
    cases rest with
    | nil =>
      by_cases same : index = storage
      · subst index
        have equal : value = permission := by
          simpa [readPermission, found] using read
        simpa only [equal] using found
      · simp [readPermission, found, same] at read
    | cons second tail => simp [readPermission, found] at read

/-- Membership follows from the actual recursive any-guard after BOTH reads.
No source membership, producer equation or R45 acceptance is assumed. -/
theorem decode_member [DecidableEq State] [DecidableEq Batch]
    (permissionOwner viewOwner : Owner State Batch)
    (views : List (Nat × List Id)) (permissions : List (Nat × Permission Id))
    (endpoint : Endpoint) (registration storage : Nat)
    (family : Id) (permission : Permission Id)
    (success : decode permissionOwner viewOwner views permissions endpoint registration storage =
      some (family, permission)) :
    permissionOwner = viewOwner ∧
      (∃ allowed, views[endpoint.view]? = some (endpoint.view, allowed) ∧
        allowed[endpoint.member]? = some family) ∧
      matching permissions registration = [(storage, permission)] ∧
      family ∈ permission.concrete := by
  by_cases owners : permissionOwner = viewOwner
  · cases rf : readFamily views endpoint with
    | none => simp [decode, owners, rf] at success
    | some actualFamily =>
      cases rp : readPermission permissions registration storage with
      | none => simp [decode, owners, rf, rp] at success
      | some actualPermission =>
        by_cases guard : contains actualPermission.concrete actualFamily = true
        · have same : (actualFamily, actualPermission) = (family, permission) := by
            simpa [decode, owners, rf, rp, guard] using success
          have sf := congrArg Prod.fst same
          have sp := congrArg Prod.snd same
          cases sf
          cases sp
          exact ⟨owners, read_family_exact views endpoint family rf,
            read_permission_exact permissions registration storage permission rp,
            contains_member permission.concrete family guard⟩
        · simp [decode, owners, rf, rp, guard] at success
  · simp [decode, owners] at success

/-- Registration 1 occupies packed slot 0; native member 1 decodes family 7.
These numbers deliberately belong to different namespaces. -/
def examplePermission : Permission Nat :=
  { InternalPermissionIncidenceR45.witnessProbe.permission with registration := 1 }

theorem unequal_coordinates :
    decode (⟨9, 10⟩ : Owner Nat Nat) ⟨9, 10⟩ [(0, [99, 7])]
      [(0, examplePermission)] ⟨0, 1⟩ 1 0 = some (7, examplePermission) ∧
      (1 : Nat) ≠ 0 ∧ (1 : Nat) ≠ 7 := by decide

/-- A real published record leaves its registration present in the post-state.
The decoder's membership check does not recover the earlier constructor state. -/
def postInputs : Inputs Nat :=
  { InternalPermissionIncidenceR45.witnessInputs.source with retainedRegistrations := [0] }

theorem post_state_is_not_prepare_input :
    decode (⟨9, 10⟩ : Owner Nat Nat) ⟨9, 10⟩ [(0, [7])]
      [(0, InternalPermissionIncidenceR45.witnessProbe.permission)] ⟨0, 0⟩ 0 0 =
        some (7, InternalPermissionIncidenceR45.witnessProbe.permission) ∧
      prepare postInputs InternalPermissionIncidenceR45.witnessAction = none := by decide

end YulangClosure.NativePermissionDecoderR118

-- FUTURE audit commands: no outputs or axiom sets have been observed.
#check @YulangClosure.NativePermissionDecoderR118.contains_member
#print axioms YulangClosure.NativePermissionDecoderR118.contains_member
#check @YulangClosure.NativePermissionDecoderR118.read_family_exact
#print axioms YulangClosure.NativePermissionDecoderR118.read_family_exact
#check @YulangClosure.NativePermissionDecoderR118.read_permission_exact
#print axioms YulangClosure.NativePermissionDecoderR118.read_permission_exact
#check @YulangClosure.NativePermissionDecoderR118.decode_member
#print axioms YulangClosure.NativePermissionDecoderR118.decode_member
#check @YulangClosure.NativePermissionDecoderR118.unequal_coordinates
#print axioms YulangClosure.NativePermissionDecoderR118.unequal_coordinates
#check @YulangClosure.NativePermissionDecoderR118.post_state_is_not_prepare_input
#print axioms YulangClosure.NativePermissionDecoderR118.post_state_is_not_prepare_input
