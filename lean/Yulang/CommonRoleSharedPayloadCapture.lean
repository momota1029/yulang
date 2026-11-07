import Yulang.CommonRoleStableRecordResidual

/-! Operational capture of approved plain-variable branches. The payload is
kept opaque: the computed finite binding table stores the same supplied
description for every mentioned variable. No pre-merge value is recovered.
This component does not implement the surrounding K2 graph inspection. -/
namespace Yulang.CommonRoleSharedPayloadCapture

open CommonRoleCanonicalRows (Row normalize lookup)

variable {Payload : Type}

def bindings (names : List Nat) (payload : Payload) : Row Payload :=
  normalize (names.map (fun name => (name, payload)))

def assignment (names : List Nat) (payload : Payload) (name : Nat) : Option Payload :=
  lookup name (bindings names payload)

theorem lookup_repeated_payload (names : List Nat) (payload : Payload) (name : Nat) :
    lookup name (names.map (fun name => (name, payload))) =
      if name ∈ names then some payload else none := by
  induction names with
  | nil => rfl
  | cons first rest ih =>
      by_cases same : name = first
      · simp [List.map_cons, lookup, same]
      · simp [List.map_cons, lookup, same, ih]

theorem assignment_exact (names : List Nat) (payload : Payload) (name : Nat) :
    assignment names payload name = if name ∈ names then some payload else none := by
  rw [assignment, bindings, CommonRoleCanonicalRows.lookup_normalize]
  exact lookup_repeated_payload names payload name

theorem captured_as_is (names : List Nat) (payload : Payload) (name : Nat) (mentioned : name ∈ names) :
    assignment names payload name = some payload := by simp [assignment_exact, mentioned]

theorem unmentioned (names : List Nat) (payload : Payload) (name : Nat) (absent : name ∉ names) :
    assignment names payload name = none := by simp [assignment_exact, absent]

theorem bindings_unique (names : List Nat) (payload : Payload) :
    ((bindings names payload).map Prod.fst).Nodup := CommonRoleCanonicalRows.normalize_unique _

/-- Independent specification of the approved branch rule. This is not an
existential decomposition of a Common type. -/
def Captures (names : List Nat) (payload : Payload) (image : Nat → Option Payload) : Prop :=
  (∀ name ∈ names, image name = some payload) ∧ (∀ name ∉ names, image name = none)

theorem capture_sound (names : List Nat) (payload : Payload) : Captures names payload (assignment names payload) :=
  ⟨captured_as_is names payload, unmentioned names payload⟩

theorem capture_complete (names : List Nat) (payload : Payload) (image : Nat → Option Payload)
    (specified : Captures names payload image) : image = assignment names payload := by
  funext name
  by_cases mentioned : name ∈ names
  · exact (specified.1 name mentioned).trans (captured_as_is names payload name mentioned).symm
  · exact (specified.2 name mentioned).trans (unmentioned names payload name mentioned).symm

theorem capture_exact (names : List Nat) (payload : Payload) (image : Nat → Option Payload) :
    Captures names payload image ↔ image = assignment names payload :=
  ⟨capture_complete names payload image, fun equal => equal ▸ capture_sound names payload⟩

theorem capture_unique (names : List Nat) (payload : Payload) (first last : Nat → Option Payload)
    (a : Captures names payload first) (b : Captures names payload last) : first = last :=
  (capture_complete names payload first a).trans (capture_complete names payload last b).symm

theorem both_same (names : List Nat) (payload : Payload) (first last : Nat)
    (a : first ∈ names) (b : last ∈ names) : assignment names payload first = assignment names payload last :=
  (captured_as_is names payload first a).trans (captured_as_is names payload last b).symm

theorem duplicate_unchanged (names : List Nat) (payload : Payload) (name : Nat) :
    assignment (name :: name :: names) payload = assignment (name :: names) payload := by
  funext current
  simp [assignment_exact]

/-- Defaults are observable only at names absent from the head. -/
def totalAssignment (names : List Nat) (payload fallback : Payload) (name : Nat) : Payload :=
  (assignment names payload name).getD fallback

theorem total_captured_as_is (names : List Nat) (payload fallback : Payload) (name : Nat) (mentioned : name ∈ names) :
    totalAssignment names payload fallback name = payload := by simp [totalAssignment, captured_as_is _ _ _ mentioned]

def variablePayload (first : Nat) : List Nat → Roles.Term
  | [] => .var first
  | next :: rest => CommonRoleMergedPayload.joinTerm (.var first) (variablePayload next rest)

def sourceRow (tag : Nat) (names : List Nat) : Variants.Merged.Row Nat Roles.Term :=
  Variants.Merged.normalize CommonRoleMergedPayload.joinTerm (names.map (fun name => (tag, Roles.Term.var name)))

theorem actual_merge (tag first : Nat) (rest : List Nat) :
    (sourceRow tag (first :: rest)).entries = [(tag, variablePayload first rest)] := by
  induction rest generalizing first with
  | nil => rfl
  | cons next rest ih =>
      change Variants.Merged.Raw.insert CommonRoleMergedPayload.joinTerm tag (.var first)
        (sourceRow tag (next :: rest)).entries = _
      rw [ih]
      simp [Variants.Merged.Raw.insert, variablePayload]

theorem interpret_payload (first : Nat) (rest : List Nat) (image : Nat → Common.Ty) (payload : Common.Ty)
    (assigned : ∀ name ∈ first :: rest, image name = payload) :
    CommonRoleMergedPayload.interpret (variablePayload first rest) image =
      some (CommonRoleMergedPayload.paddedType rest.length payload) := by
  induction rest generalizing first with
  | nil => simpa [variablePayload, CommonRoleMergedPayload.interpret, CommonRoleMergedPayload.paddedType] using assigned first (by simp)
  | cons next rest ih =>
      have current := assigned first (by simp)
      have remaining := ih next (fun name member => assigned name (List.mem_cons_of_mem _ member))
      simp [variablePayload, CommonRoleMergedPayload.joinTerm, CommonRoleMergedPayload.interpret,
        current, remaining, CommonRoleMergedPayload.paddedType]

theorem approved_head_meaning (tag first : Nat) (rest : List Nat) (payload fallback : Common.Ty) :
    CommonRoleMergedPayload.interpret (.app (tag + 3) [variablePayload first rest])
      (totalAssignment (first :: rest) payload fallback) =
        some (Common.variant tag (CommonRoleMergedPayload.paddedType rest.length payload)) ∧
    Common.Equivalent (Common.variant tag (CommonRoleMergedPayload.paddedType rest.length payload))
      (Common.variant tag payload) := by
  constructor
  · have interpreted := interpret_payload first rest (totalAssignment (first :: rest) payload fallback) payload
      (fun name member => total_captured_as_is _ _ _ _ member)
    simp [CommonRoleMergedPayload.interpret, interpreted]
  · exact (CommonCanonicalShapes.variant_equivalent_iff tag _ _).mpr (CommonRoleMergedPayload.padded_equivalent _ _)

theorem approved_two (payload : Payload) :
    assignment [0, 1] payload 0 = some payload ∧ assignment [0, 1] payload 1 = some payload :=
  ⟨captured_as_is _ _ _ (by decide), captured_as_is _ _ _ (by decide)⟩

theorem no_bottom_split : ¬ Common.Equivalent
    (totalAssignment [0, 1] (.base .int) (.bottom : Common.Ty) 0) .bottom := by
  rw [total_captured_as_is _ _ _ _ (by decide)]
  exact fun same => CommonRoleMergedCaptureBoundary.bottom_not_int (Common.equivalent_symm same)

end Yulang.CommonRoleSharedPayloadCapture
