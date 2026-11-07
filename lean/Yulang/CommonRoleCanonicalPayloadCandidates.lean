import Yulang.CommonRoleSharedPayloadCapture

/-! The approved variable-merge/int-head component reads actual stored
Roles.Impl fields. It is not a full head matcher: non-variable compound
payloads remain the separate policy question. This module verifies the
approved ambiguity example and its canonical captures without choosing an
arbitrary Common preimage. All goals in this component are finite Ground. -/
namespace Yulang.CommonRoleCanonicalPayloadCandidates

open CommonRoleLinearClock (Ground)
open CommonRoleCanonicalRows (Row lookup)
open CommonRoleSharedPayloadCapture (bindings Captures)

structure Goal where
  role : Nat
  tag : Nat
  payload : Ground
  deriving DecidableEq, Repr

def Goal.description (goal : Goal) : CommonRoleInspectedSemantics.Goal :=
  ⟨goal.role, .variant goal.tag (.ground goal.payload)⟩

theorem finite_ready (visible : List Roles.Impl) (goal : Goal) :
    CommonRoleInspectedSemantics.Ready visible goal.description :=
  CommonRoleInspectedSemantics.finite_ready _ _ rfl

def variableNames : Roles.Term → Option (List Nat)
  | .var name => some [name]
  | .app 4 [first, last] => do return (← variableNames first) ++ (← variableNames last)
  | _ => none

def headView : List Roles.Term → Option (Nat × Roles.Term)
  | [.app (tag + 3) [payload]] => some (tag, payload)
  | _ => none

def capturePayload (term : Roles.Term) (payload : Ground) : Option (Row Ground) :=
  if term = .app 0 [] then
    if payload = .int then some [] else none
  else (variableNames term).map (fun names => bindings names payload)

def PayloadCaptures (term : Roles.Term) (payload : Ground) (image : Nat → Option Ground) : Prop :=
  (term = .app 0 [] ∧ payload = .int ∧ image = fun _ => none) ∨
    ∃ names, variableNames term = some names ∧ Captures names payload image

theorem payload_capture_exact (term : Roles.Term) (payload : Ground) (image : Nat → Option Ground) :
    (∃ entries, capturePayload term payload = some entries ∧ image = fun name => lookup name entries) ↔
      PayloadCaptures term payload image := by
  by_cases literal : term = .app 0 []
  · subst term
    by_cases integer : payload = .int <;>
      simp [capturePayload, PayloadCaptures, variableNames, integer, lookup]
  · cases decoded : variableNames term with
    | none => simp [capturePayload, PayloadCaptures, literal, decoded]
    | some names =>
        have read : capturePayload term payload = some (bindings names payload) := by
          simp [capturePayload, literal, decoded]
        constructor
        · rintro ⟨entries, found, sameImage⟩
          have equal := Option.some.inj (read.symm.trans found)
          subst entries
          apply Or.inr
          refine ⟨names, decoded, ?_⟩
          rw [sameImage]
          exact CommonRoleSharedPayloadCapture.capture_sound names payload
        · intro specified
          rcases specified with ⟨impossible, _⟩ | ⟨other, otherRead, captures⟩
          · exact False.elim (literal impossible)
          · have equal := Option.some.inj (decoded.symm.trans otherRead)
            subst other
            exact ⟨bindings names payload, read,
              CommonRoleSharedPayloadCapture.capture_complete names payload image captures⟩

def tryCapture (implementation : Roles.Impl) (goal : Goal) : Option (Row Ground) :=
  if implementation.role = goal.role then do
    let (tag, term) ← headView implementation.head
    if tag = goal.tag then capturePayload term goal.payload else none
  else none

def HeadCaptures (implementation : Roles.Impl) (goal : Goal) (image : Nat → Option Ground) : Prop :=
  implementation.role = goal.role ∧ ∃ tag term,
    headView implementation.head = some (tag, term) ∧ tag = goal.tag ∧ PayloadCaptures term goal.payload image

theorem head_capture_exact (implementation : Roles.Impl) (goal : Goal) (image : Nat → Option Ground) :
    (∃ entries, tryCapture implementation goal = some entries ∧ image = fun name => lookup name entries) ↔
      HeadCaptures implementation goal image := by
  by_cases role : implementation.role = goal.role
  · cases viewed : headView implementation.head with
    | none => simp [tryCapture, HeadCaptures, role, viewed]
    | some pair =>
        rcases pair with ⟨tag, term⟩
        by_cases same : tag = goal.tag
        · simpa [tryCapture, HeadCaptures, role, viewed, same, and_assoc] using
            payload_capture_exact term goal.payload image
        · simp [tryCapture, HeadCaptures, role, viewed, same]
  · simp [tryCapture, HeadCaptures, role]

def headMatches (implementation : Roles.Impl) (goal : Goal) : Bool := (tryCapture implementation goal).isSome

theorem head_matches_exact (implementation : Roles.Impl) (goal : Goal) :
    headMatches implementation goal = true ↔ ∃ image, HeadCaptures implementation goal image := by
  constructor
  · intro matched
    obtain ⟨entries, read⟩ := Option.isSome_iff_exists.mp matched
    exact ⟨_, (head_capture_exact _ _ _).mp ⟨entries, read, rfl⟩⟩
  · rintro ⟨image, matched⟩
    obtain ⟨entries, read, _⟩ := (head_capture_exact _ _ _).mpr matched
    exact Option.isSome_iff_exists.mpr ⟨entries, read⟩

def candidates (visible : List Roles.Impl) (goal : Goal) : List Roles.Impl :=
  (Roles.distinct visible).filter (fun implementation => headMatches implementation goal)

theorem mem_candidates (visible : List Roles.Impl) (goal : Goal) (implementation : Roles.Impl) :
    implementation ∈ candidates visible goal ↔ implementation ∈ visible ∧ ∃ image, HeadCaptures implementation goal image := by
  simp [candidates, head_matches_exact]

inductive HeadOutcome where
  | unsupported
  | absent
  | selected : Roles.Impl → HeadOutcome
  | ambiguous
  deriving DecidableEq, Repr

def supportedHead (implementation : Roles.Impl) : Bool :=
  match headView implementation.head with
  | none => false
  | some (_, term) => decide (term = .app 0 []) || (variableNames term).isSome

def classifyHeads (visible : List Roles.Impl) (goal : Goal) : HeadOutcome :=
  if visible.all supportedHead then
    match candidates visible goal with
    | [] => .absent
    | [implementation] => .selected implementation
    | _ :: _ :: _ => .ambiguous
  else .unsupported

theorem unsupported_explicit (visible : List Roles.Impl) (goal : Goal)
    (outside : visible.all supportedHead = false) : classifyHeads visible goal = .unsupported := by
  simp [classifyHeads, outside]

abbrev merged := CommonRoleMergedCaptureBoundary.merged.toImpl
abbrev concrete := CommonRoleMergedCaptureBoundary.concrete.toImpl
abbrev visible := CommonRoleMergedCaptureBoundary.visible

def exampleGoal (payload : Ground) : Goal := ⟨1, 0, payload⟩

theorem example_supported : visible.all supportedHead = true := by decide +kernel

theorem merged_capture (payload : Ground) : tryCapture merged (exampleGoal payload) = some (bindings [0, 1] payload) := rfl

theorem concrete_capture (payload : Ground) :
    tryCapture concrete (exampleGoal payload) = if payload = .int then some [] else none := rfl

theorem actual_candidate_list (payload : Ground) :
    candidates visible (exampleGoal payload) = if payload = .int then [merged, concrete] else [merged] := by
  have different := CommonRoleMergedCaptureBoundary.distinct_declarations
  simp only [candidates, CommonRoleMergedCaptureBoundary.visible, Roles.distinct]
  simp only [List.mem_singleton, different, ↓reduceIte, List.not_mem_nil]
  simp only [List.filter_cons, List.filter_nil, headMatches, merged_capture, concrete_capture, Option.isSome_some, ↓reduceIte]
  by_cases integer : payload = .int <;> simp [integer]

theorem approved_ambiguous : classifyHeads visible (exampleGoal .int) = .ambiguous := by
  simp [classifyHeads, example_supported, actual_candidate_list]

theorem other_payload_selected (payload : Ground) (different : payload ≠ .int) :
    classifyHeads visible (exampleGoal payload) = .selected merged := by
  simp [classifyHeads, example_supported, actual_candidate_list, different]

theorem actual_two_images (payload : Ground) :
    lookup 0 (bindings [0, 1] payload) = some payload ∧ lookup 1 (bindings [0, 1] payload) = some payload :=
  CommonRoleSharedPayloadCapture.approved_two payload

theorem approved_independent_overlap :
    merged ≠ concrete ∧ merged ∈ visible ∧ concrete ∈ visible ∧
      (∃ image, HeadCaptures merged (exampleGoal .int) image) ∧
      (∃ image, HeadCaptures concrete (exampleGoal .int) image) := by
  refine ⟨CommonRoleMergedCaptureBoundary.distinct_declarations, by simp [visible, CommonRoleMergedCaptureBoundary.visible],
    by simp [visible, CommonRoleMergedCaptureBoundary.visible], ?_, ?_⟩
  · exact (head_matches_exact _ _).mp (by rw [headMatches, merged_capture]; rfl)
  · exact (head_matches_exact _ _).mp (by rw [headMatches, concrete_capture]; rfl)

/-- Terminal evidence only, with every actual where field required empty.
This is a component judgment, not a replacement for nested dictionaries. -/
structure TerminalEvidence (visible : List Roles.Impl) (goal : Goal) where
  implementation : Roles.Impl
  image : Nat → Option Ground
  member : implementation ∈ visible
  captured : HeadCaptures implementation goal image
  unique : ∀ other ∈ visible, (∃ image, HeadCaptures other goal image) → other = implementation
  terminal : implementation.constraints = []

def TerminalEvidence.erase {visible : List Roles.Impl} {goal : Goal}
    (evidence : TerminalEvidence visible goal) : RoleDictionaries.Plan := .node evidence.implementation []

theorem TerminalEvidence.all_visible {visible : List Roles.Impl} {goal : Goal}
    (evidence : TerminalEvidence visible goal) (implementation : Roles.Impl)
    (member : implementation ∈ evidence.erase.declarations) : implementation ∈ visible := by
  have equal : implementation = evidence.implementation := by simpa [TerminalEvidence.erase, RoleDictionaries.Plan.declarations] using member
  exact equal ▸ evidence.member

theorem approved_no_dictionary : ¬ Nonempty (TerminalEvidence visible (exampleGoal .int)) := by
  rintro ⟨evidence⟩
  obtain ⟨different, firstMember, lastMember, firstCapture, lastCapture⟩ := approved_independent_overlap
  exact different ((evidence.unique merged firstMember firstCapture).trans
    (evidence.unique concrete lastMember lastCapture).symm)

theorem other_payload_dictionary (payload : Ground) (different : payload ≠ .int) :
    Nonempty (TerminalEvidence visible (exampleGoal payload)) := by
  refine ⟨⟨merged, CommonRoleSharedPayloadCapture.assignment [0, 1] payload,
    by simp [visible, CommonRoleMergedCaptureBoundary.visible], ?_, ?_, rfl⟩⟩
  · exact (head_capture_exact _ _ _).mp ⟨bindings [0, 1] payload, merged_capture payload, rfl⟩
  · intro other member matched
    have candidate := (mem_candidates visible (exampleGoal payload) other).mpr ⟨member, matched⟩
    simpa only [actual_candidate_list, different, ↓reduceIte, List.mem_singleton] using candidate

theorem example_dictionary_exact (payload : Ground) :
    Nonempty (TerminalEvidence visible (exampleGoal payload)) ↔ payload ≠ .int := by
  constructor
  · intro evidence equal
    subst payload
    exact approved_no_dictionary evidence
  · exact other_payload_dictionary payload

def selectedPlan (visible : List Roles.Impl) (goal : Goal) : Option RoleDictionaries.Plan :=
  match classifyHeads visible goal with
  | .selected implementation => if implementation.constraints.isEmpty then some (.node implementation []) else none
  | _ => none

theorem approved_no_plan : selectedPlan visible (exampleGoal .int) = none := by
  rw [selectedPlan, approved_ambiguous]

theorem other_payload_plan (payload : Ground) (different : payload ≠ .int) :
    selectedPlan visible (exampleGoal payload) = some (.node merged []) := by
  rw [selectedPlan, other_payload_selected payload different]
  rfl

theorem example_plan_exact (payload : Ground) :
    (∃ plan, selectedPlan visible (exampleGoal payload) = some plan) ↔
      Nonempty (TerminalEvidence visible (exampleGoal payload)) := by
  rw [example_dictionary_exact]
  constructor
  · rintro ⟨plan, produced⟩ equal
    subst payload
    rw [approved_no_plan] at produced
    cases produced
  · intro different
    exact ⟨.node merged [], other_payload_plan payload different⟩

end Yulang.CommonRoleCanonicalPayloadCandidates
