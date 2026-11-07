import Yulang.CommonRoleSharedPayloadAgreement

/-! Glue between the stable checker and the approved computed capture for
plain-variable merge heads. This is finite Form/idempotence-stage descent,
not the missing all-grammar regular matcher theorem. -/
namespace Yulang.CommonRoleSharedCaptureDescent

open CommonRoleCaptureNormalization (Form)
open CommonRoleStablePaterson (Declaration)

def variableForm (first : Nat) : List Nat → Form
  | [] => .var first
  | next :: rest => .join (.var first) (variableForm next rest)

theorem encode_variables (first : Nat) (rest : List Nat) :
    (variableForm first rest).encode = CommonRoleSharedPayloadCapture.variablePayload first rest := by
  induction rest generalizing first with
  | nil => rfl
  | cons next rest ih => simp [variableForm, CommonRoleSharedPayloadCapture.variablePayload,
      Form.encode, CommonRoleMergedPayload.joinTerm, ih]

theorem normalized_variables (first : Nat) (rest : List Nat) (image : Nat → Form) (payload : Form)
    (assigned : ∀ name ∈ first :: rest, image name = payload) :
    ((variableForm first rest).subst image).normalize = payload.normalize := by
  induction rest generalizing first with
  | nil => simpa [variableForm, Form.subst] using congrArg Form.normalize (assigned first (by simp))
  | cons next rest ih =>
      have current := assigned first (by simp)
      have remaining := ih next (fun name member => assigned name (List.mem_cons_of_mem _ member))
      simp [variableForm, Form.subst, Form.normalize, current, remaining]

def declaration (role key first : Nat) (rest : List Nat) (requirements : List (Nat × List Form)) : Declaration :=
  ⟨role, key, [.tick (variableForm first rest)], requirements⟩

theorem actual_head_is_goal (first : Nat) (rest : List Nat) (payload fallback : Form) :
    CommonRoleStablePaterson.instantiated [.tick (variableForm first rest)]
      (CommonRoleSharedPayloadCapture.totalAssignment (first :: rest) payload fallback) =
        CommonRoleStablePaterson.childBound [.tick payload] := by
  have normalized := normalized_variables first rest
    (CommonRoleSharedPayloadCapture.totalAssignment (first :: rest) payload fallback) payload
    (fun name member => CommonRoleSharedPayloadCapture.total_captured_as_is _ _ _ _ member)
  simpa only [CommonRoleStablePaterson.instantiated, CommonRoleStablePaterson.childBound,
    List.map_cons, List.map_nil, Form.subst, Form.normalize, Form.encode] using
      congrArg (fun form => [(Form.tick form).encode]) normalized

theorem canonical_capture_strictly_decreases (role key first : Nat) (rest : List Nat)
    (requirements : List (Nat × List Form))
    (accepted : CommonRoleStablePaterson.check (declaration role key first rest requirements) = true)
    (child : Nat × List Form) (required : child ∈ requirements) (payload fallback : Form) :
    Roles.argsSize (CommonRoleStablePaterson.instantiated child.2
      (CommonRoleSharedPayloadCapture.totalAssignment (first :: rest) payload fallback)) <
        Roles.argsSize (CommonRoleStablePaterson.childBound [.tick payload]) ∧
      ∀ name, Roles.argsOccurrences name (CommonRoleStablePaterson.instantiated child.2
        (CommonRoleSharedPayloadCapture.totalAssignment (first :: rest) payload fallback)) ≤
          Roles.argsOccurrences name (CommonRoleStablePaterson.childBound [.tick payload]) := by
  have stable := CommonRoleStablePaterson.check_sound (declaration role key first rest requirements)
    accepted child required (CommonRoleSharedPayloadCapture.totalAssignment (first :: rest) payload fallback)
  change _ ∧ ∀ name, _ at stable
  change Roles.argsSize _ < Roles.argsSize (CommonRoleStablePaterson.instantiated [.tick (variableForm first rest)] _) ∧
    ∀ name, Roles.argsOccurrences name _ ≤ Roles.argsOccurrences name
      (CommonRoleStablePaterson.instantiated [.tick (variableForm first rest)] _) at stable
  rw [actual_head_is_goal] at stable
  exact stable

end Yulang.CommonRoleSharedCaptureDescent
