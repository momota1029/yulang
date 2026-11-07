import Yulang.CommonRoleNominalCoverBoundary

/-! Agreement with the earlier independent Common head relation for the
approved two-declaration finite-tree family. Arbitrary Common assignments
occur only on the comparison side; the operational capture is the already
computed shared payload. This is not a full-language agreement theorem. -/
namespace Yulang.CommonRoleSharedPayloadAgreement

open CommonRoleLinearClock (Ground)
open CommonRoleCanonicalPayloadCandidates (merged concrete visible exampleGoal HeadCaptures)

def meaning (payload : Ground) : CommonRoleMergedSemantic.Goal := ⟨1, Common.variant 0 payload.eval⟩

theorem previous_merged_matches (payload : Ground) :
    ∃ image, CommonRoleMergedSemantic.Matches merged (meaning payload) image := by
  let image := CommonRoleSharedPayloadCapture.totalAssignment [0, 1] payload.eval (.bottom : Common.Ty)
  refine ⟨image, rfl, _, _, rfl, CommonRoleMergedCaptureBoundary.merged_head_interpreted image, ?_⟩
  have first : image 0 = payload.eval := CommonRoleSharedPayloadCapture.total_captured_as_is _ _ _ _ (by decide)
  have last : image 1 = payload.eval := CommonRoleSharedPayloadCapture.total_captured_as_is _ _ _ _ (by decide)
  change Common.Equivalent (Common.variant 0 (.union (image 0) (image 1))) (Common.variant 0 payload.eval)
  rw [first, last]
  exact (CommonCanonicalShapes.variant_equivalent_iff 0 _ _).mpr (CommonRoleMergedPayload.padded_equivalent 1 _)

theorem previous_concrete_exact (payload : Ground) :
    (∃ image, CommonRoleMergedSemantic.Matches concrete (meaning payload) image) ↔ payload = .int := by
  constructor
  · rintro ⟨image, role, term, type, head, read, same⟩
    have termEqual : term = (CommonRoleCaptureNormalization.Form.tick .int).normalize.encode :=
      (List.cons.inj head).1.symm
    subst term
    have typeEqual := Option.some.inj ((CommonRoleMergedCaptureBoundary.concrete_head_interpreted image).symm.trans read)
    subst type
    have payloadEqual := (CommonCanonicalShapes.variant_equivalent_iff 0 _ _).mp same
    exact ((CommonRoleLinearClock.Ground.equivalent_iff .int payload).mp payloadEqual).symm
  · rintro rfl
    let image : Nat → Common.Ty := fun _ => .base .int
    exact ⟨image, rfl, _, _, rfl, CommonRoleMergedCaptureBoundary.concrete_head_interpreted image,
      Common.equivalent_refl _⟩

theorem canonical_concrete_exact (payload : Ground) :
    (∃ image, HeadCaptures concrete (exampleGoal payload) image) ↔ payload = .int := by
  rw [← CommonRoleCanonicalPayloadCandidates.head_matches_exact]
  simp [CommonRoleCanonicalPayloadCandidates.headMatches,
    CommonRoleCanonicalPayloadCandidates.concrete_capture]

theorem finite_head_agreement (payload : Ground) (implementation : Roles.Impl)
    (member : implementation ∈ visible) :
    (∃ image, HeadCaptures implementation (exampleGoal payload) image) ↔
      ∃ image, CommonRoleMergedSemantic.Matches implementation (meaning payload) image := by
  rcases List.mem_cons.mp member with rfl | member
  · constructor
    · intro _; exact previous_merged_matches payload
    · intro _
      exact (CommonRoleCanonicalPayloadCandidates.head_matches_exact _ _).mp
        (by rw [CommonRoleCanonicalPayloadCandidates.headMatches,
          CommonRoleCanonicalPayloadCandidates.merged_capture]; rfl)
  · have equal : implementation = concrete := by simpa using member
    subst implementation
    exact (canonical_concrete_exact payload).trans (previous_concrete_exact payload).symm

def PreviousUnique (implementation : Roles.Impl) (payload : Ground) : Prop :=
  ∀ other ∈ visible, (∃ image, CommonRoleMergedSemantic.Matches other (meaning payload) image) → other = implementation

theorem previous_no_unique_at_int (implementation : Roles.Impl) : ¬ PreviousUnique implementation .int := by
  intro unique
  have first := unique merged (by simp [visible, CommonRoleMergedCaptureBoundary.visible]) (previous_merged_matches .int)
  have last := unique concrete (by simp [visible, CommonRoleMergedCaptureBoundary.visible])
    ((previous_concrete_exact .int).mpr rfl)
  exact CommonRoleMergedCaptureBoundary.distinct_declarations (first.trans last.symm)

theorem previous_unique_other (payload : Ground) (different : payload ≠ .int) : PreviousUnique merged payload := by
  intro other member matched
  have canonical := (finite_head_agreement payload other member).mpr matched
  have inCandidates := (CommonRoleCanonicalPayloadCandidates.mem_candidates visible (exampleGoal payload) other).mpr
    ⟨member, canonical⟩
  simpa only [CommonRoleCanonicalPayloadCandidates.actual_candidate_list, different, ↓reduceIte, List.mem_singleton] using inCandidates

theorem previous_selected_plan (payload : Ground) :
    (∃ image, CommonRoleMergedSemantic.Matches merged (meaning payload) image) ∧
      PreviousUnique merged payload ↔ payload ≠ .int := by
  constructor
  · rintro ⟨_, unique⟩ equal
    subst payload
    exact previous_no_unique_at_int merged unique
  · intro different
    exact ⟨previous_merged_matches payload, previous_unique_other payload different⟩

theorem actual_plan_agrees_previous (payload : Ground) :
    (∃ plan, CommonRoleCanonicalPayloadCandidates.selectedPlan visible (exampleGoal payload) = some plan) ↔
      (∃ image, CommonRoleMergedSemantic.Matches merged (meaning payload) image) ∧ PreviousUnique merged payload := by
  rw [CommonRoleCanonicalPayloadCandidates.example_plan_exact,
    CommonRoleCanonicalPayloadCandidates.example_dictionary_exact, previous_selected_plan]

end Yulang.CommonRoleSharedPayloadAgreement
