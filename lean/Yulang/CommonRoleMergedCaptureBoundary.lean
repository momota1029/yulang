import Yulang.CommonRoleStablePaterson

/-! A specification boundary, not an E2. Both terminal declarations satisfy
the stable checker. The fixed completions below establish mathematical head
equalities only; none is silently declared to be the real resolver's capture.
The independent completion/pending policy is the accompanying single question. -/
namespace Yulang.CommonRoleMergedCaptureBoundary

open CommonRoleCaptureNormalization (Form)
open CommonRoleStablePaterson (Declaration check)
open CommonRoleMergedPayload (interpret)

def merged : Declaration := ⟨1, 0, [.tick (.join (.var 0) (.var 1))], []⟩
def concrete : Declaration := ⟨1, 1, [.tick .int], []⟩
def visible : List Roles.Impl := [merged.toImpl, concrete.toImpl]

theorem stable_checked : check merged = true ∧ check concrete = true := ⟨rfl, rfl⟩

theorem wellFormed : Roles.WellFormed visible := by
  intro implementation member
  rcases List.mem_cons.mp member with rfl | member
  · exact CommonRoleStablePaterson.accepted_wellFormed merged rfl
  · have equal : implementation = concrete.toImpl := by simpa using member
    subst implementation
    exact CommonRoleStablePaterson.accepted_wellFormed concrete rfl

def environment : Roles.AssocEnv where
  impls := visible.map CommonRoleMergedRegistry.annotate
  coherent := by
    intro first firstMember last lastMember _
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp firstMember
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp lastMember
    rfl

theorem environment_cores : environment.cores = visible := by
  simp [environment, Roles.AssocEnv.cores, List.map_map, Function.comp_def, CommonRoleMergedRegistry.annotate]

theorem associated_determined : CommonRoleMergedRegistry.HeadDeterminesAssociated environment := by
  intro implementation member σ τ _ name rhs body
  obtain ⟨core, _, rfl⟩ := List.mem_map.mp member
  have equal : (name, rhs) = (0, CommonRoleMergedPayload.dataTerm .int) := by
    simpa [CommonRoleMergedRegistry.annotate] using body
  cases equal
  exact ⟨.base .int, .base .int, rfl, rfl, Common.equivalent_refl _⟩

theorem merged_head_interpreted (assignment : Nat → Common.Ty) :
    interpret ((Form.tick (.join (.var 0) (.var 1))).normalize.encode) assignment =
      some (Common.variant 0 (.union (assignment 0) (assignment 1))) := rfl

theorem concrete_head_interpreted (assignment : Nat → Common.Ty) :
    interpret ((Form.tick .int).normalize.encode) assignment = some (Common.variant 0 (.base .int)) := rfl

def fullPayload : Nat → Common.Ty := fun _ => .base .int
def separatedPayload (name : Nat) : Common.Ty := if name = 0 then .bottom else .base .int

theorem full_payload_head : Common.Equivalent
    (Common.variant 0 (.union (fullPayload 0) (fullPayload 1))) (Common.variant 0 (.base .int)) :=
  (CommonCanonicalShapes.variant_equivalent_iff 0 _ _).mpr (CommonRoleMergedPayload.padded_equivalent 1 _)

theorem separated_payload_head : Common.Equivalent
    (Common.variant 0 (.union (separatedPayload 0) (separatedPayload 1))) (Common.variant 0 (.base .int)) := by
  apply (CommonCanonicalShapes.variant_equivalent_iff 0 _ _).mpr
  constructor
  · exact (Common.common_union_is_join _ _ _).mpr
      ⟨CommonBoundCoalescing.bottom_le _, Common.subtype_refl _⟩
  · exact CommonBoundCoalescing.le_union_right _ _

theorem bottom_not_int : ¬ Common.Equivalent (.bottom : Common.Ty) (.base .int) := by
  intro same
  have impossible := same.2 0
  have observed := (CommonFinite.producerLe_iff_probe _ _).mp impossible 0
    ⟨fun _ => .bottom, fun _ => []⟩ (.role 0) (by trivial)
  simp [Common.observeTy, CommonFinite.ProbeAt, CommonFinite.ProbeStep, CommonFinite.MaskedProbeStep,
    CommonSyntax.Layer.evalAt] at observed

theorem completions_differ : ¬ Common.Equivalent (fullPayload 0) (separatedPayload 0) := by
  intro same
  exact bottom_not_int (Common.equivalent_symm same)

theorem distinct_declarations : merged.toImpl ≠ concrete.toImpl := by decide +kernel

end Yulang.CommonRoleMergedCaptureBoundary
