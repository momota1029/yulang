import Yulang.CommonRoleFiniteShadowSemantic
import Yulang.CommonRoleSemanticPadding

/-! Declaration normalization in the fixed int/pair/variant/one-field record
countergrammar. Explicit hidden fields are removed recursively, including
inside payloads. Unknown tails remain variables. Preservation quantifies
arbitrary Common substitutions. This is an E2 boundary, not a full-language
normalizer or a source-elaboration theorem. -/

namespace Yulang.CommonRoleNormalizedDeclarations

open CommonRoleInspectedSemantics

def TailEq (first last : Common.Ty) : Prop :=
  Common.RecordTailLe [0] first last ∧ Common.RecordTailLe [0] last first

theorem tail_of_equivalent {first last : Common.Ty} (same : Common.Equivalent first last) : TailEq first last := by
  constructor
  · exact (Common.common_record_iff 0 (.base .int) (.base .int) first last).mp
      (Common.common_record_mono 0 (Common.subtype_refl _) same.1) |>.2
  · exact (Common.common_record_iff 0 (.base .int) (.base .int) last first).mp
      (Common.common_record_mono 0 (Common.subtype_refl _) same.2) |>.2

theorem tail_trans {first middle last : Common.Ty} (before : TailEq first middle) (after : TailEq middle last) :
    TailEq first last :=
  ⟨fun depth => CommonFinite.recordTailLe_trans [0] (before.1 depth) (after.1 depth),
    fun depth => CommonFinite.recordTailLe_trans [0] (after.2 depth) (before.2 depth)⟩

theorem hidden_tail (payload rest : Common.Ty) : TailEq rest (Common.record 0 payload rest) := by
  have same := Common.common_shadowed_head_equivalent 0 (.base .int) payload rest
  exact ⟨(Common.common_record_iff 0 _ _ _ _).mp same.2 |>.2,
    (Common.common_record_iff 0 _ _ _ _).mp same.1 |>.2⟩

theorem record_congr {a b first last : Common.Ty} (payload : Common.Equivalent a b) (tail : TailEq first last) :
    Common.Equivalent (Common.record 0 a first) (Common.record 0 b last) :=
  ⟨(Common.common_record_iff 0 _ _ _ _).mpr ⟨payload.1, tail.1⟩,
    (Common.common_record_iff 0 _ _ _ _).mpr ⟨payload.2, tail.2⟩⟩

theorem normalize_meaning (pattern : Pattern) (assignment : Nat → Common.Ty) :
    Common.Equivalent ((pattern.visible false).eval assignment) (pattern.eval assignment) ∧
      TailEq ((pattern.visible true).eval assignment) (pattern.eval assignment) := by
  induction pattern with
  | var name | int | empty => exact ⟨Common.equivalent_refl _, tail_of_equivalent (Common.equivalent_refl _)⟩
  | pair first last ihFirst ihLast =>
      have same := (CommonCanonicalShapes.pair_equivalent_iff _ _ _ _).mpr ⟨ihFirst.1, ihLast.1⟩
      exact ⟨same, tail_of_equivalent same⟩
  | variant tag payload ih =>
      have same := (CommonCanonicalShapes.variant_equivalent_iff tag _ _).mpr ih.1
      exact ⟨same, tail_of_equivalent same⟩
  | record payload rest ihPayload ihRest =>
      exact ⟨record_congr ihPayload.1 ihRest.2,
        tail_trans ihRest.2 (hidden_tail (payload.eval assignment) (rest.eval assignment))⟩

def normalizeTerm (term : Roles.Term) : Roles.Term :=
  ((decodePattern term).map (fun pattern => (pattern.visible false).encode)).getD term

@[simp] theorem normalizeTerm_encode (pattern : Pattern) :
    normalizeTerm pattern.encode = (pattern.visible false).encode := by simp [normalizeTerm]

theorem normalizeTerm_meaning (term : Roles.Term) (assignment : Nat → Common.Ty)
    (valid : (decodePattern term).isSome = true) :
    ∃ first last, interpretTerm (normalizeTerm term) assignment = some first ∧
      interpretTerm term assignment = some last ∧ Common.Equivalent first last := by
  cases decoded : decodePattern term with
  | none => simp [decoded] at valid
  | some pattern =>
      refine ⟨_, _, ?_, ?_, (normalize_meaning pattern assignment).1⟩
      · simp [normalizeTerm, decoded]
      · simp [interpretTerm, decoded]

theorem normalized_head_match_exact (term : Roles.Term) (assignment : Nat → Common.Ty)
    (valid : (decodePattern term).isSome = true) (goal : Common.Ty) :
    (∃ type, interpretTerm (normalizeTerm term) assignment = some type ∧ Common.Equivalent type goal) ↔
      ∃ type, interpretTerm term assignment = some type ∧ Common.Equivalent type goal := by
  obtain ⟨first, last, firstRead, lastRead, same⟩ := normalizeTerm_meaning term assignment valid
  constructor
  · rintro ⟨type, read, matched⟩
    have equal := Option.some.inj (firstRead.symm.trans read)
    subst type
    exact ⟨last, lastRead, Common.equivalent_trans (Common.equivalent_symm same) matched⟩
  · rintro ⟨type, read, matched⟩
    have equal := Option.some.inj (lastRead.symm.trans read)
    subst type
    exact ⟨first, firstRead, Common.equivalent_trans same matched⟩

def normalizeGoal (goal : Roles.Goal) : Roles.Goal := ⟨goal.role, goal.args.map normalizeTerm⟩

def normalizeImpl (implementation : Roles.Impl) : Roles.Impl :=
  ⟨implementation.role, implementation.head.map normalizeTerm, implementation.constraints.map normalizeGoal,
    implementation.key⟩

def checkPatterns (terms : List Roles.Term) : Bool := terms.all (fun term => (decodePattern term).isSome)

def checkImpl (implementation : Roles.Impl) : Bool :=
  checkPatterns implementation.head && implementation.constraints.all (fun child => checkPatterns child.args) &&
    CheckedRoles.checkImpl (normalizeImpl implementation)

def NormalizedWellFormed (visible : List Roles.Impl) : Prop := Roles.WellFormed (visible.map normalizeImpl)

def checkEnvironment (environment : Roles.AssocEnv) : Bool :=
  environment.impls.all (fun implementation => checkImpl implementation.impl &&
    implementation.assoc.all (fun body => decide (body.2 = Pattern.int.encode)))

theorem checkImpl_sound (implementation : Roles.Impl) (accepted : checkImpl implementation = true) :
    (normalizeImpl implementation).WellFormed :=
  (CheckedRoles.checkImpl_exact _).mp (Bool.and_eq_true_iff.mp accepted).2

theorem checkEnvironment_sound (environment : Roles.AssocEnv) (accepted : checkEnvironment environment = true) :
    NormalizedWellFormed environment.cores ∧ CommonRoleFiniteShadowRegistry.HeadDeterminesAssociated environment := by
  have each := List.all_eq_true.mp accepted
  constructor
  · intro implementation member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    obtain ⟨annotated, annotatedMember, rfl⟩ := List.mem_map.mp present
    exact checkImpl_sound _ (Bool.and_eq_true_iff.mp (each annotated annotatedMember)).1
  · intro implementation member σ τ _ name rhs body
    have bodies := (Bool.and_eq_true_iff.mp (each implementation member)).2
    have same : rhs = Pattern.int.encode := of_decide_eq_true ((List.all_eq_true.mp bodies) (name, rhs) body)
    subst rhs
    exact ⟨.base .int, .base .int, rfl, rfl, Common.equivalent_refl _⟩

/-- Duplicate-field removal is not a complete normalization of Common
equivalence: union idempotence has no record fields at all. This is a kernel
fact, not permission to write general union annotations in source. -/
theorem another_size_erasure :
    Common.Equivalent (.union (.base .int) (.base .int)) (.base .int) ∧
      (.app 2 [.app 0 [], .app 0 []] : Roles.Term).size > (.app 0 [] : Roles.Term).size := by
  constructor
  · exact ⟨(Common.common_union_is_join _ _ _).mpr ⟨Common.subtype_refl _, Common.subtype_refl _⟩,
      CommonBoundCoalescing.le_union_left _ _⟩
  · decide +kernel

end Yulang.CommonRoleNormalizedDeclarations
