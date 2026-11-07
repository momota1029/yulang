import Yulang.CommonLegacy
import Yulang.CommonBoundCoalescing

/-!
# Finite legacy-bound interpolation for arbitrary common witnesses

A finite family of old regular upper bounds admits a monotone interpolation
of every common type back into the old contextual carrier. The interpolation
preserves all old lower bounds and exactly preserves comparison to each
listed upper bound. One simultaneous interpolation therefore preserves every
shared flow edge of a finite bound problem, as well as an old result bound.

The finite tests may contain arbitrary old regular graphs and arbitrary rows.
The original witnesses may contain exact/default/masked common types. No
syntactic restriction is placed on those witnesses.

This is an existential reflection result for fixed legacy bounds. It does
not assert that interpolation commutes with constructor equations whose
children are still unknown. That extra step is needed for the full supported
source reflection theorem of decision 46. The semantic filter below is a
proof witness, not an executable inference or normalization algorithm.
-/

namespace Yulang.CommonLegacyReflection

open Common (Subtype Equivalent embedOld)
open LayerBoundTemplates (Constraint Problem)

abbrev OldTy := RegularInferenceModel.Ty Common.Row

abbrev OldLe (first last : OldTy) :=
  ProducerContextualRegular.ProducerLe (RegularInferenceModel.graph Common.Row)
    Common.rowLe first last

def meet : List OldTy → OldTy
  | [] => .top
  | first :: rest => .inter first (meet rest)

theorem embed_meet (types : List OldTy) :
    embedOld (meet types) = CommonBoundCoalescing.meetTypes (types.map embedOld) := by
  induction types with
  | nil => rfl
  | cons first rest ih =>
      change CommonSyntax.Layer.inter (embedOld first) (embedOld (meet rest)) =
        CommonSyntax.Layer.inter (embedOld first)
          (CommonBoundCoalescing.meetTypes (rest.map embedOld))
      rw [ih]

theorem below_embedded_meet_iff (source : Common.Ty) (types : List OldTy) :
    Subtype source (embedOld (meet types)) ↔
      ∀ type ∈ types, Subtype source (embedOld type) := by
  rw [embed_meet, CommonBoundCoalescing.le_meetTypes_iff]
  simp only [List.forall_mem_map]

theorem old_below_meet_iff (source : OldTy) (types : List OldTy) :
    OldLe source (meet types) ↔ ∀ type ∈ types, OldLe source type := by
  constructor
  · intro below type member
    exact (Common.contextual_embedding_exact _ _).mp
      ((below_embedded_meet_iff _ _).mp
        ((Common.contextual_embedding_exact _ _).mpr below) type member)
  · intro below
    exact (Common.contextual_embedding_exact _ _).mp
      ((below_embedded_meet_iff _ _).mpr fun type member =>
        (Common.contextual_embedding_exact _ _).mpr (below type member))

theorem meet_below_member (types : List OldTy) (type : OldTy) (member : type ∈ types) :
    OldLe (meet types) type :=
  (old_below_meet_iff (meet types) types).mp
    (ProducerContextualRegular.producerLe_refl _) type member

/-- A single finite family is shared by every interpolated unknown. -/
noncomputable def envelope (tests : List OldTy) (source : Common.Ty) : OldTy := by
  classical
  exact meet (tests.filter fun type => decide (Subtype source (embedOld type)))

theorem below_envelope (tests : List OldTy) (source : Common.Ty) :
    Subtype source (embedOld (envelope tests source)) := by
  classical
  apply (below_embedded_meet_iff source _).mpr
  intro type member
  exact of_decide_eq_true (List.mem_filter.mp member).2

/-- Every listed old upper test has exactly its original truth value. -/
theorem envelope_upper_exact (tests : List OldTy) (source : Common.Ty)
    (target : OldTy) (member : target ∈ tests) :
    OldLe (envelope tests source) target ↔ Subtype source (embedOld target) := by
  classical
  constructor
  · intro below
    exact Common.subtype_trans (below_envelope tests source)
      ((Common.contextual_embedding_exact _ _).mpr below)
  · intro below
    exact meet_below_member _ target (List.mem_filter.mpr ⟨member, by simpa using below⟩)

/-- Lower bounds need not belong to the finite test family. -/
theorem envelope_preserves_lower (tests : List OldTy) (source : Common.Ty)
    (lower : OldTy) (below : Subtype (embedOld lower) source) :
    OldLe lower (envelope tests source) :=
  (Common.contextual_embedding_exact _ _).mp
    (Common.subtype_trans below (below_envelope tests source))

/-- Applying the same envelope to all unknowns preserves every shared flow. -/
theorem envelope_mono (tests : List OldTy) (source target : Common.Ty)
    (below : Subtype source target) :
    OldLe (envelope tests source) (envelope tests target) := by
  classical
  apply (old_below_meet_iff _ _).mpr
  intro type member
  obtain ⟨available, accepted⟩ := List.mem_filter.mp member
  exact (envelope_upper_exact tests source type available).mpr
    (Common.subtype_trans below (of_decide_eq_true accepted))

theorem envelope_fixes_boundary (tests : List OldTy) (type : OldTy) (member : type ∈ tests) :
    ProducerContextualRegular.ProducerEq (RegularInferenceModel.graph Common.Row)
      Common.rowLe (envelope tests (embedOld type)) type :=
  ⟨(envelope_upper_exact tests (embedOld type) type member).mpr (Common.subtype_refl _),
    envelope_preserves_lower tests (embedOld type) type (Common.subtype_refl _)⟩

/-- Every finite legacy interval inhabited by a common type already has an
old regular inhabitant. Both directions quantify over all original bounds. -/
theorem finite_interval_exact (lowers uppers : List OldTy) :
    (∃ source : Common.Ty,
      (∀ lower ∈ lowers, Subtype (embedOld lower) source) ∧
      ∀ upper ∈ uppers, Subtype source (embedOld upper)) ↔
    ∃ source : OldTy,
      (∀ lower ∈ lowers, OldLe lower source) ∧
      ∀ upper ∈ uppers, OldLe source upper := by
  constructor
  · rintro ⟨source, lowerBounds, upperBounds⟩
    exact ⟨envelope uppers source,
      fun lower member => envelope_preserves_lower uppers source lower (lowerBounds lower member),
      fun upper member => (envelope_upper_exact uppers source upper member).mpr
        (upperBounds upper member)⟩
  · rintro ⟨source, lowerBounds, upperBounds⟩
    exact ⟨embedOld source,
      fun lower member => (Common.contextual_embedding_exact _ _).mpr (lowerBounds lower member),
      fun upper member => (Common.contextual_embedding_exact _ _).mpr (upperBounds upper member)⟩

universe u
variable {n : Nat} {Bound : Type u}

def upperTests (evaluate : Bound → OldTy) (problem : Problem n Bound) : List OldTy :=
  problem.filterMap fun
    | .upper _ bound => some (evaluate bound)
    | _ => none

theorem upper_mem_tests (evaluate : Bound → OldTy) (problem : Problem n Bound)
    (source : Fin n) (bound : Bound) (member : .upper source bound ∈ problem) :
    evaluate bound ∈ upperTests evaluate problem :=
  List.mem_filterMap.mpr ⟨.upper source bound, member, rfl⟩

/-- Fixed old bounds and all variable flows survive one simultaneous
interpolation. Extra tests can pin the comparison to an old output target. -/
theorem fixed_bounds_reflected (evaluate : Bound → OldTy) (problem : Problem n Bound)
    (extra : List OldTy) (values : Fin n → Common.Ty)
    (model : CommonBoundCoalescing.Models (embedOld ∘ evaluate) problem values) :
    CommonBoundCoalescing.Models (embedOld ∘ evaluate) problem
      (fun index => embedOld (envelope (upperTests evaluate problem ++ extra) (values index))) := by
  intro constraint member
  have original := model constraint member
  cases constraint with
  | lower bound target =>
      exact (Common.contextual_embedding_exact _ _).mpr
        (envelope_preserves_lower _ (values target) (evaluate bound) original)
  | flow source target =>
      exact (Common.contextual_embedding_exact _ _).mpr
        (envelope_mono _ (values source) (values target) original)
  | upper source bound =>
      exact (Common.contextual_embedding_exact _ _).mpr
        ((envelope_upper_exact _ (values source) (evaluate bound)
          (List.mem_append_left _ (upper_mem_tests evaluate problem source bound member))).mpr original)
  | check source target => exact original

/-- The fixed-bound model has an arbitrary common witness iff it has an old
regular witness. The same old witness assignment satisfies every flow edge. -/
theorem fixed_bounds_models_exact (evaluate : Bound → OldTy) (problem : Problem n Bound) :
    (∃ values : Fin n → Common.Ty,
      CommonBoundCoalescing.Models (embedOld ∘ evaluate) problem values) ↔
    ∃ values : Fin n → OldTy,
      CommonBoundCoalescing.Models (embedOld ∘ evaluate) problem (embedOld ∘ values) := by
  constructor
  · rintro ⟨values, model⟩
    exact ⟨fun index => envelope (upperTests evaluate problem ++ []) (values index),
      fixed_bounds_reflected evaluate problem [] values model⟩
  · rintro ⟨values, model⟩
    exact ⟨embedOld ∘ values, model⟩

/-- Reflection also preserves the actual comparison to any old result type,
not just satisfiability of the finite fixed-bound problem. -/
theorem fixed_bounds_output_exact (evaluate : Bound → OldTy) (problem : Problem n Bound)
    (output : Fin n) (target : OldTy) :
    (∃ values : Fin n → Common.Ty,
      CommonBoundCoalescing.Models (embedOld ∘ evaluate) problem values ∧
      Subtype (values output) (embedOld target)) ↔
    ∃ values : Fin n → OldTy,
      CommonBoundCoalescing.Models (embedOld ∘ evaluate) problem (embedOld ∘ values) ∧
      OldLe (values output) target := by
  constructor
  · rintro ⟨values, model, below⟩
    refine ⟨fun index => envelope (upperTests evaluate problem ++ [target]) (values index),
      fixed_bounds_reflected evaluate problem [target] values model, ?_⟩
    exact (envelope_upper_exact _ (values output) target
      (List.mem_append_right _ List.mem_cons_self)).mpr below
  · rintro ⟨values, model, below⟩
    exact ⟨embedOld ∘ values, model, (Common.contextual_embedding_exact _ _).mpr below⟩

end Yulang.CommonLegacyReflection
