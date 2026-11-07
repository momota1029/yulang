import Yulang.CommonEffectDepthBoundary
import Yulang.CommonFiniteOptionalInspection

/-! A finite-choice obstruction for constructor depths, not B3/E2.
Even two fixed candidate targets of the SAME source may cover every depth
without either candidate being a whole Common supertype. Thus the proved
negative-rank compactness cannot simply be run a second time on depth. -/
namespace Yulang.CommonEffectDepthChoiceBoundary
open Common (Ty Row)
open CommonFinite (ProducerLe ProbeAt ProbeStep MaskedProbeStep)
open CommonEffectDepthBoundary (badDefault not_at_zero)

abbrev BelowAt (depth : Nat) (source target : Ty) : Prop :=
  ProducerLe Common.rowLe (Common.observeTy depth source) (Common.observeTy depth target)

theorem width_below_positive (depth : Nat) : BelowAt (depth + 1) Common.emptyRecord badDefault := by
  exact CommonEffectDepthBoundary.at_one

theorem default_below_zero : BelowAt 0 badDefault (Common.required 0 .top) :=
  CommonFiniteOptionalInspection.default_zero_required 0 (.base .int) (.base .unit) .top

theorem default_not_below_one : ¬ BelowAt 1 badDefault (Common.required 0 .top) := by
  intro below
  let environment : CommonFinite.Environment Row := ⟨fun _ => .bottom, fun _ => []⟩
  have field : ProbeAt Common.rowLe 0 environment (Common.observeTy 1 (Common.required 0 .top)) (.field 0 .trivial) := by
    simp [Common.observeTy, Common.required, Common.record, CommonSyntax.Layer.evalAt,
      CommonSyntax.observe, CommonSyntax.graph, ProbeAt, ProbeStep, MaskedProbeStep]
  have impossible := (CommonFinite.producerLe_iff_probe _ _).mp below 0 environment (.field 0 .trivial) field
  exact impossible.1

theorem pair_successor (depth : Nat) (a b c d : Ty) :
    BelowAt (depth + 1) (Common.pair a b) (Common.pair c d) ↔ BelowAt depth a c ∧ BelowAt depth b d :=
  CommonFinite.producerLe_pair_iff _ _ _ _

def source : Ty := Common.pair Common.emptyRecord badDefault
def first : Ty := Common.pair badDefault .top
def second : Ty := Common.pair .top (Common.required 0 .top)

theorem first_zero : BelowAt 0 source first := CommonFinite.producerLe_refl _
theorem second_one : BelowAt 1 source second :=
  (pair_successor 0 _ _ _ _).mpr ⟨CommonEffectTypeNormalisation.subtype_top Common.emptyRecord 0, default_below_zero⟩

theorem first_later (depth : Nat) : BelowAt (depth + 2) source first :=
  (pair_successor (depth + 1) _ _ _ _).mpr
    ⟨width_below_positive depth, CommonEffectTypeNormalisation.subtype_top badDefault (depth + 1)⟩

theorem first_not_one : ¬ BelowAt 1 source first := fun below => not_at_zero ((pair_successor 0 _ _ _ _).mp below).1
theorem second_not_two : ¬ BelowAt 2 source second := fun below => default_not_below_one ((pair_successor 1 _ _ _ _).mp below).2

theorem each_depth : ∀ depth, ∃ target ∈ [first, second], BelowAt depth source target := by
  intro depth
  cases depth with
  | zero => exact ⟨first, by simp, first_zero⟩
  | succ depth =>
    cases depth with
    | zero => exact ⟨second, by simp, second_one⟩
    | succ depth => exact ⟨first, by simp, first_later depth⟩

theorem no_uniform_target : ¬ ∃ target ∈ [first, second], Common.Subtype source target := by
  rintro ⟨target, member, below⟩
  rcases List.mem_cons.mp member with rfl | last
  · exact first_not_one (below 1)
  · have same : target = second := List.mem_singleton.mp last
    subst target
    exact second_not_two (below 2)

theorem finite_depth_compactness_fails :
    ¬ (∀ (fixed : Ty) (targets : List Ty),
      (∀ depth, ∃ target ∈ targets, BelowAt depth fixed target) → ∃ target ∈ targets, Common.Subtype fixed target) :=
  fun compact => no_uniform_target (compact source [first, second] each_depth)

def function (input : Ty) : Ty := Common.arrow input Common.rowEmpty (.base .unit) Common.rowEmpty

theorem overloaded_callable : Common.Subtype (.inter (function first) (function second)) (function source) := by
  intro depth
  cases depth with
  | zero => exact CommonBoundCoalescing.inter_le_left (function first) (function second) 0
  | succ depth =>
    obtain ⟨target, member, below⟩ := each_depth depth
    have arrowBelow : BelowAt (depth + 1) (function target) (function source) :=
      (CommonFinite.producerLe_arrow_iff Common.rowLe_refl Common.rowLe_trans _ _ _ _ _ _ _ _).mpr
        ⟨below, Common.rowLe_refl _, CommonFinite.producerLe_refl _, Common.rowLe_refl _⟩
    rcases List.mem_cons.mp member with rfl | member
    · exact CommonFinite.producerLe_trans
        (CommonBoundCoalescing.inter_le_left (function first) (function second) (depth + 1)) arrowBelow
    · have same : target = second := List.mem_singleton.mp member
      subst target
      exact CommonFinite.producerLe_trans
        (CommonBoundCoalescing.inter_le_right (function first) (function second) (depth + 1)) arrowBelow

theorem inter_arrow_disjunction_fails :
    ¬ (∀ a b input : Ty, Common.Subtype (.inter (function a) (function b)) (function input) →
      Common.Subtype input a ∨ Common.Subtype input b) := by
  intro split
  have selected := split first second source overloaded_callable
  exact selected.elim (fun below => first_not_one (below 1)) (fun below => second_not_two (below 2))

end Yulang.CommonEffectDepthChoiceBoundary
