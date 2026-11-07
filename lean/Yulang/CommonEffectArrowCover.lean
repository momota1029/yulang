import Yulang.CommonEffectRankCompactness
import Yulang.CommonBoundCoalescing

/-! Exact finite-family arrow inspection retaining depth-wise domain choice.
No candidate is forced to serve all constructor depths. Negative ranks are
eliminated by the proved finite-rank compactness; a depth-cover obligation
remains explicit rather than becoming a condition on solved parameters. -/
namespace Yulang.CommonEffectArrowCover
open Common (Ty Row)
open CommonFinite (ProducerLe ProbeAt)
open CommonEffectRankMonotonicity (Compare compare_refl)
open CommonBoundCoalescing (meetTypes)

def family (inputs : List Ty) (incoming : Row) (result : Ty) (outgoing : Row) : Ty :=
  meetTypes (inputs.map (fun input => Common.arrow input incoming result outgoing))

def Covers (inputs : List Ty) (target : Ty) : Prop :=
  ∀ depth, ∃ input ∈ inputs, ProducerLe Common.rowLe (Common.observeTy depth target) (Common.observeTy depth input)

theorem argument_family (inputs : List Ty) (incoming : Row) (result : Ty) (outgoing : Row)
    (depth rank : Nat) (environment : CommonFinite.Environment Row) (name : Nat) :
    ProbeAt Common.rowLe (rank + 1) environment (Common.observeTy (depth + 1) (family inputs incoming result outgoing)) (.arrowArgument name) ↔
      ∃ input ∈ inputs, Compare rank (environment.types name) (Common.observeTy depth input) := by
  induction inputs with
  | nil => simp [family, meetTypes, Common.observeTy, CommonSyntax.Layer.evalAt, ProbeAt,
      CommonFinite.ProbeStep, CommonFinite.MaskedProbeStep]
  | cons input rest ih =>
    change (Compare rank (environment.types name) (Common.observeTy depth input) ∨
      ProbeAt Common.rowLe (rank + 1) environment (Common.observeTy (depth + 1) (family rest incoming result outgoing)) (.arrowArgument name)) ↔ _
    rw [ih]
    simp only [List.mem_cons, exists_eq_or_imp]

/-- Arbitrary same result and rows, arbitrary finite family of arbitrary
Common domains. Empty input families are included. -/
theorem family_subtype_exact (inputs : List Ty) (target : Ty) (incoming : Row) (result : Ty) (outgoing : Row) :
    Common.Subtype (family inputs incoming result outgoing) (Common.arrow target incoming result outgoing) ↔ Covers inputs target := by
  constructor
  · intro below depth
    let pairs := inputs.map (fun input => (Common.observeTy depth target, Common.observeTy depth input))
    have everyRank : ∀ rank, ∃ pair ∈ pairs, Compare rank pair.1 pair.2 := by
      intro rank
      let environment : CommonFinite.Environment Row := ⟨fun _ => Common.observeTy depth target, fun _ => []⟩
      have targetAccepted : ProbeAt Common.rowLe (rank + 1) environment
          (Common.observeTy (depth + 1) (Common.arrow target incoming result outgoing)) (.arrowArgument 0) :=
        compare_refl rank (Common.observeTy depth target)
      have familyAccepted := (CommonFinite.producerLe_iff_probe _ _).mp (below (depth + 1)) (rank + 1) environment (.arrowArgument 0) targetAccepted
      obtain ⟨input, member, accepted⟩ := (argument_family inputs incoming result outgoing depth rank environment 0).mp familyAccepted
      exact ⟨(Common.observeTy depth target, Common.observeTy depth input), List.mem_map.mpr ⟨input, member, rfl⟩, accepted⟩
    obtain ⟨pair, member, accepted⟩ := (CommonEffectRankCompactness.finite_rank_exact pairs).mp everyRank
    obtain ⟨input, present, rfl⟩ := List.mem_map.mp member
    exact ⟨input, present, accepted⟩
  · intro cover depth
    cases depth with
    | zero =>
      obtain ⟨input, member, _⟩ := cover 0
      exact CommonBoundCoalescing.meetTypes_le_member
        (List.mem_map.mpr ⟨input, member, rfl⟩ : Common.arrow input incoming result outgoing ∈ _) 0
    | succ depth =>
      obtain ⟨input, member, accepted⟩ := cover depth
      have arrowBelow : ProducerLe Common.rowLe
          (Common.observeTy (depth + 1) (Common.arrow input incoming result outgoing))
          (Common.observeTy (depth + 1) (Common.arrow target incoming result outgoing)) :=
        (CommonFinite.producerLe_arrow_iff Common.rowLe_refl Common.rowLe_trans _ _ _ _ _ _ _ _).mpr
          ⟨accepted, Common.rowLe_refl _, CommonFinite.producerLe_refl _, Common.rowLe_refl _⟩
      exact CommonFinite.producerLe_trans
        (CommonBoundCoalescing.meetTypes_le_member
          (List.mem_map.mpr ⟨input, member, rfl⟩ : Common.arrow input incoming result outgoing ∈ _) (depth + 1)) arrowBelow

end Yulang.CommonEffectArrowCover
