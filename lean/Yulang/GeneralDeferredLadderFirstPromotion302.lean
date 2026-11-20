import Yulang.GeneralDeferredLadderAvailability302

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeferredLadderFirstPromotion302
open GeneralDeferredLadderLedger302 (Phase)
open GeneralDeferredLadderExact302 (RawStep Promotion)
open GeneralDeferredLadderTrace302 (InstallTrace exact_prefix)
open GeneralDeferredLadderAdvance302 (run)
open GeneralDeferredLadderAvailability302 (no_root_evidence)
open GeneralObservedLadderRefresh301 (before)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalExamples (registry displayRoot)
open GeneralDeclarationExamples (roles)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
open B4Target (Steps)

/-- The first promotion edge and its actual install-only prefix.
The suffix is still the full raw relation, not a restricted iterator. -/
def FirstPromotion (n : Nat) (last : State roles) : Prop :=
  ∃ k, ∃ cap : k ≤ n+1, ∃ next,
    InstallTrace n k (before n) (run n k cap).state ∧
    RawStep (run n k cap).state next ∧
    Promotion n (run n k cap).state next ∧ Steps RawStep next last

theorem trace_split (n : Nat) (last : State roles) (trace : Steps RawStep (before n) last) :
    (∃ k, InstallTrace n k (before n) last) ∨ FirstPromotion n last := by
  induction trace with
  | refl => exact .inl ⟨0,.zero _⟩
  | tail _ step ih =>
    rcases ih with ⟨k,plain⟩ | ⟨k,cap,next,kept,strict,promoted,path⟩
    · classical
      have casesOf {s t : State roles} (_edge : RawStep s t) : Promotion n s t ∨ ¬ Promotion n s t := Classical.em _
      rcases casesOf step with found|found
      · obtain ⟨cap,eq⟩ := exact_prefix n 0 (by omega) plain
        have state_indices (a b : Nat) (same : a = b) (left : a ≤ n+1) (right : b ≤ n+1) :
            (run n a left).state = (run n b right).state := by
          subst b
          rfl
        have same := eq.trans (state_indices (0+k) k (Nat.zero_add k) cap (by omega))
        cases same
        exact .inr ⟨k,by omega,_,plain,step,found,.refl⟩
      · exact .inl ⟨k+1,.next plain step found⟩
    · exact .inr ⟨k,cap,next,kept,strict,promoted,.tail path step⟩

theorem necessary_for_halt (n : Nat) (last : State roles) (trace : Steps RawStep (before n) last)
    (halt : ∀ s, ¬ RawStep last s) : FirstPromotion n last := by
  rcases trace_split n last trace with ⟨k,plain⟩|yes
  · obtain ⟨next,step,_⟩ := GeneralDeferredLadderTrace302.promotion_required_to_halt n k last plain
    exact False.elim (halt next step)
  · exact yes

theorem necessary_for_dictionary (n : Nat) (last : State roles) (trace : Steps RawStep (before n) last)
    (m : Assignment) (d : Payload) (evidence : (boundary roles).Evidence registry last m displayRoot d) :
    FirstPromotion n last := by
  rcases trace_split n last trace with ⟨k,plain⟩|yes
  · obtain ⟨cap,rfl⟩ := exact_prefix n 0 (by omega) plain
    exact False.elim (no_root_evidence n _ cap m d evidence)
  · exact yes

end Yulang.GeneralDeferredLadderFirstPromotion302
