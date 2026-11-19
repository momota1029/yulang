import Yulang.GeneralRebasePhasePrivate281

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseAggregateCollapse281
open GeneralNominalCommonBridge (Assignment)
open GeneralSourceState (Interval)
open CommonNominalFullCarrier (Subtype Equivalent subtype_refl subtype_trans)
open GeneralNominalAllocation (lower upper equations)
open GeneralNominalCaptureMerges (lower_exact upper_exact equations_exact)
open GeneralRebasePortMeaning280 (Matches)
open GeneralRebasePortProjection280 (Respects)
open GeneralRebasePortCopy280 (PairWrites)
open PresenceNormalForm (All)

theorem lower_collapse (m : Assignment) (bounds : List Interval) (used : sample ∈ bounds)
    (equiv : ∀ b ∈ bounds, Matches m b sample) :
    Equivalent ((lower bounds).eval CommonNominalFullCarrier.model m) (m sample.1).1 := by
  have populated : bounds ≠ [] := by
    rintro rfl
    cases used
  refine ⟨(lower_exact m bounds populated _).mpr (fun b h => (equiv b h).1.1),?_⟩
  exact (lower_exact m bounds populated _).mp (subtype_refl _) sample used

theorem upper_collapse (m : Assignment) (bounds : List Interval) (used : sample ∈ bounds)
    (equiv : ∀ b ∈ bounds, Matches m b sample) :
    Equivalent ((upper bounds).eval CommonNominalFullCarrier.model m) (m sample.2).1 := by
  have populated : bounds ≠ [] := by
    rintro rfl
    cases used
  refine ⟨?_,(upper_exact m bounds populated _).mpr (fun b h => (equiv b h).2.2)⟩
  exact (upper_exact m bounds populated _).mp (subtype_refl _) sample used

theorem equivalence_retarget {a b c : CommonNominalFullCarrier.Ty}
    (value : Equivalent b c) : Equivalent a b ↔ Equivalent a c := by
  constructor
  · intro h
    exact ⟨subtype_trans h.1 value.1,subtype_trans value.2 h.2⟩
  · intro h
    exact ⟨subtype_trans h.1 value.2,subtype_trans value.1 h.2⟩

theorem pair_respects (m : Assignment) (target source : Interval) :
    Respects (PairWrites target source) m ↔ Matches m target source := by
  constructor
  · intro h
    exact ⟨h _ List.mem_cons_self,h _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))⟩
  · intro h
    intro row listed
    change row ∈ [(target.1,source.1),(target.2,source.2)] at listed
    rcases List.mem_cons.mp listed with rfl|last
    · exact h.1
    · cases List.mem_singleton.mp last
      exact h.2

theorem collapse_atoms (m : Assignment) (bounds : List Interval) (target : Interval)
    (used : sample ∈ bounds) (equiv : ∀ b ∈ bounds, Matches m b sample) :
    All CommonNominalFullCarrier.model m (equations target.1 (lower bounds) ++ equations target.2 (upper bounds)) ↔
      Respects (PairWrites target sample) m := by
  rw [PresenceNormalForm.all_append,equations_exact,equations_exact,pair_respects]
  exact and_congr (equivalence_retarget (lower_collapse m bounds used equiv))
    (equivalence_retarget (upper_collapse m bounds used equiv))

end Yulang.GeneralRebaseAggregateCollapse281
