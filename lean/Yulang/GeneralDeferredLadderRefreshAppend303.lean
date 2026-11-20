import Yulang.GeneralNominalRefinements
import Yulang.GeneralDictionaryOrdinaryTransport

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeferredLadderRefreshAppend303
open GeneralNominalRefinements (Refines)
open GeneralDictionaryOrdinaryTransport (extendState)
open GeneralNominalState (State)
open GeneralNominalIdentities (Origin)
open PresenceNormalForm (Atom)

/-- Identical allocated names and ordinary facts preserve an existing slot
embedding. The order of old entries in the two ledgers need not agree. -/
def extend_refines {old new : State} (base : Refines old new)
    (reserved : List Nat) (atoms : List (Atom Nat)) (allocated : List Origin) :
    Refines (extendState old reserved atoms allocated) (extendState new reserved atoms allocated) := by
  refine ⟨base.base,base.heads,base.nominals,?_,base.known,?_,?_,base.seed,base.constructors⟩
  · intro a member
    rcases List.mem_append.mp member with prior|added
    · exact List.mem_append_left _ (base.ordinary a prior)
    · exact List.mem_append_right _ added
  · intro a member
    rcases List.mem_append.mp member with prior|added
    · exact List.mem_append_left _ (base.reserved a prior)
    · exact List.mem_append_right _ added
  · intro a member
    rcases List.mem_append.mp member with prior|added
    · exact List.mem_append_left _ (base.allocated a prior)
    · exact List.mem_append_right _ added

theorem extend_support {old new : State}
    (supported : ∀ s ∈ GeneralNominalState.sources new, s ∈ GeneralNominalState.sources old)
    (reserved : List Nat) (atoms : List (Atom Nat)) (allocated : List Origin) :
    ∀ s ∈ GeneralNominalState.sources (extendState new reserved atoms allocated),
      s ∈ GeneralNominalState.sources (extendState old reserved atoms allocated) := by
  intro s member
  have oldConditions : s ∈ GeneralNominalState.sources new →
      s ∈ GeneralNominalState.sources old := supported s
  simp only [GeneralNominalState.sources,extendState,List.mem_append,List.flatMap_append] at member oldConditions ⊢
  grind

end Yulang.GeneralDeferredLadderRefreshAppend303
