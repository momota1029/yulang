import Yulang.GeneralDeclarativeWhereReuse346

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWhereStore346
open GeneralDeclarations (Registry)
open GeneralNominalCenters (Plan)
open GeneralWhereVersionInstall317 (Journal)
open GeneralWhereOriginTrace318 (Trace rawOf Blame)
open GeneralWhereOriginConfig318 (Config history_config)
open GeneralWhereOriginDelta318 (High)
open GeneralNominalVersionedRefresh232 (reobserve)
open GeneralNominalReobservationSteps (Revision)
open GeneralDictionaryBinderLocations (sourceSlot sourceSlot_exact)
open GeneralWhereOriginDelta318 (Cell)

structure Store (r : Registry) (j : Journal rs) : Prop where
  owned : ∀ (i : Fin (rawOf j).base.slots), High (rawOf j) ((rawOf j).base.source i) →
    Blame j ((rawOf j).base.source i)
  drawing : ∀ p ∈ j.versionedWhere, Config r j p

theorem from_trace {j : Journal rs} (trace : Trace r j) : Store r j :=
  ⟨GeneralWhereOriginTrace318.source_origin trace,history_config trace⟩

def revise (j : Journal rs) (revision : Revision j.mixed.core.erased.current) : Journal rs :=
  ⟨reobserve j.mixed revision,j.versionedWhere⟩

/-- Nominal descriptor revision uses the same raw basis, interpretation
and version journal, without retaining the literal old descriptors. -/
theorem under_revision {j : Journal rs} (tracked : Store r j)
    (revision : Revision j.mixed.core.erased.current) : Store r (revise j revision) := by
  refine ⟨?_,?_⟩
  · intro i high
    exact tracked.owned i high
  · intro p present
    obtain ⟨registry,visible,meaning,seed⟩ := tracked.drawing p present
    exact ⟨registry,visible,meaning,seed⟩

theorem exact_before_lookup {j : Journal rs} (tracked : Store r j)
    {n : Nat} {i : Fin (rawOf j).base.slots}
    (atSlot : sourceSlot (rawOf j).base n = some i) (high : High (rawOf j) n) :
    ∃ q : Plan rs, ∃ (c : Cell q) (k : Nat),
      j.versionedWhere[k]? = some q ∧ c.row.target = n := by
  have id := (sourceSlot_exact ..).mp atSlot
  obtain ⟨p,listed,c,same⟩ := tracked.owned i (id.symm ▸ high)
  obtain ⟨k,seen⟩ := List.mem_iff_getElem?.mp listed
  exact ⟨p,c,k,seen,same.trans id⟩

end Yulang.GeneralDeclarativeWhereStore346
