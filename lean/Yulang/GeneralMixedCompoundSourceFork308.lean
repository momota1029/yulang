import Yulang.GeneralMixedCompoundFiveSlotDescriptor308

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 18500
set_option maxHeartbeats 10000000
namespace Yulang.GeneralMixedCompoundSourceFork308
open GeneralDictionaryJournalRefinement228Source (roles root constructors snapshot)
open GeneralDictionaryJournalRefinement228Reobserve (exactCopy loose)
open GeneralDictionaryCompoundSource238 (registry)
open GeneralDictionaryCompoundFrame238 (before installed)
open GeneralDictionaryOptionalInstall229 (model)
open GeneralMixedCompoundSourcePrefix308 (firstRevision pointBefore initial_model exact_operation early_reobservation)
open GeneralMixedCompoundFiveSlotDescriptor308 (descriptor_exact)
open GeneralNominalReobservationSteps (Revision Improves PointAt PointDescriptor)
open GeneralNominalVersionedMixedObservations233 (Reobserve reobserve_models)
open GeneralNominalVersionedRefresh232 (reobserve)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalVersionedJournal232 (State)

theorem point_exactCopy : PointDescriptor exactCopy := by
  intro p member
  change p ∈ [.type ((2 : Fin 5),2),.type (2,2)] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl <;> rfl

theorem old_one : PointAt snapshot (1 : Fin 5) := ⟨exactCopy,rfl,point_exactCopy⟩

theorem occupied (rev : Revision before.core.erased.current) (i : Fin 5) {d}
    (present : rev.entries i = some d) : i = 0 ∨ i = 1 := by
  by_cases z : i = 0
  · exact Or.inl z
  · by_cases o : i = 1
    · exact Or.inr o
    · have prior : snapshot.nominals i = none := by simp [snapshot,z,o]
      have missing := (rev.domain i).mpr prior
      rw [missing] at present
      cases present

theorem both (rev : Revision before.core.erased.current) (improved : Improves rev) :
    PointAt rev.snapshot (0 : Fin 5) ∧ PointAt rev.snapshot (1 : Fin 5) := by
  have one := improved.1 (1 : Fin 5) old_one
  obtain ⟨i,notPoint,d,seen,now⟩ := improved.2
  change rev.entries i = some d at seen
  rcases occupied rev i seen with zero|old
  · subst i; exact ⟨⟨d,seen,now⟩,one⟩
  · subst i; exact False.elim (notPoint old_one)

theorem actual_entry (rev : Revision before.core.erased.current) (cert : Reobserve before rev)
    (i : Fin 5) (point : PointAt rev.snapshot i) : rev.entries i = some exactCopy := by
  obtain ⟨d,read,shape⟩ := point
  change rev.entries i = some d at read
  have modelAfter := (reobserve_models cert).mpr initial_model
  have raw := modelAfter.1.1.2.1 i d read
  have precise := descriptor_exact i d (occupied rev i read) (rev.catalogue i d read) shape raw
  rw [precise] at read
  exact read

theorem entries_exact (rev : Revision before.core.erased.current) (cert : Reobserve before rev)
    (improved : Improves rev) : rev.entries = firstRevision.entries := by
  funext i
  change Fin 5 at i
  by_cases z : i = 0
  · subst i; exact actual_entry rev cert 0 (both rev improved).1
  · by_cases o : i = 1
    · subst i; exact actual_entry rev cert 1 (both rev improved).2
    · have prior : snapshot.nominals i = none := by simp [snapshot,z,o]
      rw [(rev.domain i).mpr prior,(firstRevision.domain i).mpr prior]

theorem revision_eq {s : GeneralNominalSaturationState.State roles} (a b : Revision s)
    (same : a.entries = b.entries) : a = b := by
  rcases a with ⟨f,cat,opq,domain⟩
  rcases b with ⟨g,cat',opq',domain'⟩
  dsimp only at same
  subst g
  rfl

theorem exact_fork {t : State roles} : Step registry root before t ↔ t = installed ∨ t = pointBefore := by
  constructor
  · intro move
    rcases exact_operation.mp move with h|⟨rev,cert,improved,eq⟩
    · exact Or.inl h
    · have same := revision_eq rev firstRevision (entries_exact rev cert improved)
      subst rev
      exact Or.inr eq
  · rintro (rfl|rfl)
    · exact GeneralDictionaryCompoundStep238.step
    · exact early_reobservation

end Yulang.GeneralMixedCompoundSourceFork308
