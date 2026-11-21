import Yulang.GeneralWherePhysicalCurrentModel319

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 33000
set_option maxHeartbeats 32000000
namespace Yulang.GeneralWherePhysicalCurrentFrame319
open GeneralWhereOriginSingleSource318
open GeneralWherePhysicalCurrentRead319 (packet plan locate exact_report zero)
open GeneralWherePhysicalHead319 (current_head)
open GeneralWherePhysicalPatch319 (n)
open GeneralWherePhysicalReobserve319 (updated old_sites)
open GeneralWherePhysicalPast319 (point pointCtx layout low_id high_id)
open GeneralWherePhysicalIndex319 (old new)
open GeneralWherePhysicalBase319 (source_old row_old source_new)
open GeneralWhereOriginSingleCells318 (loOld hi)
open GeneralWhereOriginSingleModel318 (previousLo previousHi)
open GeneralDictionaryJournalRefinement228Source (roles root snapshot)
open GeneralNominalVersionedCandidates231 (Prepared Survivor Unique inputs)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalState (sources)
open GeneralNominalIdentities (source)
open GeneralNominalCenters

theorem endpoints_or_original {k : Nat} (member : k ∈ sources point) :
    k ∈ sources snapshot ∨ k = loOld ∨ k = hi := by
  have slotCase (i : Fin 7) (eq : point.base.source i = k) : k ∈ sources snapshot ∨ k = loOld ∨ k = hi := by
    refine Fin.addCases (m := 5) (n := 2) (fun j h => ?_) (fun j h => ?_) i eq
    · change GeneralWherePhysicalBase319.source layout (old 2 j) = k at h
      rw [source_old] at h
      exact Or.inl (h ▸ GeneralNominalAllocationSupport.slot_source snapshot j)
    · have two : j = 0 ∨ j = 1 := by omega
      rcases two with rfl|rfl
      · exact Or.inr (.inl (h.symm.trans low_id))
      · exact Or.inr (.inr (h.symm.trans high_id))
  simp only [sources,List.mem_append] at member
  rcases member with ((one|two)|reserve)|ordinary
  · obtain ⟨i,eq⟩ := List.mem_ofFn.mp one
    exact slotCase i eq
  · obtain ⟨i,eq⟩ := List.mem_ofFn.mp two
    have same : point.base.rowSource i = point.base.source i := by
      refine Fin.addCases (m := 5) (n := 2) ?_ ?_ i <;> intro j
      · change GeneralWherePhysicalBase319.rowSource layout (old 2 j) =
          GeneralWherePhysicalBase319.source layout (old 2 j)
        rw [row_old,source_old]
      · change Fin.addCases snapshot.base.rowSource layout.ids (new 5 j) =
          GeneralWherePhysicalBase319.source layout (new 5 j)
        rw [Fin.addCases_right,source_new]
    exact slotCase i (same.symm.trans eq)
  · exact .inl (List.mem_append_left _ (List.mem_append_right _ reserve))
  · exact .inl (List.mem_append_right _ ordinary)

theorem no_reserved (k : GeneralNominalIdentities.Origin)
    (reserved : source point.seed k ∈ GeneralVersionedInstallDomain313.reserve packet) :
    source point.seed k ∉ sources point := by
  have small := GeneralVersionedInstallDomain313.reserve_purpose packet reserved
  intro hit
  rcases endpoints_or_original hit with base|lo|hi'
  · have high := GeneralNominalIdentities.source_above_seed point.seed k
    have bound := GeneralDictionaryJournalRefinement228Source.source_bound _ base
    change 4 < source point.seed k at high
    omega
  · obtain ⟨o,h,e⟩ := previousLo.high (t := point) rfl
    exact GeneralVersionedHighOrigins315.distinct (a := k) (b := o) (by omega) point.seed (lo.trans e)
  · obtain ⟨o,h,e⟩ := previousHi.high (t := point) rfl
    exact GeneralVersionedHighOrigins315.distinct (a := k) (b := o) (by omega) point.seed (hi'.trans e)

theorem linked : GeneralNominalState.Linked point (inputs root).demand := by
  constructor
  · intro i
    have found : point.base.source zero = 0 := rfl
    have known : 0 ∈ sources point := found ▸ GeneralNominalAllocationSupport.slot_source point zero
    exact ⟨known,known⟩
  · intro _ impossible
    cases impossible

theorem prepared : Prepared registry pointCtx root declaration := by
  refine ⟨GeneralDictionaryJournalRefinement228Source.metadata registry rfl,linked,
    [(zero,zero)],locate,?_,?_,n,
    (GeneralNominalVersionedCandidates231.headModels_packet_iff packet n).mpr current_head⟩
  · intro key enumerated hit
    have reserved : source point.seed key ∈ GeneralVersionedInstallDomain313.reserve packet :=
      List.mem_map.mpr ⟨key,enumerated,rfl⟩
    exact False.elim (no_reserved key reserved hit)
  · rw [exact_report]
    exact ⟨rfl,rfl,rfl⟩

theorem frame : Frame registry updated.mixed.core root declaration.id plan :=
  ⟨rfl,rfl,rfl,rfl,List.mem_cons_self,List.mem_cons_self,List.mem_cons_self,rfl,locate,prepared⟩

theorem no_pending : ¬ GeneralNominalState.RootPending point (inputs root).demand := by
  rintro ⟨i,side⟩
  have nz : GeneralNominalState.Known point 0 := ⟨zero,rfl,.inr ⟨_,GeneralWherePhysicalCurrentRead319.nominal0⟩⟩
  exact side nz

theorem survivor : Survivor registry pointCtx root declaration.id (GeneralNominalVersionedFrame231.children packet) :=
  ⟨no_pending,declaration,List.mem_cons_self,declaration_checked,
    rfl,rfl,[(zero,zero)],locate,prepared,rfl⟩

theorem unique : Unique registry pointCtx root declaration.id (GeneralNominalVersionedFrame231.children packet) := by
  refine ⟨survivor,?_⟩
  intro key kids alternative
  have shadow := alternative
  obtain ⟨_,d,seen,_,eq,role,_,_,_,_⟩ := shadow
  rcases List.mem_cons.mp seen with one|rest
  · subst d; subst key
    exact ⟨rfl,GeneralNominalVersionedCandidates231.survivor_children_functional
      GeneralWhereOriginSingleSource318.checked alternative survivor⟩
  · cases List.mem_singleton.mp rest
    cases role

end Yulang.GeneralWherePhysicalCurrentFrame319
