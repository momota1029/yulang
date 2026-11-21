import Yulang.GeneralWherePhysicalChildModel319

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 34000
set_option maxHeartbeats 37000000
namespace Yulang.GeneralWherePhysicalChildCert319
open GeneralWhereOriginSingleSource318 (registry)
open GeneralWhereOriginSingleCells318 (loOld hi loNow)
open GeneralWhereOriginSingleModel318 (previousLo previousHi presentLo)
open GeneralWherePhysicalCommit319 (final newChild emission models)
open GeneralWherePhysicalChildRead319 (packet plan locate finished)
open GeneralWherePhysicalChildModel319 (head held)
open GeneralWherePhysicalCurrentFrame319 (endpoints_or_original)
open GeneralWherePhysicalActive319 (active ctx)
open GeneralWherePhysicalFresh319 (raw lower_id upper_id lowerSlot upperSlot finalLayout)
open GeneralWherePhysicalBase319 (source_old source_new row_old)
open GeneralWherePhysicalIndex319 (old new)
open GeneralWherePhysicalPatch319 (n)
open GeneralWherePhysicalPast319 (point)
open GeneralDictionaryJournalRefinement228Source (roles snapshot)
open GeneralNominalState (sources)
open GeneralNominalIdentities (source)
open GeneralLiveCompoundRegistry316 (leaf leaf_checked)
open GeneralNominalVersionedCandidates231 (Prepared inputs)
open GeneralNominalVersionedEvidence231 (Frame Certificate Evidence)
open GeneralNominalCenters
open GeneralWhereVersionInstall317 (Models)
open GeneralNominalCommonBridge (Assignment)

theorem final_sources {k : Nat} (hit : k ∈ sources active) : k ∈ sources point ∨ k = loNow := by
  have typeCase (i : Fin 8) (eq : active.base.source i = k) : k ∈ sources point ∨ k = loNow := by
    refine Fin.addCases (m := 7) (n := 1) (fun j e => ?_) (fun j e => ?_) i eq
    · change GeneralWherePhysicalBase319.source finalLayout (old 1 j) = k at e
      rw [source_old] at e
      exact Or.inl (e ▸ GeneralNominalAllocationSupport.slot_source point j)
    · have one : j = 0 := Subsingleton.elim ..
      subst j
      exact Or.inr (e.symm.trans lower_id)
  simp only [sources,List.mem_append] at hit
  rcases hit with ((types|rows)|reserved)|ordinary
  · obtain ⟨i,e⟩ := List.mem_ofFn.mp types
    exact typeCase i e
  · obtain ⟨i,e⟩ := List.mem_ofFn.mp rows
    refine Fin.addCases (m := 7) (n := 1) (fun j eq => ?_) (fun j eq => ?_) i e
    · change GeneralWherePhysicalBase319.rowSource finalLayout (old 1 j) = k at eq
      rw [row_old] at eq
      exact .inl (eq ▸ List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_right _ (List.mem_ofFn.mpr ⟨j,rfl⟩))))
    · have ej : j = 0 := Subsingleton.elim ..
      subst j
      exact .inr eq.symm
  · exact .inl (List.mem_append_left _ (List.mem_append_right _ reserved))
  · exact .inl (List.mem_append_right _ ordinary)

theorem no_reserved (k : GeneralNominalIdentities.Origin)
    (reserved : source active.seed k ∈ GeneralVersionedInstallDomain313.reserve packet) :
    source active.seed k ∉ sources active := by
  have small := GeneralVersionedInstallDomain313.reserve_purpose packet reserved
  intro hit
  rcases final_sources hit with prior|lower
  · rcases endpoints_or_original prior with base|lo|hi'
    · have high := GeneralNominalIdentities.source_above_seed active.seed k
      have bound := GeneralDictionaryJournalRefinement228Source.source_bound _ base
      change 4 < source active.seed k at high
      omega
    · obtain ⟨o,h,e⟩ := previousLo.high (t := active) rfl
      exact GeneralVersionedHighOrigins315.distinct (a := k) (b := o) (by omega) active.seed (lo.trans e)
    · obtain ⟨o,h,e⟩ := previousHi.high (t := active) rfl
      exact GeneralVersionedHighOrigins315.distinct (a := k) (b := o) (by omega) active.seed (hi'.trans e)
  · obtain ⟨o,h,e⟩ := presentLo.high (t := active) rfl
    exact GeneralVersionedHighOrigins315.distinct (a := k) (b := o) (by omega) active.seed (lower.trans e)

theorem linked : GeneralNominalState.Linked active (inputs newChild.occurrence).demand := by
  constructor
  · intro i
    have z : i = (0 : Fin 1) := Subsingleton.elim ..
    subst i
    rw [show (inputs newChild.occurrence).demand.arguments 0 = (loNow,hi) from GeneralWherePhysicalCurrentRead319.child_bounds]
    exact ⟨lower_id ▸ GeneralNominalAllocationSupport.slot_source active lowerSlot,
      upper_id ▸ GeneralNominalAllocationSupport.slot_source active upperSlot⟩
  · intro _ impossible
    cases impossible

theorem prepared (m : Assignment) (valid : Models final m) :
    Prepared registry ctx newChild.occurrence leaf := by
  refine ⟨GeneralDictionaryJournalRefinement228Source.metadata registry rfl,linked,
    [(lowerSlot,upperSlot)],locate,?_,finished,m,
    (GeneralNominalVersionedCandidates231.headModels_packet_iff packet m).mpr (head m valid)⟩
  intro key listed hit
  have reserved : source active.seed key ∈ GeneralVersionedInstallDomain313.reserve packet :=
    List.mem_map.mpr ⟨key,listed,rfl⟩
  exact False.elim (no_reserved key reserved hit)

theorem frame (m : Assignment) (valid : Models final m) :
    Frame registry final.mixed.core newChild.occurrence leaf.id plan := by
  refine ⟨rfl,rfl,rfl,rfl,?_,?_,List.mem_cons_of_mem _ (List.mem_singleton_self _),rfl,locate,prepared m valid⟩
  · apply List.mem_append_right
    rw [emission]; exact List.mem_cons_self
  · apply List.mem_append_right
    rw [emission]; exact List.mem_cons_self

theorem terminal : GeneralNominalVersionedFrame231.children packet = [] := by
  unfold GeneralNominalVersionedFrame231.children GeneralDictionaryEmissionPlans.children
    GeneralCanonicalChildOrder.canonicalEmit GeneralCanonicalChildOrder.canonicalDeclaration
    GeneralCanonicalChildOrder.canonicalRequirements GeneralDeclarationDemands.emitAll
  simp [List.mergeSort_nil]

theorem certificate (m : Assignment) (valid : Models final m) :
    Certificate registry final.mixed.core m newChild.occurrence leaf.id [] plan :=
  ⟨frame m valid,terminal.symm,held m valid,fun _ absent => by cases absent⟩

theorem leaf_evidence (m : Assignment) (valid : Models final m) :
    Evidence registry final.mixed.core m newChild.occurrence (.node leaf.id []) :=
  GeneralNominalVersionedEvidence231.evidence_leaf ⟨plan,certificate m valid⟩

end Yulang.GeneralWherePhysicalChildCert319
