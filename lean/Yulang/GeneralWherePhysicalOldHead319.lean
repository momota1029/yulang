import Yulang.GeneralWherePhysicalOldValues319

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28500
set_option maxHeartbeats 26000000
namespace Yulang.GeneralWherePhysicalOldHead319
open GeneralWhereOriginSingleSource318
open GeneralWhereOriginSingleRead318 (firstOrigin secondOrigin old_query old_report)
open GeneralWherePhysicalOldValues319 (old_head baseline_raw head_value binder_value bounded)
open GeneralDictionaryJournalRefinement228Source (roles root snapshot context interpretation root_point)
open GeneralNominalVersionedPlans231 (SchemaHolds variables)
open GeneralNominalVersionedCandidates231 (Prepared Survivor Unique inputs)
open GeneralLiveCompoundLeafProof316 (w)
open GeneralNominalRecursiveInspection
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalCenters
open GeneralDeclarations
open CommonNominalFullCarrier

abbrev start := GeneralNominalVersionedJournal232.initial context root
abbrev before : GeneralWhereVersionInstall317.Journal roles := ⟨start,[]⟩

theorem prepared : Prepared registry context root declaration := by
  refine ⟨GeneralDictionaryJournalRefinement228Source.metadata registry rfl,
    ⟨?_,by intro output impossible; cases impossible⟩,[(0,0)],by decide +kernel,?_,?_,w,
    (GeneralNominalVersionedCandidates231.headModels_packet_iff older w).mpr old_head⟩
  · intro i
    exact ⟨GeneralNominalAllocationSupport.slot_source snapshot (0 : Fin 5),
      GeneralNominalAllocationSupport.slot_source snapshot (0 : Fin 5)⟩
  · intro key _ hit
    have high := GeneralNominalIdentities.source_above_seed snapshot.seed key
    have small := GeneralDictionaryJournalRefinement228Source.source_bound _ hit
    change 4 < GeneralNominalIdentities.source snapshot.seed key at high
    change GeneralNominalIdentities.source snapshot.seed key ≤ 4 at small
    omega
  · rw [old_report]
    exact ⟨rfl,rfl,rfl⟩

theorem frame : Frame registry start.core root declaration.id oldPlan :=
  ⟨rfl,rfl,rfl,rfl,List.mem_singleton_self _,List.mem_singleton_self _,List.mem_cons_self,rfl,by decide +kernel,prepared⟩

theorem survivor : Survivor registry context root declaration.id (GeneralNominalVersionedFrame231.children older) :=
  ⟨GeneralDictionaryCompoundPacket238.known,declaration,List.mem_cons_self,declaration_checked,
    rfl,rfl,[(0,0)],by decide +kernel,prepared,rfl⟩

theorem unique : Unique registry context root declaration.id (GeneralNominalVersionedFrame231.children older) := by
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

theorem schema_code : oldPlan.headSchema =
    { tests := [(.source 0,.nominal 0 2)]
      variables := [⟨0,firstOrigin,.actual⟩,⟨1,secondOrigin,.actual⟩] } := by
  unfold Plan.headSchema
  rw [old_query]
  simp [GeneralNominalMaterialization.schemas,GeneralNominalMaterialization.schema,
    GeneralNominalMaterialization.Schema.append,List.ofFn_succ,oldPlan,rootSite,firstOrigin,secondOrigin]

theorem test : GeneralNominalOriginTerms.Head w (.source 0) (.nominal 0 2) := by
  refine ⟨⟨_,.source 0⟩,?_⟩
  intro value seen
  cases seen
  exact ⟨[.inl .emptyRecord,.inl .emptyRecord],rfl,head_value.1,head_value.2⟩

theorem sees (i : Nat) (known : i = 0 ∨ i = 1) :
    Observes w (.nominal (.source 0) 0 i) .emptyRecord := by
  rcases known with rfl|rfl <;> exact .nominal (.source 0) head_value rfl

theorem actual_same (i : Nat) (known : i = 0 ∨ i = 1) :
    GeneralNominalOriginTerms.Same w (.nominal (.source 0) 0 i)
      (.source (GeneralNominalVersionedFrame231.binder oldPlan i)) := by
  refine ⟨⟨_,sees i known⟩,⟨_,.source _⟩,?_⟩
  intro a b one two
  cases two
  rw [binder_value i known]
  exact nominal_observation_unique w (.argument (.source 0) 0 i) a .emptyRecord one (sees i known)

theorem schema_holds : SchemaHolds oldPlan oldPlan.headSchema w := by
  rw [schema_code]
  constructor
  · intro entry present
    cases List.mem_singleton.mp present
    exact test
  · intro entry present
    rcases List.mem_cons.mp present with rfl|last
    · exact actual_same 0 (.inl rfl)
    · cases List.mem_singleton.mp last
      exact actual_same 1 (.inr rfl)

theorem all_captures (n : Nat)
    (used : n ∈ older.declaration.inputNames ∨ GeneralNominalSharedCaptures.Needed older n) :
    GeneralNominalCaptureMerges.Fits w ((GeneralNominalVersionedFrame231.capture older).inputs n)
      (w (GeneralNominalVersionedFrame231.binder oldPlan n)).1 := by
  apply bounded
  rcases used with head|⟨c,seen,variables⟩
  · change n ∈ [0,1] at head
    simpa using head
  · cases List.mem_singleton.mp seen
    change n ∈ [0] at variables
    exact .inl (List.mem_singleton.mp variables)

theorem before_models : GeneralWhereVersionInstall317.Models before w :=
  ⟨(GeneralNominalVersionedJournal232.initial_models context root w).mpr
    ⟨baseline_raw,point_root_holds _ _ root_point w⟩,fun _ impossible => by cases impossible⟩

end Yulang.GeneralWherePhysicalOldHead319
