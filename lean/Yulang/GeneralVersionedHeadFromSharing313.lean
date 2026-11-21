import Yulang.GeneralVersionedSharingBinderTable313
import Yulang.GeneralVersionedSelectedJointHead312
import Yulang.GeneralVersionedSemanticPeer312

set_option backward.isDefEq.respectTransparency false
/-! Produce the initial diagnostic head witness from a shared, actual set
of origins. No installed dictionary is used. Checked equations on the
protected targets are enough; ledger reuse is one way to obtain them. -/
namespace Yulang.GeneralVersionedHeadFromSharing313
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedDiagnostic232 (HeadEquations)
open GeneralNominalVersionedPlans231 (HeadModels)
open GeneralNominalVersionedModelSupport237 (Support)
open GeneralNominalVersionedAggregateLedger236 (packetEntries)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralVersionedSemanticPeer312 (complete protectedPool)
open GeneralVersionedSharingBinderRows313 (Tests rows schema_after)
open GeneralVersionedSharingBinderTable313 (PrivateAgrees)
open GeneralVersionedAliasHeadWrites312 (pool)
open GeneralNominalCenteredModelExtension (originSource)
open GeneralNominalCenteredFrame179 (Agree)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalOriginTerms (Same)
open GeneralNominalRecursiveInspection (Origin)

def origins (p : Plan roles) : List Nat :=
  p.headSchema.tests.map (fun test => originSource test.1) ++
    p.headSchema.variables.map (fun use => originSource use.origin)

def supportWithOrigins (p : Plan roles) (names : List Nat) : List Nat := names ++ origins p

theorem same_iff {m n : Assignment} (a b : Origin)
    (left : m (originSource a) = n (originSource a)) (right : m (originSource b) = n (originSource b)) :
    Same m a b ↔ Same n a b := by
  unfold Same
  simp only [GeneralNominalCenteredFrame179.observes_iff _ left,
    GeneralNominalCenteredFrame179.observes_iff _ right]

theorem origin_agree (p : Plan roles) {m n : Assignment}
    (same : Agree (origins p) m n) :
    (Tests p m ↔ Tests p n) ∧
    (GeneralDictionaryHeadSharing220.Holds p m ↔ GeneralDictionaryHeadSharing220.Holds p n) := by
  constructor
  · unfold Tests
    apply forall_congr'
    intro test
    apply forall_congr'
    intro member
    exact GeneralNominalCenteredFrame179.head_iff test.1 test.2
      (same _ (List.mem_append_left _ (List.mem_map.mpr ⟨test,member,rfl⟩)))
  · rw [GeneralDictionaryHeadSharing220.holds_iff,GeneralDictionaryHeadSharing220.holds_iff]
    apply forall_congr'
    intro a
    apply forall_congr'
    intro one
    apply forall_congr'
    intro b
    apply forall_congr'
    intro two
    apply forall_congr'
    intro _
    exact same_iff _ _
      (same _ (List.mem_append_right _ (List.mem_map.mpr ⟨a,one,rfl⟩)))
      (same _ (List.mem_append_right _ (List.mem_map.mpr ⟨b,two,rfl⟩)))

theorem materialize {s : State roles} {p : Plan roles}
    (frame : Frame (Compiled registry) s.core focus key p)
    (sufficient : Support s names) (m : Assignment) (valid : Models s m)
    (head : HeadModels p.packet m) (tests : Tests p m)
    (sharing : GeneralDictionaryHeadSharing220.Holds p m)
    (privateBinder : PrivateAgrees p names m sharing) :
    ∃ n, Models s n ∧ HeadModels p.packet n ∧ HeadEquations p n := by
  obtain ⟨coherent,fixed⟩ := GeneralVersionedSharingBinderTable313.table frame names m valid sharing tests privateBinder
  let n := GeneralFiniteTypedWrites312.applyWrites (rows p m sharing) (pool p names) m
  have preserves := GeneralFiniteTypedWrites312.preserved (rows p m sharing) (pool p names) m
  have live := (sufficient m n (fun id h => preserves id (by simp [pool,h]))).mp valid
  have rawOld : GeneralNominalState.Models p.packet.context.state m := by rw [frame.context_eq]; exact valid.1.1
  have rawNew : GeneralNominalState.Models p.packet.context.state n := by rw [frame.context_eq]; exact live.1.1
  have headNext := (GeneralNominalVersionedResidualFrame237.head_models_iff p.packet rawOld rawNew
    (fun id h => preserves id (by simp [pool,h]))).mp head
  exact ⟨n,live,headNext,GeneralVersionedSelectedJointHead312.head_of_schema frame live headNext
    (schema_after p m names sharing tests coherent fixed)⟩

def Equations (p : Plan roles) (names : List Nat) (m : Assignment) : Prop :=
  ∀ entry ∈ packetEntries p.packet, entry.1 ∈ protectedPool p.packet (supportWithOrigins p names) →
    PresenceNormalForm.All CommonNominalFullCarrier.model m (GeneralNominalAllocation.equations entry.1 entry.2)

def BinderAfter (p : Plan roles) (names : List Nat) (m : Assignment) : Prop :=
  let n := complete p.packet (supportWithOrigins p names) m
  ∀ sharing : GeneralDictionaryHeadSharing220.Holds p n, PrivateAgrees p names n sharing

theorem of_tests_and_sharing {s : State roles} {p : Plan roles}
    (frame : Frame (Compiled registry) s.core focus key p)
    (sufficient : Support s names) (m : Assignment) (valid : Models s m)
    (tests : Tests p m) (sharing : GeneralDictionaryHeadSharing220.Holds p m)
    (eqns : Equations p names m) (binders : BinderAfter p names m) :
    ∃ n, Models s n ∧ HeadModels p.packet n ∧ HeadEquations p n := by
  have enlarged : Support s (supportWithOrigins p names) := GeneralNominalVersionedModelSupport237.weaken sufficient
    (fun _ h => List.mem_append_left _ h)
  have locate := frame.occurrence_eq.symm ▸ frame.located
  have raw := (GeneralVersionedAliasReport312.from_tests p frame.context_eq frame.center_recorded locate m valid tests
    (GeneralDictionaryHeadSharing220.agreement_of_holds p m sharing)).2
  let n := complete p.packet (supportWithOrigins p names) m
  obtain ⟨more,head⟩ := GeneralVersionedSemanticPeer312.full_head frame.context_eq enlarged valid raw eqns
  have same : Agree (origins p) m n := by
    intro id member
    exact (GeneralNominalSelectiveEquationRealization236.preserves _ _ id
      (List.mem_append_left _ (List.mem_append_right _ member))).symm
  obtain ⟨testsIff,sharedIff⟩ := origin_agree p same
  exact materialize frame sufficient n more head (testsIff.mp tests) (sharedIff.mp sharing) (binders _)

theorem selected_sharing {registry : Registry} {s : State roles} {root focus : Occurrence roles} {p : Plan roles}
    (checked : (boundary roles).Checked registry)
    (path : B4TargetV8.Reachable (boundary roles) registry root s)
    (selected : Local registry s focus (.selected key children))
    (frame : Frame (Compiled registry) s.core focus key p)
    (inhabited : ∃ m, Models s m) :
    ∃ m, Models s m ∧ GeneralDictionaryHeadSharing220.Holds p m := by
  obtain ⟨m,valid,other,otherFrame,sharing⟩ := GeneralNominalVersionedMixedSelectedWitness236.sharing path selected inhabited
  have eq := GeneralVersionedCurrentFrame312.frame_exact checked path frame otherFrame
  exact ⟨m,valid,eq.symm ▸ sharing⟩

theorem selected_head {registry : Registry} {s : State roles} {root focus : Occurrence roles} {p : Plan roles}
    (checked : (boundary roles).Checked registry)
    (path : B4TargetV8.Reachable (boundary roles) registry root s)
    (selected : Local registry s focus (.selected key children))
    (frame : Frame (Compiled registry) s.core focus key p)
    (inhabited : ∃ m, Models s m) (sufficient : Support s names)
    (certify : ∀ m, Models s m → GeneralDictionaryHeadSharing220.Holds p m →
      Tests p m ∧ Equations p names m ∧ BinderAfter p names m) :
    ∃ n, Models s n ∧ HeadEquations p n := by
  obtain ⟨m,valid,sharing⟩ := selected_sharing checked path selected frame inhabited
  obtain ⟨tests,eqns,binders⟩ := certify m valid sharing
  obtain ⟨n,live,_,head⟩ := of_tests_and_sharing frame sufficient m valid tests sharing eqns binders
  exact ⟨n,live,head⟩

end Yulang.GeneralVersionedHeadFromSharing313
