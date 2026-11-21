import Yulang.GeneralWhereOriginInstall318
import Yulang.GeneralWhereOriginCheckedFixture318

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29000
set_option maxHeartbeats 26000000
namespace Yulang.GeneralWhereOriginFixtureCut318
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralLiveCompoundRegistry316 (registry sourceRegistry otherChild)
open GeneralLiveCompoundLeafInstall316 (after reachable)
open GeneralLiveCompoundPostFrames316 (rootPlan)
open GeneralLiveCompoundPostRootHead316 (frame)
open GeneralWhereVersionInstall317 (before)
open GeneralWhereOriginJoint318 (guard childGuard)
open GeneralWhereOriginReady318 (headGuard)
open GeneralWhereOriginAssemble318 (actualSources)
open GeneralWhereOriginSupport318 (journalSources)
open GeneralNominalIdentities (Origin source)
open GeneralVersionedTraceDomain313 (seed)
open GeneralVersionedHighOrigins315 (Absent raw_absent input_domain binder_domain distinct)
open GeneralVersionedEndpointPatch315 (aligned_domain schema_absent classes_absent operand_absent)
open GeneralNominalVersionedPacketFrame236 (headSources captureSources)
open GeneralNominalVersionedFrame231 (capture binder)
open GeneralNominalVersionedPlans231 (childSchema)
open GeneralWhereVersionCompiler317 (schema)
open GeneralNominalVersionedExpressionFrame236 (schemaSources equationSources)
open GeneralNominalCenteredHeadMatSchemas (Equation)
open GeneralNominalCenteredFrame179 (siteSources)

theorem legacy_cut {k : Origin} (large : 9 < k.2.2.1) :
    source (seed after) k ∉ journalSources before := by
  intro h
  change source (seed after) k ∈ GeneralNominalVersionedJournalFrame236.sources after ++ [] at h
  rw [List.append_nil] at h
  exact GeneralVersionedHighJournal315.all reachable large _ h rfl

theorem private_cut {k : Origin} (large : 9 < k.2.2.1) :
    ∀ n ∈ headSources rootPlan.packet, Absent after k n := by
  intro n found equal
  have visible : rootPlan.packet.declaration ∈ rootPlan.packet.registry.declarations := List.mem_cons_self
  rcases List.mem_append.mp found with privatePart|report
  · have rawPrivate := GeneralNominalSemanticRawFrame236.contained _ privatePart
    let pack := rootPlan.packet
    have domain (id : Nat) (item : id ∈ GeneralNominalState.sources (GeneralNominalVersionedPlans231.privateState pack)) :
        id ∈ GeneralVersionedInstallDomain313.pool pack := by
      apply GeneralNominalAllocationSupport.extend_sources _ [] _ ?_ (by intro _ no; cases no) ?_ item
      · refine GeneralNominalAllocationSupport.extend_sources pack.context.state
          (GeneralVersionedInstallDomain313.reserve pack) _ (fun _ h => List.mem_append_left _ h)
          (fun _ h => List.mem_append_right _ h) ?_
        intro atom present
        rcases List.mem_append.mp present with cross|merges
        · exact GeneralNominalAllocationSupport.cross_sources
            (GeneralVersionedInstallDomain313.extension_endpoints pack) atom cross
        · exact GeneralVersionedInstallDomain313.merge_atom pack visible atom merges
      · exact fun atom member => GeneralNominalAllocationSupport.checks_sources _ _
          (fun _ found => List.mem_append_left _ found) atom member
    rcases List.mem_append.mp (domain n rawPrivate) with old|reserve
    · rw [frame.context_eq,equal] at old
      exact raw_absent reachable large old
    · have cfg := (aligned_domain frame.context_eq).1
      rw [equal,← cfg] at reserve
      have tags := GeneralVersionedInstallDomain313.reserve_purpose rootPlan.packet reserve
      omega
  · have rawReport := GeneralNominalSemanticRawFrame236.contained _
        (GeneralNominalSemanticRawFrame236.report_sources_subset _ _ _ report)
    rw [frame.context_eq,equal] at rawReport
    exact raw_absent reachable large rawReport

theorem captures_cut {k : Origin} (large : 9 < k.2.2.1) :
    ∀ n ∈ captureSources rootPlan, Absent after k n := by
  obtain ⟨cfg,domain⟩ := aligned_domain frame.context_eq
  intro n found
  obtain ⟨name,_,inCell⟩ := List.mem_flatMap.mp found
  simp only [List.mem_cons,List.not_mem_nil,or_false] at inCell
  rcases inCell with rfl|rfl|rfl
  · exact (input_domain reachable cfg domain large name).1
  · exact (input_domain reachable cfg domain large name).2
  · exact binder_domain reachable cfg domain large name

theorem actual_cut {k : Origin} (_large : 9 < k.2.2.1) :
    ∀ n ∈ actualSources rootPlan, Absent after k n := by
  intro n found
  unfold actualSources at found
  rw [GeneralWhereVersionCase317.rows] at found
  change n ∈ [4] at found
  cases List.mem_singleton.mp found
  have high := GeneralNominalIdentities.source_above_seed (seed after) k
  change 4 < source (seed after) k at high
  omega

theorem child_cut {k : Origin} (large : 9 < k.2.2.1) :
    ∀ n ∈ childGuard rootPlan, Absent after k n := by
  intro n found
  obtain ⟨c,_,support⟩ := List.mem_flatMap.mp found
  obtain ⟨clause,listed⟩ := c
  have same := List.mem_singleton.mp listed
  subst clause
  rw [GeneralWhereVersionSemantics317.actual_child_schema] at support
  obtain ⟨row,only,within⟩ := List.mem_flatMap.mp support
  cases List.mem_singleton.mp only
  rcases List.mem_cons.mp within with rfl|reads
  · intro eq
    change source (seed after) (GeneralNominalAllocation.origin root.identity
      GeneralLiveCompoundRegistry316.declaration.id 9 otherChild.id 0) = _ at eq
    exact distinct (by omega : (9:Nat) ≠ k.2.2.1) _ eq
  · obtain ⟨read,_,rfl⟩ := List.mem_map.mp reads
    exact operand_absent reachable frame.context_eq large read.1 read.2

theorem current_guard {k : Origin} (large : 9 < k.2.2.1) :
    source (seed after) k ∉ guard before rootPlan := by
  intro found
  simp only [GeneralWhereOriginJoint318.guard,headGuard,List.mem_append] at found
  rcases found with (((((privatePart|input)|cap)|schematic)|effects)|actual)|subtree
  · exact private_cut large _ privatePart rfl
  · exact GeneralVersionedHighPacket315.registered reachable large rootPlan.input frame.center_recorded _ input rfl
  · exact captures_cut large _ cap rfl
  · exact schema_absent reachable large frame _ schematic rfl
  · exact classes_absent reachable large frame _ effects rfl
  · exact actual_cut large _ actual rfl
  · exact child_cut large _ subtree rfl

end Yulang.GeneralWhereOriginFixtureCut318
