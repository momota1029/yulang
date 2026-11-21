import Yulang.GeneralSharedNamedHeadSeparation310
import Yulang.GeneralVersionedCheckedReturn310

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27000
set_option maxHeartbeats 16500000
namespace Yulang.GeneralSharedNamedPremerge310
open GeneralSharedNamedSource310 (root compiled registry impl checked)
open GeneralSharedNamedPlan310 (loSite hiSite kids)
open GeneralSharedNamedInstall310 (after inhabited centers)
open GeneralSharedNamedLeaf310 (Side site)
open GeneralSharedNamedEvidence310 (parentPlan parent_frame parent_children parent_ready siblings_different alias_identity)
open GeneralSharedNamedMerge310 (merged)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open GeneralNominalVersionedDiagnostic232 (AdministrativeReady)
open GeneralDeclarationExamples (roles)
open GeneralNominalCenters (Site)
open GeneralSharedNamedNodes310 (Node focus)
open GeneralSharedNamedCompiler310 (decode)
open CommonRoleOutermostResolver (Tree Resolves)

theorem no_raw_or_live_cycle (d : GeneralSourceDictionaries.Occurrence roles) :
    ¬ ((GeneralNominalVersionedDiagnostic232.fields roles).RootK2 compiled after d) ∧
    ¬ ((GeneralNominalVersionedDiagnostic232.fields roles).CandidateK2 compiled after d) := by
  constructor
  · rintro (raw | (⟨i,cycle⟩ | ⟨s,_,_,i,cycle⟩))
    · obtain ⟨_,_,_,slot,_,cycle⟩ := raw
      exact GeneralRebaseDisplaySafety276.raw_acyclic after.core.erased.current.context.state rfl inhabited.1.1 slot cycle
    · exact GeneralRebaseDisplaySafety276.semantic inhabited _ cycle
    · exact GeneralRebaseDisplaySafety276.semantic inhabited _ cycle
  · rintro (raw | ⟨p,_,entry,_,cycle⟩)
    · obtain ⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ := raw
      exact GeneralRebaseDisplaySafety276.raw_acyclic after.core.erased.current.context.state rfl inhabited.1.1 visited.1 cycle
    · exact GeneralRebaseDisplaySafety276.semantic inhabited _ cycle

theorem no_merged (d : GeneralSourceDictionaries.Occurrence roles) :
    ¬ GeneralNominalVersionedMergedConflict232.MergedOutputConflict after d := by
  rintro ⟨⟨a,b,recorded,_,_⟩,_⟩
  cases recorded

theorem not_ready (side : Side) : ¬ AdministrativeReady after (site side).occurrence := by
  intro ready
  have lo : loSite ∈ after.core.sites := centers ▸ List.mem_cons_of_mem _ List.mem_cons_self
  have hi : hiSite ∈ after.core.sites := centers ▸ List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  cases side
  · exact siblings_different (alias_identity (ready.2 loSite lo rfl hiSite hi GeneralSharedNamedMerge310.same_inputs))
  · have swap : GeneralNominalCenters.SameInputs (Models after) hiSite loSite := by
      refine ⟨rfl,?_⟩
      change GeneralNominalDemandMerging.All₂ (GeneralNominalDemandMerging.Related (Models after)) (List.ofFn fun i => some (.source (hiSite.center i)))
        (List.ofFn fun i => some (.source (loSite.center i)))
      simp only [List.ofFn_succ,List.ofFn_zero]
      rw [GeneralSharedNamedPlan310.center_high,GeneralSharedNamedPlan310.center_low]
      exact .cons ⟨_,_,rfl,rfl,GeneralNominalDemandMerging.source_same _ _⟩ .nil
    exact siblings_different (alias_identity (ready.2 hiSite hi rfl loSite lo swap)).symm

theorem child_pending (side : Side) : Local registry after (site side).occurrence .pending := by
  apply GeneralNominalVersionedMixedSourceBoundary234.local_iff.mpr
  apply GeneralNominalVersionedMixedBoundary234.local_iff.mpr
  refine .ordinary ?_ (.ordinary (no_merged _) (.inspectionPending (GeneralSharedNamedLeafFrame310.known side)
    (.inr (not_ready side)) (no_raw_or_live_cycle _).1 (no_raw_or_live_cycle _).2))
  rintro ⟨_,_,_,safe,_⟩
  exact not_ready side (Classical.byContradiction (fun absent => safe.2.2.2 (.inr absent)))

theorem admin_root : AdministrativeReady after root := by
  refine ⟨⟨parentPlan.input,parent_frame.center_recorded,rfl⟩,?_⟩
  intro a one same b two equal
  rw [centers] at one two
  simp only [List.mem_cons,List.not_mem_nil,or_false] at one two
  rcases one with rfl|rfl|rfl
  · rcases two with rfl|rfl|rfl
    · exact .refl _
    · cases equal.1
    · cases equal.1
  · exact False.elim (GeneralSharedNamedLeafFrame310.invocations .low
      (congrArg GeneralSourceDictionaries.Occurrence.identity same))
  · exact False.elim (GeneralSharedNamedLeafFrame310.invocations .high
      (congrArg GeneralSourceDictionaries.Occurrence.identity same))

theorem parent_selected : Local registry after root (.selected 1 kids) := by
  have known := GeneralSharedNamedPreinstall310.known
  have safe : B4TargetV8.SafeKnown (GeneralNominalVersionedDiagnostic232.boundary roles) compiled after root := by
    refine ⟨known,(no_raw_or_live_cycle _).1,(no_raw_or_live_cycle _).2,?_⟩
    rintro (⟨_,d,visible,role,_,unprepared⟩|notAdmin)
    · cases GeneralSharedNamedPreinstall310.member_parent visible role
      exact unprepared parent_frame.prepared
    · exact notAdmin admin_root
  have survivor := GeneralNominalVersionedMixedFrameSelection235.frame_survivor parent_frame known
  have actual := parent_children ▸ survivor
  have unique : GeneralNominalVersionedCandidates231.Unique compiled after.core.erased.current.context root 1 kids := by
    refine ⟨actual,?_⟩
    intro k cs given
    have copy := given
    obtain ⟨_,decl,visible,_,identity,role,_⟩ := copy
    cases GeneralSharedNamedPreinstall310.member_parent visible role
    subst k
    exact ⟨rfl,GeneralNominalVersionedCandidates231.survivor_children_functional
      GeneralSharedNamedPreinstall310.compiled_checked given actual⟩
  apply GeneralNominalVersionedMixedSourceBoundary234.local_iff.mpr
  apply GeneralNominalVersionedMixedBoundary234.local_iff.mpr
  exact GeneralNominalVersionedDiagnosticLaws232.selected_of_model safe unique inhabited parent_frame parent_ready
    (GeneralNominalVersionedInstalledEvidence233.replay_holds inhabited)
    (GeneralNominalVersionedInstalledEvidence233.class_effects inhabited) (no_merged _)

def before : Tree := .selected 1 [.pending,.pending]

def read : GeneralPartialDiagnosticRead310.Read
  | 0 => some (.selected 1 [1,2])
  | 1 | 2 => some .pending
  | _ => none

theorem faithful : GeneralPartialDiagnosticRead310.Faithful read decode (Local registry after) := by
  intro n row hit
  match n with
  | 0 => cases Option.some.inj hit; exact parent_selected
  | 1 => cases Option.some.inj hit; exact child_pending .low
  | 2 => cases Option.some.inj hit; exact child_pending .high
  | _+3 => cases hit

theorem checked_diagnostic : GeneralPartialDiagnosticRead310.check read 2 0 before = true := rfl

theorem preserves_pending_children : Resolves (Local registry after) root before :=
  GeneralPartialDiagnosticRead310.sound read decode (Local registry after) faithful 2 0 before checked_diagnostic

theorem not_flattened :
    GeneralPartialDiagnosticRead310.check read 2 0 .rejected = false ∧
    GeneralPartialDiagnosticRead310.check read 2 0 .pending = false :=
  ⟨rfl,rfl⟩

end Yulang.GeneralSharedNamedPremerge310
