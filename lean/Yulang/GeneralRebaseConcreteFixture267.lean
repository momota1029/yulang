import Yulang.GeneralRebaseConcreteCorrect267
import Yulang.GeneralRebaseInstallFixture267
import Yulang.GeneralRebaseCheckedFixture266

set_option maxRecDepth 12000
set_option maxHeartbeats 4000000
namespace Yulang.GeneralRebaseConcreteFixture267
open GeneralDictionaryJournalRefinement228Source (root roles)
open GeneralDictionaryCompoundFrame238 (before effect installed)
open GeneralDictionaryCompoundSource238 (sourceRegistry registry)
open GeneralDictionaryCompoundPacket238 (plan)
open GeneralRebaseHeadProbeFixture267 (entries_exact certifiedCase certifiedCase_honest)
open GeneralRebaseSourceSurvivor267 (Boundary)
open GeneralRebaseSourceObserver267 (Probes installs installAt)
open GeneralRebaseObserverSound267 (Sound)
open GeneralRebaseConcreteEntries267 (Entry)
open GeneralRebaseSourceStrictFixture265 (owners pool first last proposed)

theorem checked : (Boundary roles).Checked sourceRegistry := ⟨rfl,GeneralDictionaryCompoundSource238.checked⟩

def probes : Probes roles :=
 ⟨fun _ => certifiedCase,fun _ _ => false,fun _ _ => true,fun _ _ => false⟩

theorem only_root (focus : GeneralSourceDictionaries.Occurrence roles)
 (generated : GeneralNominalSaturationState.Generated before.core.erased.current root focus) : focus = root := by
 induction generated with
 | root => rfl
 | child _ listed _ => cases listed
 | alias _ _ listed _ _ =>
   cases List.mem_singleton.mp listed
   rfl

theorem knows : Sound sourceRegistry before root checked probes := by
 refine ⟨GeneralDictionaryCompoundFrame238.prepared.1,?_,?_,?_,?_⟩
 · intro focus seen
   cases only_root focus seen
   exact certifiedCase_honest
 · intro focus seen
   cases only_root focus seen
   constructor
   · intro _ _ impossible; cases impossible
   · intro candidate listed _ next reg snapshot same
     change candidate ∈ GeneralRebaseHeadProbeFixture267.entries at listed
     rw [entries_exact] at listed
     cases List.mem_singleton.mp listed
     cases GeneralRebaseSourceInstall267.effect_ext next effect reg snapshot same
     exact ⟨GeneralDictionaryCompoundVersionedModel238.extended,GeneralRebaseProspectiveFixture264.residual⟩
 · intro focus candidate present
   obtain ⟨_,_,listed,_,_,_,_,_⟩ := (GeneralRebaseInstallCandidates267.scan_exact ..).mp present
   obtain ⟨_,same⟩ := (GeneralRebaseHeadProbe267.atFocus_exact ..).mp listed
   have generated := ((GeneralRebaseCandidatePrepared267.ready_exact ..).mp
     ((GeneralRebaseHeadProbe267.atFocus_exact ..).mp listed).1).1.generated
   have focusEq := (same.symm.trans (only_root _ generated)).symm
   cases focusEq
   change candidate ∈ GeneralRebaseHeadProbeFixture267.entries at listed
   rw [entries_exact] at listed
   cases List.mem_singleton.mp listed
   exact GeneralRebaseInstallFixture267.guard
 · intro _ _ _ _ impossible
   cases impossible

theorem actual_installs : installs sourceRegistry before root checked probes = [plan] := by
 have focusList : GeneralRebaseExecutableGenerated267.discover before.core.erased.current root = [root] := by decide +kernel
 have one : installAt sourceRegistry before root root checked probes = [plan] := by
   unfold installAt
   change GeneralRebaseInstallCandidates267.scan before certifiedCase (fun _ => false) (fun _ => true)
     GeneralRebaseHeadProbeFixture267.entries = [plan]
   rw [entries_exact]
   simp [GeneralRebaseInstallCandidates267.scan,GeneralRebaseSourceClassification267.verdict,
     GeneralRebaseHeadProbe267.positive,GeneralRebaseHeadProbe267.unresolved,certifiedCase,
     GeneralRebasePartialClassification267.classify,GeneralRebaseInstallCandidates267.eligible,
     GeneralRebasePickPlan267.matches_exact,GeneralRebaseInstallFixture267.history,
     GeneralRebaseNoveltyProbe267.novel,GeneralRebaseInstallFixture267.missing]
 unfold installs
 rw [focusList]
 simpa using one

theorem no_merges : GeneralRebaseMergeScan267.scan before root probes.mergeInputs = [] := by
 apply List.eq_nil_iff_forall_not_mem.mpr
 intro pair listed
 rcases pair with ⟨first,last⟩
 obtain ⟨one,two,_,noAlias⟩ := ((GeneralRebaseMergeScan267.linkedPairs_exact ..).mp
   ((GeneralRebaseMergeScan267.scan_exact ..).mp listed).1)
 cases List.mem_singleton.mp one
 cases List.mem_singleton.mp two
 exact noAlias (.refl _)

theorem actual_next :
 ∃ entry : Entry sourceRegistry root before,
 GeneralRebaseConcreteNext267.next sourceRegistry root checked (fun _ => probes) owners pool before
   GeneralDictionaryCompoundStep238.initial_reachable knows = .ok (some entry) ∧
 entry.after = installed := by
 let item : {p : GeneralNominalCenters.Plan roles // p ∈ installs sourceRegistry before root checked probes} :=
   ⟨plan,by rw [actual_installs]; exact List.mem_singleton_self _⟩
 let entry := GeneralRebaseConcreteEntries267.installEntry sourceRegistry root before checked
    GeneralDictionaryCompoundStep238.initial_reachable probes knows item
 let choices := GeneralRebaseConcreteEntries267.entries sourceRegistry root before checked
    GeneralDictionaryCompoundStep238.initial_reachable probes knows
 have listed : entry ∈ choices := List.mem_append_left _ (List.mem_map.mpr ⟨item,List.mem_attach _ _,rfl⟩)
 have one : choices.length = 1 := by
   have eq := GeneralRebaseConcreteEntries267.same_order sourceRegistry root before checked
      GeneralDictionaryCompoundStep238.initial_reachable probes knows
   unfold GeneralRebaseSourceObserver267.proposals at eq
   rw [actual_installs,no_merges] at eq
   have count := congrArg List.length eq
   simpa only [choices,List.length_map,List.map_nil,List.append_nil,List.map_cons,List.length_cons,List.length_nil,Nat.zero_add] using count
 have uniq : choices = [entry] := by
   cases h : choices with
   | nil => simp [h] at one
   | cons first rest =>
     have empty : rest = [] := by simpa [h] using one
     subst rest
     have same := List.mem_singleton.mp (h ▸ listed)
     cases same
     rfl
 have own : entry.facts = proposed := rfl
 have same : entry.after = installed := by
   unfold entry GeneralRebaseConcreteEntries267.installEntry
   apply congrArg (GeneralNominalVersionedInstall232.install before)
   exact GeneralRebaseSourceInstall267.effect_ext _ effect rfl rfl rfl
 refine ⟨entry,?_,same⟩
 change GeneralRebaseConcreteScan267.scan owners pool before choices = _
 rw [uniq,GeneralRebaseConcreteScan267.scan,own,GeneralRebaseCheckedFixture266.first_checked]

end Yulang.GeneralRebaseConcreteFixture267
