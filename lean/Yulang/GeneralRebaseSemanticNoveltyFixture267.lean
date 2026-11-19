import Yulang.GeneralRebaseInstallCoverage267
import Yulang.GeneralNominalVersionedDiagnosticLaws232

set_option maxRecDepth 12000
set_option maxHeartbeats 3000000
namespace Yulang.GeneralRebaseSemanticNoveltyFixture267
open GeneralDictionaryJournalRefinement228Source (root roles context)
open GeneralDictionaryOptionalInitial229 (registry sourceRegistry start)
open GeneralDictionaryOptionalInstall229 (plan packet)
open GeneralDictionaryVersionedInitialFrame233 (before effect installed frame unique children_empty installation_models)
open GeneralDictionaryVersionedInitialModel233 (extended initial_model)
open GeneralRebaseSourceSurvivor267 (Boundary declChecked)
open GeneralRebaseHeadProbe267 (atFocus Honest observation)
open GeneralRebaseInstallCandidates267 (scan Probes)

theorem checked : (Boundary roles).Checked sourceRegistry :=
 ⟨rfl,GeneralDictionaryOptionalInitial229.checked⟩

theorem initial_reachable : B4TargetV8.Reachable (Boundary roles) sourceRegistry root before :=
 ⟨before,⟨start,GeneralDictionaryOptionalInitial229.initial,rfl⟩,.refl⟩

noncomputable def entries := atFocus registry before root root (declChecked checked)

def headProbe (_ : GeneralNominalCenters.Plan roles) : Option Bool := some true

def modelProbe (_ : GeneralNominalCenters.Plan roles) : Bool := true

theorem entry_count : entries.length = 1 := by decide +kernel

theorem entries_exact : entries = [plan] := by
 have actual := GeneralRebaseCandidatePrepared267.includes_real_install registry before root (declChecked checked) effect
   .root (GeneralNominalVersionedMixedKernel234.of_old_installable GeneralDictionaryVersionedInitialStep233.installable)
 have member : plan ∈ entries := (GeneralRebaseHeadProbe267.atFocus_exact ..).mpr ⟨actual,rfl⟩
 have one := entry_count
 cases h : entries with
 | nil => simp [h] at one
 | cons candidate rest =>
   have noRest : rest = [] := by simpa [h] using one
   subst rest
   obtain equal := List.mem_singleton.mp (h ▸ member)
   cases equal
   rfl

theorem honest : Honest headProbe entries := by
 constructor
 · intro x present _
   rw [entries_exact] at present
   cases List.mem_singleton.mp present
   exact ⟨extended,GeneralDictionaryVersionedInitialPacket233.head_model⟩
 · intro _ _ h
   cases h

theorem probes : Probes registry before modelProbe modelProbe entries := by
 constructor
 · intro x present _
   rw [entries_exact] at present
   cases List.mem_singleton.mp present
   exact GeneralRebaseNoveltyBoundary267.actual_semantic_novelty.2.1
 · intro x present _ candidate reg context same
   rw [entries_exact] at present
   cases List.mem_singleton.mp present
   cases GeneralRebaseSourceInstall267.effect_ext candidate effect reg context same
   exact ⟨extended,(GeneralNominalVersionedMixedMaterialization237.installation_models_iff
     checked initial_reachable rfl rfl).mp installation_models⟩

theorem actual_scan :
 scan before headProbe modelProbe modelProbe entries = [plan] := by
 have ready : GeneralRebaseInstallCandidates267.eligible before headProbe modelProbe modelProbe (observation plan) plan = true := by
   have matched := (GeneralRebasePickPlan267.matches_exact headProbe (observation plan) plan).mpr ⟨rfl,rfl⟩
   have equality : GeneralRebaseNoveltyProbe267.novel before modelProbe plan = true :=
     (GeneralRebaseNoveltyProbe267.flags ..).mpr (Or.inr rfl)
   simp only [GeneralRebaseInstallCandidates267.eligible,matched,equality,modelProbe,Bool.true_and,Bool.and_true]
   rfl
 rw [entries_exact]
 simp [scan,GeneralRebaseSourceClassification267.verdict,GeneralRebaseHeadProbe267.positive,
   GeneralRebaseHeadProbe267.unresolved,headProbe,GeneralRebasePartialClassification267.classify,ready]


theorem equal_outputs (focus : GeneralSourceDictionaries.Occurrence roles) :
 GeneralNominalCenteredHeadOutputs.EqualOutputs before.core focus extended := by
 have requested (out : GeneralSourceState.Output) (member : out ∈ GeneralNominalCenteredHeadOutputs.requests before.core focus) : out = ⟨0,4⟩ := by
   obtain ⟨site,present,_,within⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp member
   cases List.mem_singleton.mp present
   exact List.mem_singleton.mp within
 intro first one last two _
 cases requested first one
 cases requested last two
 exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩

theorem guards : GeneralRebaseSourceSelect267.Guard sourceRegistry before root plan.packet.declaration.id := by
 have compiled := GeneralNominalVersionedDiagnosticLaws232.selected_of_model
   GeneralDictionaryVersionedInitialStep233.safe unique initial_model frame
   GeneralDictionaryOptionalInstall229.ready GeneralDictionaryVersionedInitialPacket233.packet_holds
   GeneralDictionaryVersionedInitialFrame233.class_effects
   (GeneralNominalVersionedMergedConflict232.models_exclude_conflict initial_model
     (fun demand _ => equal_outputs demand) (equal_outputs root))
 obtain ⟨v7,clearSharing⟩ := B4TargetV8.selected_iff.mp compiled
 obtain ⟨v6,clearMerged⟩ := B4TargetV7.selected_iff.mp v7
 cases v6 with
 | selected safe _ output => exact ⟨safe,output,clearMerged,clearSharing⟩

/-- A real no-child update recovered by the semantic-novelty proof. The new
search finds the exact same concrete effect without a stored Plan/edge list. -/
theorem recovered_install :
 (Boundary roles).Step sourceRegistry root before installed ∧
 ∃ model, GeneralNominalVersionedJournal232.Models installed model := by
 have selected : plan ∈ scan before headProbe modelProbe modelProbe entries := by
   rw [actual_scan]; exact List.mem_singleton_self _
 obtain ⟨derived,reg,atState,same,step,model⟩ :=
   GeneralRebaseInstallCandidates267.source_step sourceRegistry before root root checked initial_reachable .root
    GeneralDictionaryVersionedInitialFrame233.prepared.1 headProbe modelProbe modelProbe honest probes plan selected guards
 cases GeneralRebaseSourceInstall267.effect_ext derived effect reg atState same
 exact ⟨step,model⟩

end Yulang.GeneralRebaseSemanticNoveltyFixture267
