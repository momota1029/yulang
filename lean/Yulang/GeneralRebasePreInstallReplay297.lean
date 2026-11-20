import Yulang.GeneralRebaseSignedRefresh297
import Yulang.GeneralRebaseRawDepthReplay297

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 24000
set_option maxHeartbeats 10000000
namespace Yulang.GeneralRebasePreInstallReplay297
open GeneralDictionaryOutputDepth252 (roles sourceRegistry registry plan root initial snapshot context model)
open GeneralDictionaryOutputDepthInstall252 (smallModel)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedMixedObservations233 (Refresh CacheSound refresh_models)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalState (Known sources)
open GeneralRebaseScalarSnapshot271 (enrich)
open GeneralRebaseSignedRefresh297 (moved preserves_test)
open GeneralRebaseSignedModels297 (Sign Test)

def target := GeneralRebaseScalarSnapshot271.context context

theorem kept (id : Nat) : Known snapshot id → Known target.state id := by
  rintro ⟨slot,equal,graph | nominal⟩
  · change snapshot.view.graph slot ≠ .unresolved at graph
    exact False.elim (graph rfl)
  · exact ⟨slot,equal,Or.inr nominal⟩

def refines : GeneralNominalRefinements.Refines snapshot target.state where
  base := (GeneralNominalRefinements.refl snapshot).base
  heads := (GeneralNominalRefinements.refl snapshot).heads
  nominals := (GeneralNominalRefinements.refl snapshot).nominals
  ordinary := fun _ h => h
  known := kept
  reserved := fun _ h => h
  allocated := fun _ h => h
  seed := rfl
  constructors := rfl

theorem sound_cache : CacheSound initial target.state := by
  intro observation recorded
  exact ⟨[],[],.source,.source,fun m _ supported =>
    GeneralCanonicalObservations.recorded_sound target.state m
      (show GeneralNominalState.Models target.state m from supported.1) recorded⟩

def cert : Refresh initial target where
  refines := refines
  interpretation := rfl
  support := fun _ held => held
  constraints := fun _ held => ⟨held.1.1.1,held.1.1.2.2⟩
  cache := sound_cache

def after := refresh initial target
def candidate := moved (p := plan) cert rfl

theorem zero_old : ¬ Known snapshot 0 := by
  rintro ⟨slot,eq,head | ⟨d,recorded⟩⟩
  · exact head rfl
  · change slot.val = 0 at eq
    have eq' : slot = (0 : Fin 4) := Fin.ext eq
    subst slot
    cases recorded

theorem zero_new : Known target.state 0 := ⟨(0 : Fin 4),rfl,Or.inl (by decide +kernel)⟩

theorem zero_source : 0 ∈ sources snapshot := by
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_append_left
  exact List.mem_ofFn.mpr ⟨(0 : Fin 4),rfl⟩

theorem actual_before_install : Step registry root initial after :=
  ⟨root,.root,.refresh root target cert 0 zero_source zero_old zero_new⟩

theorem different : after ≠ initial := by
  intro same
  have found : Known after.core.erased.current.context.state 0 := zero_new
  rw [same] at found
  exact zero_old found

theorem seen : GeneralRebaseRetarget275.Observed plan := by
  unfold GeneralRebaseRetarget275.Observed
  change GeneralNominalRefinementTrace197.ObservedMany snapshot
    [GeneralNominalInspection.translate snapshot.constructors context.interpretation (.var 0)]
    [((2 : Fin 4),(2 : Fin 4))]
  rw [GeneralNominalInspection.translate.eq_1]
  exact .cons .variables .nil

theorem all_tests (sign : Sign) (m : Assignment) :
    Test after candidate sign m ↔ Test initial plan sign m :=
  preserves_test cert rfl seen sign m

theorem signs_preserved :
    Test after candidate .pass model ∧ Test after candidate .reject smallModel :=
  ⟨(all_tests .pass model).mpr GeneralRebaseSignedDepth297.positive,
    (all_tests .reject smallModel).mpr GeneralRebaseSignedDepth297.negative⟩

theorem source_reachable :
    B4TargetV8.Reachable (GeneralRebaseSourceSurvivor267.Boundary roles) sourceRegistry root after :=
  ⟨initial,GeneralDictionaryOutputDepth252.initial_source,.tail .refl actual_before_install⟩

theorem raw_observation_not_determined_by_tests :
    (∀ sign m, Test after candidate sign m ↔ Test initial plan sign m) ∧
      ¬ Known initial.core.erased.current.context.state 0 ∧ Known after.core.erased.current.context.state 0 :=
  ⟨all_tests,zero_old,zero_new⟩

theorem listed_after (p : GeneralNominalCenters.Plan roles) :
    p ∈ GeneralRebaseSourceQuestions297.entries sourceRegistry after root GeneralRebaseSignedDepth297.checked ↔
      p = candidate := by
  have certain : candidate ∈ GeneralRebaseSourceQuestions297.entries sourceRegistry after root GeneralRebaseSignedDepth297.checked := by
    let ck := GeneralRebaseSourceSurvivor267.declChecked GeneralRebaseSignedDepth297.checked
    have shell : GeneralRebaseCandidatePlan267.Shell registry after root candidate :=
      ⟨rfl,rfl,.root,List.mem_cons_self ..,List.mem_cons_self ..,List.mem_cons_self ..,rfl,
        by decide +kernel⟩
    have ready : candidate ∈ GeneralRebaseCandidatePrepared267.readyPlans registry after root ck :=
      (GeneralRebaseCandidatePrepared267.ready_exact ..).mpr
        ⟨shell,(GeneralRebaseCandidateChecks267.allKnown_exact ..).mp (by decide +kernel),
          by decide +kernel⟩
    exact GeneralRebaseSourceQuestions297.of_focus sourceRegistry after root root
      GeneralRebaseSignedDepth297.checked .root candidate ((GeneralRebaseHeadProbe267.atFocus_exact ..).mpr ⟨ready,rfl⟩)
  have count : (GeneralRebaseSourceQuestions297.entries sourceRegistry after root GeneralRebaseSignedDepth297.checked).length = 1 := by
    decide +kernel
  generalize eq : GeneralRebaseSourceQuestions297.entries sourceRegistry after root GeneralRebaseSignedDepth297.checked = ps at certain count ⊢
  cases ps with
  | nil => cases count
  | cons first rest =>
    cases rest with
    | nil => exact ⟨fun x => (List.mem_singleton.mp x).trans (List.mem_singleton.mp certain).symm,
        fun same => same.symm ▸ certain⟩
    | cons second rest => simp at count

abbrev xs := GeneralRebasePriorWitness297.values GeneralRebaseSignedDepth297.pool
abbrev entries := GeneralRebaseSourceQuestions297.entries sourceRegistry after root GeneralRebaseSignedDepth297.checked

theorem retained_table :
    GeneralRebaseSourceQuestions297.Checked after entries xs (fun _ => true)
      (fun _ a => GeneralRebaseSignedDepth297.nested a) := by
  have earlier := GeneralRebaseDepthCompiler297.all_models_checked
  refine ⟨fun a inside => ((earlier.old a inside).trans (refresh_models cert).symm),?_⟩
  intro p listed a inside
  cases (listed_after p).mp listed
  have old := (earlier.old a inside).mp rfl
  exact (earlier.test plan (List.mem_cons_self ..) a inside).trans
    (GeneralRebaseSignedRefresh297.candidate_exact cert rfl seen a old).symm

theorem retained_coverage :
    GeneralRebaseFiniteWitnessTable297.Covers (GeneralRebaseSourceQuestions297.holds after)
      (GeneralRebaseSourceQuestions297.questions entries) xs := by
  rintro ⟨p,sg⟩ found yes
  have pIn := (GeneralRebaseSourceQuestions297.question_exact entries p sg).mp found
  cases (listed_after p).mp pIn
  have prior := GeneralRebaseSignedDepth297.pool_covers (plan,sg)
    ((GeneralRebaseSourceQuestions297.question_exact [plan] plan sg).mpr (List.mem_cons_self ..))
  exact GeneralRebaseSignedRefresh297.preserves_covers cert rfl seen xs sg prior yes

theorem retained_answers (sg : Sign) :
    GeneralRebaseFiniteWitnessTable297.hit xs
      (GeneralRebaseSourceQuestions297.signed (fun _ => true) (fun _ a => GeneralRebaseSignedDepth297.nested a))
      (candidate,sg) = true := by
  apply (GeneralRebaseSourceQuestions297.exact retained_coverage retained_table candidate ((listed_after candidate).mpr rfl) sg).mpr
  cases sg
  · exact ⟨model,signs_preserved.1⟩
  · exact ⟨smallModel,signs_preserved.2⟩

end Yulang.GeneralRebasePreInstallReplay297
