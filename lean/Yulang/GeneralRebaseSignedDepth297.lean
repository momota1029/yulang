import Yulang.GeneralRebasePriorWitness297
import Yulang.GeneralRebaseDepthMinimal285

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 22000
set_option maxHeartbeats 8000000
namespace Yulang.GeneralRebaseSignedDepth297
open GeneralDictionaryOutputDepth252 (sourceRegistry roles model initial reachable root plan source_checked)
open GeneralDictionaryOutputDepthInstall252 (effect smallModel small_initial installed installed_model step installable)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseSourceSurvivor267 (Boundary Encoded declChecked)
open GeneralRebaseSourceQuestions297 (entries Question questions)
open GeneralRebasePriorWitness297 (Prior values vote)
open GeneralRebaseSignedModels297 (Sign Conditions Test)
open GeneralRebaseSignedSupport297 (Agree candidateReads)
open GeneralRebaseFiniteWitnessTable297 (Covers)

theorem checked : (Boundary roles).Checked sourceRegistry := ⟨rfl,source_checked⟩

theorem listed : plan ∈ entries sourceRegistry initial root checked := by
  have here := GeneralRebaseCandidatePrepared267.includes_real_install
    (Encoded sourceRegistry) initial root (declChecked checked) effect .root installable
  exact GeneralRebaseSourceQuestions297.of_focus sourceRegistry initial root root checked .root plan
    ((GeneralRebaseHeadProbe267.atFocus_exact ..).mpr ⟨here,rfl⟩)

theorem positive : Test initial plan .pass model :=
  (GeneralRebaseSignedModels297.accepted_exact (e := effect) checked reachable rfl rfl model).mpr installed_model

theorem negative : Test initial plan .reject smallModel :=
  (GeneralRebaseSignedModels297.rejected_exact (e := effect) checked reachable rfl rfl smallModel).mpr
    ⟨small_initial,GeneralRebaseDepthPublic285.no_raw_substitute.2.2.2⟩

theorem same_public_types :
    GeneralRebaseDepthPublic285.project model = GeneralRebaseDepthPublic285.project smallModel :=
  GeneralRebaseDepthPublic285.no_raw_substitute.1

theorem all_rows_same : ∀ n, (model n).2 = (smallModel n).2 :=
  GeneralRebaseDepthPublic285.no_raw_substitute.2.1

theorem output_only_rejection : Test initial plan .reject (GeneralRebaseDepthMinimal285.damage 3) := by
  let altered := GeneralRebaseDepthMinimal285.damage 3
  apply (GeneralRebaseSignedModels297.rejected_exact (e := effect) checked reachable rfl rfl altered).mpr
  refine ⟨?_,GeneralRebaseDepthMinimal285.breaks_raw 3 (by decide)⟩
  apply (GeneralNominalVersionedJournal232.initial_models ..).mpr
  refine ⟨?_,fun _ => ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩⟩
  have good := GeneralDictionaryOutputDepth252.source_model
  apply (GeneralRebaseDepthGroundModels285.source_inputs altered).mpr
  have same (n : Nat) (notOutput : n ≠ 3) : (altered n).1 = (model n).1 :=
    GeneralRebaseDepthMinimal285.literal_agreement 3 n notOutput
  unfold GeneralRebaseDepthGroundModels285.InitialTypeCheck
  rw [same 0 (by decide),same 1 (by decide),same 2 (by decide)]
  exact (GeneralRebaseDepthGroundModels285.source_inputs model).mp good

theorem output_must_be_observed :
    3 ∈ candidateReads initial plan := by
  apply Classical.byContradiction
  intro omitted
  have agreement : Agree (candidateReads initial plan) model (GeneralRebaseDepthMinimal285.damage 3) :=
    ⟨fun n asked => (GeneralRebaseDepthMinimal285.literal_agreement 3 n
      (fun eq => omitted (eq ▸ asked))).symm,fun _ => rfl⟩
  exact output_only_rejection.2
    ((GeneralRebaseSignedSupport297.conditions_iff initial plan model _ agreement).mp positive.2)

def acceptRow : Prior initial := ⟨model,positive.1⟩
def rejectRow : Prior initial := ⟨smallModel,negative.1⟩
def pool := [acceptRow,rejectRow]

def nested (m : Assignment) : Bool :=
  match (m 3).1 with
  | .nominal .. => true
  | _ => false

def check (_ : GeneralNominalCenters.Plan roles) (a : Prior initial) : Bool := nested a.val

theorem bit_checked (a : Prior initial) (row : a ∈ pool) :
    check plan a = true ↔ Conditions initial plan a.val := by
  simp only [pool,List.mem_cons,List.not_mem_nil,or_false] at row
  rcases row with rfl | rfl
  · exact ⟨fun _ => positive.2,fun _ => rfl⟩
  · constructor
    · intro impossible; cases impossible
    · intro yes; exact False.elim (negative.2 yes)

theorem pool_covers : Covers (GeneralRebaseSourceQuestions297.holds initial)
    (questions [plan]) (values pool) := by
  rintro ⟨p,sign⟩ found _
  have eq : p = plan := List.mem_singleton.mp ((GeneralRebaseSourceQuestions297.question_exact [plan] p sign).mp found)
  subst p
  cases sign
  · exact ⟨model,List.mem_map_of_mem (List.mem_cons_self ..),positive⟩
  · exact ⟨smallModel,List.mem_map_of_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..)),negative⟩

theorem exact_both (sign : Sign) :
    vote pool check plan sign = true ↔ ∃ m, Test initial plan sign m :=
  GeneralRebasePriorWitness297.vote_exact pool_covers check plan (by simp) bit_checked sign

theorem computes_both : vote pool check plan .pass = true ∧
    vote pool check plan .reject = true := ⟨rfl,rfl⟩

theorem reject_only_is_incomplete (cert : Covers (GeneralRebaseSourceQuestions297.holds initial)
    (questions [plan]) (values [rejectRow])) : False := by
  have q := (GeneralRebaseSourceQuestions297.question_exact [plan] plan .pass).mpr (List.mem_cons_self ..)
  obtain ⟨m,listed,held⟩ := cert (plan,.pass) q ⟨model,positive⟩
  have eq : m = smallModel := List.mem_singleton.mp listed
  exact negative.2 (eq ▸ held.2)

/-- Published prior-coordinate and row observation cannot test the signs:
two real prior assignments agree there and disagree about the actual plan. -/
theorem public_only_impossible (evaluate : GeneralRebaseDepthPublic285.SourceTypes → (Nat → Common.Row) → Bool)
    (recovers : ∀ m, Models initial m →
      (evaluate (GeneralRebaseDepthPublic285.project m) (fun n => (m n).2) = true ↔ Conditions initial plan m)) : False := by
  have eqRows : (fun n => (model n).2) = fun n => (smallModel n).2 := funext all_rows_same
  have yes := (recovers model positive.1).mpr positive.2
  rw [same_public_types,eqRows] at yes
  exact negative.2 ((recovers smallModel negative.1).mp yes)

end Yulang.GeneralRebaseSignedDepth297
