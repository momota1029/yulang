import Yulang.GeneralRebaseSignedDepth297
import Yulang.GeneralRebaseOutputDepthSuccessor271

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 22000
set_option maxHeartbeats 9000000
namespace Yulang.GeneralRebaseDepthCompiler297
open GeneralDictionaryOutputDepth252 (sourceRegistry roles model initial reachable root plan source_checked declaration)
open GeneralDictionaryOutputDepthInstall252 (effect smallModel installed step installable)
open GeneralRebaseSignedDepth297 (checked pool exact_both)
open GeneralRebaseSourceSurvivor267 (Boundary Encoded declChecked)
open GeneralRebaseHeadProbe267 (atFocus Honest)
open GeneralRebaseSourceObserver267 (Probes installAt)
open GeneralRebaseSourceQuestions297 (signed)
open GeneralRebaseSignedObserver297 (withModels)
open GeneralRebaseFiniteWitnessTable297 (hit)
open GeneralRebasePriorWitness297 (values vote)
open GeneralRebaseLiveProjection264 (project)
open GeneralRebaseOutputDepthSuccessor271 (owner output projected_install initial_view)
open GeneralRebaseSignedModels297 (Sign Conditions Test)

def base : Probes roles := ⟨fun _ _ => some true,fun _ _ => false,fun _ _ => false,fun _ _ => false⟩

def compiled : Probes roles :=
  withModels base (values pool) (fun _ => true) (fun _ a => GeneralRebaseSignedDepth297.nested a)

theorem votes_agree (sign : Sign) :
    hit (values pool) (signed (fun _ => true) (fun _ a => GeneralRebaseSignedDepth297.nested a)) (plan,sign) =
      vote pool GeneralRebaseSignedDepth297.check plan sign := by cases sign <;> rfl

private theorem singleton_of_length_and_member {xs : List α} {a : α}
    (len : xs.length = 1) (mem : a ∈ xs) : xs = [a] := by
  cases xs with
  | nil => contradiction
  | cons b tail =>
    cases tail with
    | nil => exact congrArg (fun c => [c]) (List.mem_singleton.mp mem).symm
    | cons c tail => simp at len

theorem root_entries : atFocus (Encoded sourceRegistry) initial root root (declChecked checked) = [plan] := by
  apply singleton_of_length_and_member
  · decide +kernel
  · apply (GeneralRebaseHeadProbe267.atFocus_exact ..).mpr
    exact ⟨GeneralRebaseCandidatePrepared267.includes_real_install
      (Encoded sourceRegistry) initial root (declChecked checked) effect .root installable,rfl⟩

theorem entries : GeneralRebaseSourceQuestions297.entries sourceRegistry initial root checked = [plan] := by
  exact singleton_of_length_and_member (by decide +kernel) GeneralRebaseSignedDepth297.listed

theorem all_models_checked :
    GeneralRebaseSourceQuestions297.Checked initial [plan] (values pool) (fun _ => true)
      (fun _ a => GeneralRebaseSignedDepth297.nested a) := by
  refine ⟨fun a listed => ⟨fun _ => GeneralRebasePriorWitness297.prior_exact pool a listed,fun _ => rfl⟩,?_⟩
  intro p inPlan a listed
  have eq := List.mem_singleton.mp inPlan
  subst p
  obtain ⟨a,mem,rfl⟩ := List.mem_map.mp listed
  exact GeneralRebaseSignedDepth297.bit_checked a mem

theorem head_condition : GeneralRebaseCandidatePrepared267.headCondition plan :=
  ⟨_,GeneralDictionaryOutputDepth252.head_model⟩

theorem scan_root : installAt sourceRegistry initial root root checked compiled = [plan] := by
  apply singleton_of_length_and_member
  · decide +kernel
  · unfold installAt
    apply GeneralRebaseInstallCoverage267.all_real_installs sourceRegistry initial root checked reachable effect .root
      installable GeneralDictionaryOutputDepthInstall252.novel
    · change Honest (compiled.head root) (atFocus (Encoded sourceRegistry) initial root root (declChecked checked))
      rw [root_entries]
      refine ⟨?_,?_⟩
      · intro p listed _
        have eq := List.mem_singleton.mp listed
        subst p
        exact head_condition
      · intro p _ no
        cases no
    · intro p _ none
      cases none
    · have coverage := GeneralRebaseSignedDepth297.pool_covers
      have compiledCoverage : GeneralRebaseFiniteWitnessTable297.Covers
          (GeneralRebaseSourceQuestions297.holds initial)
          (GeneralRebaseSourceQuestions297.questions
            (GeneralRebaseSourceQuestions297.entries sourceRegistry initial root checked)) (values pool) :=
        entries.symm ▸ coverage
      have evidence : GeneralRebaseSourceQuestions297.Checked initial
          (GeneralRebaseSourceQuestions297.entries sourceRegistry initial root checked) (values pool)
          (fun _ => true) (fun _ a => GeneralRebaseSignedDepth297.nested a) :=
        entries.symm ▸ all_models_checked
      exact GeneralRebaseSignedObserver297.complete_guards (base := base) reachable compiledCoverage evidence root .root

theorem no_structural_novelty :
    installAt sourceRegistry initial root root checked
      ({compiled with novelty := fun _ _ => false} : Probes roles) = [] :=
  List.eq_nil_of_length_eq_zero (by decide +kernel)

theorem no_joint :
    installAt sourceRegistry initial root root checked
      ({compiled with joint := fun _ _ => false} : Probes roles) = [] :=
  List.eq_nil_of_length_eq_zero (by decide +kernel)

theorem proposals_exact :
    GeneralRebaseSourceObserver267.proposals sourceRegistry initial root checked compiled =
      [GeneralRebaseMultiSelection263.proposal initial.core (GeneralRebaseMultiSelection263.ofPlan plan)] := by
  unfold GeneralRebaseSourceObserver267.proposals GeneralRebaseSourceObserver267.installs
  have focus : GeneralRebaseExecutableGenerated267.discover initial.core.erased.current root = [root] :=
    singleton_of_length_and_member (by decide +kernel) ((GeneralRebaseExecutableGenerated267.discover_exact ..).mpr .root)
  have noPairs : GeneralRebaseMergeScan267.linkedPairs initial root = [] := List.eq_nil_of_length_eq_zero (by decide +kernel)
  simp only [focus,List.flatMap_cons,List.flatMap_nil,List.append_nil,scan_root,List.map_cons,List.map_nil,
    GeneralRebaseMergeScan267.scan,noPairs,List.filter_nil]

theorem same_real_successor :
    ∃ p ∈ GeneralRebaseSourceObserver267.proposals sourceRegistry initial root checked compiled,
      (Boundary roles).Step sourceRegistry root initial installed ∧
      GeneralRebaseStep258.write (project [owner] [output] initial) p = project [owner] [output] installed := by
  refine ⟨_,by rw [proposals_exact]; exact List.mem_cons_self ..,step,?_⟩
  exact (GeneralRebaseSourceInstallProjection264.project_install_current sourceRegistry checked root initial reachable
      effect installable [owner] [output]).symm

end Yulang.GeneralRebaseDepthCompiler297
