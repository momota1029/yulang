import Yulang.GeneralMixedFullControlFinish306
import Yulang.GeneralMixedObserverNotRaw305
import Yulang.GeneralRebaseDepthPreEvidence286

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 30000
set_option maxHeartbeats 13000000
namespace Yulang.GeneralMixedFullControlObserver306
open GeneralDictionaryOutputDepth252 (roles initial registry root sourceRegistry model output_valid)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralRebaseDepthPathRank285 (ActualPath)
open GeneralRebaseDepthPhase286 (Pre Post)
open GeneralRebaseDepthPrePlan286 (packet_holds example_check)
open GeneralNominalVersionedMixedSourceBoundary234 (Local)
open GeneralNominalVersionedEvidence231 (Evidence)
open GeneralMixedReindexOutputCompiler305 (bits complete actual_run)
open GeneralMixedDiagnosticHead304 (boundary8)
open GeneralRebaseDiagnosticData268 (Valid)
open GeneralRebaseDiagnosticV8268 (run)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
open GeneralMixedFullControlCode306 (code marker)
open GeneralRebaseDepthGroundModels285 (FinalTypeCheck)
variable {s : State roles} {n : Nat}

theorem pre_selected (v : Pre s) : Local sourceRegistry s root (.selected 0 []) := by
  obtain ⟨p,cert⟩ := v.plan
  have clear : ¬GeneralNominalVersionedMergedConflict232.MergedOutputConflict s root := by
    rintro ⟨⟨a,b,member,_,_⟩,_⟩
    change (a,b) ∈ s.core.erased.current.aliases at member
    rw [v.anchor.aliases] at member
    cases member
  apply GeneralNominalVersionedMixedSourceBoundary234.local_iff.mpr
  apply GeneralNominalVersionedMixedBoundary234.local_iff.mpr
  exact GeneralNominalVersionedDiagnosticLaws232.selected_of_model
    (GeneralRebaseDepthEnableSafety286.safe v.anchor cert)
    (GeneralRebaseDepthEnableSafety286.unique v.anchor cert)
    ((v.anchor.models model).mpr example_check) cert.frame cert.ready
    (packet_holds v.anchor cert model example_check output_valid)
    (cert.class_of_output model output_valid) clear

theorem selected_all (path : ActualPath initial s n) : Local sourceRegistry s root (.selected 0 []) := by
  rcases GeneralRebaseDepthPhase286.path_covered (.inl GeneralRebaseDepthPhase286.start) path with pre|post
  · exact pre_selected pre
  · exact GeneralRebaseDepthPostQueries286.selected post

theorem uniform_bits (path : ActualPath initial s n) :
    Valid (boundary8 roles) registry s root bits := by
  have picked := GeneralNominalVersionedMixedBoundary234.local_iff.mp
    (GeneralNominalVersionedMixedSourceBoundary234.local_iff.mp (selected_all path))
  have ⟨middle,sharing⟩ := B4TargetV8.selected_iff.mp picked
  have ⟨last,merged⟩ := B4TargetV7.selected_iff.mp middle
  cases last with
  | selected safe unique outputs =>
    refine ⟨safe.1,safe.2.1,safe.2.2.1,safe.2.2.2,unique,?_,merged,sharing⟩
    intro key
    change GeneralRebasePartialBool268.Reflect _ (if key = 0 then some false else none)
    split
    · rename_i zero
      subst key
      exact outputs
    · trivial

theorem exact_diagnostic (path : ActualPath initial s n)
    (f : CommonRoleOutermostResolver.Frontier (GeneralSourceDictionaries.Occurrence roles)) :
    run bits = some f ↔ B4TargetV8.Local (boundary8 roles) registry s root f :=
  GeneralRebaseDiagnosticV8268.exact_of_complete (boundary8 roles) registry s root bits
    (uniform_bits path) complete f

theorem exact_evidence (path : ActualPath initial s n) (m : Assignment) (payload : Payload) :
    Models s m ∧ Evidence registry s.core m root payload ↔ FinalTypeCheck m ∧ payload = .node 0 [] :=
  GeneralRebaseDepthPreEvidence286.same_joint_everywhere path m payload

theorem evidence_covers_all_iff_installed (path : ActualPath initial s n) :
    (∀ m, Models s m → Evidence registry s.core m root (.node 0 [])) ↔ (code s).installed = true := by
  rw [marker path |>.1]
  constructor
  · intro full
    rcases GeneralRebaseDepthPhase286.path_covered (.inl GeneralRebaseDepthPhase286.start) path with pre|post
    · obtain ⟨m,prior,lack⟩ := GeneralRebaseDepthPreEvidence286.pre_noncoverage pre
      exact (lack _ (full m prior)).elim
    · exact post
  · intro post m valid
    exact ((exact_evidence path m (.node 0 [])).mpr
      ⟨(GeneralRebaseDepthPostQueries286.models post m).mp valid,rfl⟩).2

end Yulang.GeneralMixedFullControlObserver306
