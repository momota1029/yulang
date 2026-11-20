import Yulang.GeneralRebaseDepthPreAvailable286

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29500
set_option maxHeartbeats 14100000
namespace Yulang.GeneralRebaseDepthPostQueries286
open GeneralDictionaryOutputDepth252 (roles sourceRegistry registry root model)
open GeneralDictionaryOutputDepthInstall252 (installed)
open GeneralRebaseDepthPhase286 (Post)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedEvidence231 (Evidence)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
open GeneralRebaseDepthGroundModels285 (FinalTypeCheck final_check)
open GeneralRebaseDepthPathEvidenceAt285 (kept_survivor selected_unique)
open GeneralNominalVersionedCandidates231 (Unique survivor_children_functional)

theorem models {s : State roles} (a : Post s) (m : Assignment) :
    Models s m ↔ FinalTypeCheck m := (a.anchor.models m).trans (final_check m)

theorem concrete {s : State roles} (a : Post s) (m : Assignment) (p : Payload) :
    Models s m ∧ Evidence registry s.core m root p ↔ FinalTypeCheck m ∧ p = .node 0 [] := by
  obtain ⟨plan,frame,_,committed,ready,terminal⟩ := a.witness
  constructor
  · rintro ⟨modelValid,called⟩
    refine ⟨(models a m).mp modelValid,?_⟩
    have erased := (GeneralDictionaryReadback.payload_iff_erased _ _ _).mpr called
    cases erased with
    | node details ordered =>
      obtain ⟨q,details⟩ := details
      have same := GeneralRebaseDepthPathKeep285.same_plan a.anchor
        (GeneralRebaseDepthPathKeep285.of_frame details.frame)
        (GeneralRebaseDepthPathKeep285.of_frame frame)
      subst q
      rw [details.children_eq,terminal] at ordered
      cases ordered
      exact congrArg (fun i => CommonRoleOutermostResolver.Dictionary.node i [])
        (details.frame.key_eq.symm.trans frame.key_eq)
  · rintro ⟨checked,rfl⟩
    have valid := (models a m).mpr checked
    have paired := committed.1 m valid
    exact ⟨valid,GeneralNominalVersionedEvidence231.evidence_leaf
      ⟨plan,GeneralNominalVersionedEvidence231.certificate_of_semantics frame terminal.symm
        paired.1 ready (frame.occurrence_eq ▸ paired.2)⟩⟩

theorem same_joint {s : State roles} (a : Post s) (m : Assignment) (p : Payload) :
    Models s m ∧ Evidence registry s.core m root p ↔
      Models installed m ∧ Evidence registry installed.core m root p :=
  (concrete a m p).trans (GeneralRebaseDepthPayload285.same_assignment_exact m p).symm

theorem no_merged {s : State roles} (a : Post s) :
    ¬ GeneralNominalVersionedMergedConflict232.MergedOutputConflict s root := by
  rintro ⟨⟨x,y,member,_,_⟩,_⟩
  change (x,y) ∈ s.core.erased.current.aliases at member
  rw [a.aliases] at member
  cases member

theorem selected {s : State roles} (a : Post s) : Local sourceRegistry s root (.selected 0 []) := by
  have positive := kept_survivor a.anchor a.witness
  have uniq : Unique registry s.core.erased.current.context root 0 [] := by
    refine ⟨positive,?_⟩
    intro key kids other
    have copy := other
    obtain ⟨_,d,visible,_,key_eq,_,_,_,_,_⟩ := other
    cases List.mem_singleton.mp visible
    have same : key = 0 := key_eq.symm
    subst key
    exact ⟨rfl,survivor_children_functional GeneralDictionaryOutputDepth252.checked copy positive⟩
  have safe := GeneralRebaseDepthPathSelection285.safe a.anchor a.witness
  obtain ⟨p,frame,_,committed,ready,_⟩ := a.witness
  have valid := GeneralRebaseDepthPathAnchor285.valid_model a.anchor.models
  have facts := committed.1 model valid
  apply GeneralNominalVersionedMixedSourceBoundary234.local_iff.mpr
  apply GeneralNominalVersionedMixedBoundary234.local_iff.mpr
  exact GeneralNominalVersionedDiagnosticLaws232.selected_of_model safe uniq valid frame ready
    facts.1 (frame.occurrence_eq ▸ facts.2) (no_merged a)

theorem evidence_at {s : State roles} (a : Post s) :
    B4SkeletonV8.EvidenceAt (boundary roles) sourceRegistry s root := by
  intro model valid focus key children dictionaries roots _ _ choice ready
  have found : focus = root := roots.elim id
    (GeneralNominalVersionedMixedTerminalStable234.generated_only a.anchor.sites a.anchor.edges)
  subst focus
  have eq := B4TargetV8.local_functional choice (selected a)
  cases eq
  cases ready
  exact ((concrete a model (.node 0 [])).mpr ⟨(models a model).mp valid,rfl⟩).2

end Yulang.GeneralRebaseDepthPostQueries286
