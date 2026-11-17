import Yulang.GeneralDictionaryCompoundNoInstance238
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
namespace Yulang.GeneralDictionaryCompoundChildPending238
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryCompoundSource238 GeneralDictionaryCompoundPoint238 GeneralDictionaryCompoundSites238
open GeneralNominalCenters GeneralNominalVersionedEvidence231
open GeneralNominalCommonBridge (Assignment)

theorem unlocated : GeneralNominalRecursiveCandidates.arguments point.core.erased.current.context
    (GeneralNominalVersionedCandidates231.inputs childSite.occurrence) = none := by
  rw [context_exact]
  decide +kernel

theorem no_frame (key : Nat) (plan : Plan roles) : ¬ Frame registry point.core childSite.occurrence key plan := by
  intro framed
  have located := congrArg Option.isSome framed.located
  change (GeneralNominalRecursiveCandidates.arguments plan.packet.context (GeneralNominalVersionedCandidates231.inputs childSite.occurrence)).isSome = true at located
  rw [framed.context_eq,unlocated] at located
  cases located

theorem no_instance (model : Assignment) (key : Nat) (children : List (GeneralSourceDictionaries.Occurrence roles)) :
    ¬ Instance registry point.core model childSite.occurrence key children := by
  rintro ⟨plan,certificate⟩
  exact no_frame key plan certificate.frame

theorem no_evidence (model : Assignment) (payload : GeneralDictionaryReadback.Payload) :
    ¬ Evidence registry point.core model childSite.occurrence payload := by
  intro evidence
  have proof := (GeneralDictionaryReadback.payload_iff_erased _ _ _).mpr evidence
  cases proof with
  | node instanceRule _ => exact no_instance model _ _ instanceRule

theorem no_root_evidence (model : Assignment) (valid : GeneralNominalVersionedJournal232.Models point model)
    (payload : GeneralDictionaryReadback.Payload) : ¬ Evidence registry point.core model root payload := by
  intro evidence
  have proof := (GeneralDictionaryReadback.payload_iff_erased _ _ _).mpr evidence
  cases proof with
  | node instanceRule _ => exact GeneralDictionaryCompoundNoInstance238.no_instance model valid _ _ instanceRule

end Yulang.GeneralDictionaryCompoundChildPending238
