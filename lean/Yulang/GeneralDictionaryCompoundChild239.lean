import Yulang.GeneralDictionaryCompoundRefreshStep239
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryCompoundChild239
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryCompoundSource238 GeneralDictionaryCompoundSites238
open GeneralDictionaryCompoundBase239 GeneralDictionaryCompoundSnapshot239
open GeneralDictionaryCompoundRefresh239
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalVersionedCandidates231 (inputs)
open GeneralNominalCenters

theorem located : arguments extendedContext (inputs childSite.occurrence) = some [(5,6)] := by decide +kernel

theorem query : GeneralNominalInspection.queries extendedSnapshot interpretation declaration =
    [.nominal 0 [.variables [0],.variables [0]]] := by
  simp [GeneralNominalInspection.queries,GeneralDeclarations.Declaration.normalHead,
    GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
    GeneralNominalInspection.translate,interpretation]

theorem report_exact : report extendedContext declaration [(5,6)] =
    { inspected := [(5,6)], checked := [(5,6),(5,6)], conflicts := [(5,6)] } := by
  unfold report
  rw [query]
  simp [inspectMany,inspect,Report.visit,Report.append,viewHeads]

theorem no_prepared : ¬ GeneralNominalVersionedCandidates231.Prepared registry extendedContext childSite.occurrence declaration := by
  rintro ⟨_,_,bounds,locatedHyp,_,done,_⟩
  have same : bounds = [(5,6)] := Option.some.inj (locatedHyp.symm.trans located)
  subst bounds
  rw [report_exact] at done
  have bad := done.2.1
  cases bad

theorem no_survivor (key : Nat) (children : List (GeneralSourceDictionaries.Occurrence roles)) :
    ¬ GeneralNominalVersionedCandidates231.Survivor registry extendedContext childSite.occurrence key children := by
  rintro ⟨_,candidate,visible,_,_,_,_,_,prepared,_⟩
  cases List.mem_singleton.mp visible
  exact no_prepared prepared

theorem no_frame (key : Nat) (plan : Plan roles) :
    ¬ GeneralNominalVersionedEvidence231.Frame registry refreshed.core childSite.occurrence key plan := by
  intro framed
  have candidate : plan.packet.declaration = declaration := List.mem_singleton.mp framed.visible
  have ready := framed.prepared
  rw [candidate] at ready
  exact no_prepared ready

theorem no_instance (model : GeneralNominalCommonBridge.Assignment) (key : Nat)
    (children : List (GeneralSourceDictionaries.Occurrence roles)) :
    ¬ GeneralNominalVersionedEvidence231.Instance registry refreshed.core model childSite.occurrence key children := by
  rintro ⟨plan,certificate⟩
  exact no_frame key plan certificate.frame

theorem no_evidence (model : GeneralNominalCommonBridge.Assignment) (payload : GeneralDictionaryReadback.Payload) :
    ¬ GeneralNominalVersionedEvidence231.Evidence registry refreshed.core model childSite.occurrence payload := by
  intro evidence
  have proof := (GeneralDictionaryReadback.payload_iff_erased _ _ _).mpr evidence
  cases proof with
  | node instanceRule _ => exact no_instance model _ _ instanceRule
end Yulang.GeneralDictionaryCompoundChild239
