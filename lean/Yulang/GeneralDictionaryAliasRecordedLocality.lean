import Yulang.GeneralDictionaryFiniteJournalJoint
import Yulang.GeneralDictionaryEarlyMergeChoices

/-! Recorded alias classes need not consist of one literal occurrence.
Ordinary historical replay is performed at each site's own occurrence in one
current model. Early operational merges supply journal-key coherence. -/
namespace Yulang.GeneralDictionaryAliasRecordedLocality
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalSupportSteps GeneralNominalJointCandidates
variable {roles : Roles.RoleDecls}

/-- Pure journal and classifier coverage, without Instance, BranchAt, Joint,
Evidence, or any assertion that related occurrences are equal. -/
def Covered (registry : Registry) (state : Tracked roles) (focus : Occurrence roles) : Prop :=
  ∀ site, Related state.current focus site →
    (∃ packet ∈ state.current.packets, packet.site.occurrence = site.occurrence) ∧
    ∃ key children, GeneralNominalSupportBoundary.Local registry state site.occurrence (.selected key children)

/-- The prior literal-locality hypothesis is a special case of recorded
coverage. The new result permits different related occurrences instead. -/
theorem covered_of_locality (registry : Registry) (state : Tracked roles) (focus : Occurrence roles)
    (packet : Packet roles) (member : packet ∈ state.current.packets) (same : packet.site.occurrence = focus)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalSupportBoundary.Local registry state focus (.selected key children))
    (locality : ∀ site, Related state.current focus site → site.occurrence = focus) :
    Covered registry state focus := by
  intro site related
  rw [locality site related]
  exact ⟨⟨packet,member,same⟩,key,children,selected⟩

/-- A covered alias site has its own replayed Instance. Coherence identifies its
key with the root key; no cross-occurrence private-state transfer is assumed. -/
theorem related_branch (registry : Registry) (root focus : Occurrence roles) (state : Tracked roles)
    (formed : SourceFormed registry root state)
    (growth : ∀ packet ∈ state.current.packets,
      GeneralDictionaryOrdinaryTrace.Extension packet.context state.current.context)
    (coherent : GeneralDictionarySupportChoices.Coherent state.current)
    (chosen : Packet roles) (member : chosen ∈ state.current.packets)
    (same : chosen.site.occurrence = focus) (key : Nat) (chosenKey : chosen.declaration.id = key)
    (covered : Covered registry state focus) (site : GeneralNominalDemandMerging.Site roles)
    (related : Related state.current focus site)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    BranchAt registry state.current site.occurrence key model := by
  obtain ⟨⟨packet,present,located⟩,selectedKey,children,selected⟩ := covered site related
  have replay := GeneralDictionaryOrdinarySelectedReplay.selected_replay registry root site.occurrence state formed
    packet present (growth packet present) located selectedKey children selected model valid
  have alias : Alias state.current chosen.site.occurrence.identity packet.site.occurrence.identity := by
    rw [same,located]
    exact related.2
  have keys : selectedKey = key := replay.1.symm.trans ((coherent chosen member packet present alias).symm.trans chosenKey)
  have survivor : GeneralNominalRecursiveCandidates.Survivor registry state.current.context site.occurrence selectedKey children := by
    cases selected with | selected _ unique => exact unique.1
  rw [← keys]
  exact GeneralNominalStructuralSelectedGraph.branchAt_of_instance registry state.current site.occurrence selectedKey children
    survivor model replay.2.2

/-- Arbitrary recorded alias classes share one model, even when their occurrence
IDs, child IDs and named output demands differ. Their actual packets replay the
appropriate obligations independently at that SAME supplied model. -/
theorem covered_joint (registry : Registry) (root focus : Occurrence roles) (state : Tracked roles)
    (formed : SourceFormed registry root state)
    (growth : ∀ packet ∈ state.current.packets,
      GeneralDictionaryOrdinaryTrace.Extension packet.context state.current.context)
    (coherent : GeneralDictionarySupportChoices.Coherent state.current)
    (packet : Packet roles) (member : packet ∈ state.current.packets) (same : packet.site.occurrence = focus)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalSupportBoundary.Local registry state focus (.selected key children))
    (covered : Covered registry state focus)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    Joint registry state.current focus key := by
  have replay := GeneralDictionaryOrdinarySelectedReplay.selected_replay registry root focus state formed
    packet member (growth packet member) same key children selected model valid
  have survivor : GeneralNominalRecursiveCandidates.Survivor registry state.current.context focus key children := by
    cases selected with | selected _ unique => exact unique.1
  refine ⟨?_,model,valid,?_,?_⟩
  · intro other present alias
    have equal := GeneralDictionarySupportChoices.recorded_class_key state.current coherent focus packet member
      (congrArg Occurrence.identity same) other present alias
    exact equal.trans replay.1
  · exact GeneralNominalStructuralSelectedGraph.branchAt_of_instance registry state.current focus key children
      survivor model replay.2.2
  · intro site related
    exact related_branch registry root focus state formed growth coherent packet member same key replay.1
      covered site related model valid

/-- Actual ordinary history supplies growth and source formation; the existing
actual early-merge schedule supplies coherence. No semantic key or branch
compatibility assumptions are added at merge steps by this wrapper. -/
theorem early_ordinary_joint (registry : Registry) (root focus : Occurrence roles)
    (context : GeneralNominalCandidates.Context)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (state : Tracked roles)
    (path : B4Target.Steps (GeneralDictionarySupportOrdinaryExecution.Step registry root)
      (GeneralNominalSupport.initial context root) state)
    (schedule : GeneralDictionaryEarlyMergeChoices.Scheduled registry root state)
    (packet : Packet roles) (member : packet ∈ state.current.packets) (same : packet.site.occurrence = focus)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalSupportBoundary.Local registry state focus (.selected key children))
    (covered : Covered registry state focus)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    Joint registry state.current focus key :=
  covered_joint registry root focus state
    (GeneralDictionarySupportOrdinaryExecution.steps_formed (.initial context source) path)
    (GeneralDictionarySupportOrdinaryExecution.initial_packets_extension registry root context state path)
    (GeneralDictionaryEarlyMergeChoices.scheduled_coherent registry root state schedule)
    packet member same key children selected covered model valid
end Yulang.GeneralDictionaryAliasRecordedLocality
