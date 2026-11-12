import Yulang.GeneralDictionaryOrdinaryTransport
import Yulang.GeneralDictionaryFeedbackEvidence

/-! Source evidence through actual feedback steps whose contexts change only
ordinary constraints and allocation bookkeeping. This is a restriction of the
existing Step relation for a transport proof, not a new source transition or a
new dictionary judgment. Descriptor-changing refresh is intentionally excluded. -/
namespace Yulang.GeneralDictionaryOrdinaryTrace
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalSaturationState
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
open GeneralDictionaryOrdinaryTransport (extendState)

abbrev extendContext (context : GeneralNominalCandidates.Context)
    (reserved : List Nat) (atoms : List (PresenceNormalForm.Atom Nat))
    (allocated : List GeneralNominalIdentities.Origin) : GeneralNominalCandidates.Context :=
  ⟨extendState context.state reserved atoms allocated,context.interpretation⟩

/-- Exact context shape, not an assumption that evidence already transports. -/
def Extension (before after : GeneralNominalCandidates.Context) : Prop :=
  ∃ reserved atoms allocated, after = extendContext before reserved atoms allocated

theorem extension_refl (context : GeneralNominalCandidates.Context) : Extension context context := by
  refine ⟨[],[],[],?_⟩
  simp [extendContext,extendState]

theorem extension_trans {before middle after : GeneralNominalCandidates.Context}
    (first : Extension before middle) (last : Extension middle after) : Extension before after := by
  obtain ⟨rs,as,ks,rfl⟩ := first
  obtain ⟨rt,ats,kt,rfl⟩ := last
  refine ⟨rs ++ rt,as ++ ats,ks ++ kt,?_⟩
  simp [extendContext,extendState,List.append_assoc]

/-- The actual packet private context is exactly such an extension, including
its allocation ledger; no freshness or model premise is silently supplied. -/
theorem packet_extension (packet : Packet roles) : Extension packet.context packet.privateContext := by
  refine ⟨GeneralNominalAllocation.reserved packet.context.state packet.registry packet.site.occurrence.identity,
    (GeneralNominalAllocation.cross packet.bindings ++
      GeneralNominalAllocation.merges packet.context.state packet.registry packet.site.occurrence.identity
        packet.declaration packet.bindings) ++
      GeneralNominalRecursiveInspection.selfChecks packet.context.state
        (GeneralNominalRecursiveCandidates.report packet.context packet.declaration packet.bounds),
    GeneralNominalAllocation.keys packet.registry packet.site.occurrence.identity,?_⟩
  simp [Packet.privateContext,GeneralNominalRecursiveCandidates.privateState,
    GeneralNominalAllocation.propagate,GeneralNominalState.extend,extendContext,extendState,
    Packet.bindings,List.append_assoc]

/-- All real installations preserve the inspection view. -/
theorem install_extension (state : State roles) (packet : Packet roles)
    (same : packet.context = state.context) :
    Extension state.context
      (GeneralNominalFeedbackSites.install state packet (GeneralNominalFeedbackSites.emitted packet)).context := by
  simpa only [GeneralNominalFeedbackSites.install, same] using packet_extension packet

theorem enqueue_extension (state : State roles) (root : Occurrence roles) :
    Extension state.context (enqueue state root).context := extension_refl _

theorem merge_extension (state : State roles) (first last : GeneralNominalDemandMerging.Site roles) :
    Extension state.context (merge state first last).context := by
  refine ⟨[],GeneralNominalDemandMerging.outputAtoms first last,[],?_⟩
  simp [merge,extendContext,extendState,GeneralNominalState.extend]

theorem equate_extension (state : State roles) (first last : Nat) :
    Extension state.context (GeneralNominalFeedbackSteps.equate state first last).context := by
  refine ⟨[],GeneralNominalAllocation.equations first (.var last),[],?_⟩
  simp [GeneralNominalFeedbackSteps.equate,extendContext,extendState,GeneralNominalState.extend]

/-- Only existing feedback steps, with the exact no-view-change side condition. -/
def OrdinaryStep (registry : Registry) (root : Occurrence roles) (before after : State roles) : Prop :=
  GeneralNominalFeedbackSteps.Step registry root before after ∧ Extension before.context after.context

theorem ordinary_trace_extension (registry : Registry) (root : Occurrence roles)
    (before after : State roles)
    (path : B4Target.Steps (OrdinaryStep registry root) before after) :
    Extension before.context after.context := by
  induction path with
  | refl => exact extension_refl _
  | tail _ step ih => exact extension_trans ih step.2

/-- This path is a real feedback trace, not an invented update execution. -/
theorem ordinary_trace_feedback (registry : Registry) (root : Occurrence roles)
    (before after : State roles)
    (path : B4Target.Steps (OrdinaryStep registry root) before after) :
    B4Target.Steps (GeneralNominalFeedbackSteps.Step registry root) before after := by
  induction path with
  | refl => exact .refl
  | tail _ step ih => exact .tail ih step.1

/-- The final model supplies the additional equations. No candidate consistency
witness is substituted for that particular model. -/
theorem instance_extension (registry : Registry)
    (before after : GeneralNominalCandidates.Context) (growth : Extension before after)
    (model : Assignment) (valid : GeneralNominalState.Models after.state model)
    (root : Occurrence roles) (key : Nat) (children : List (Occurrence roles))
    (source : GeneralDictionaryRecursiveEvidence.Instance registry before model root key children) :
    GeneralDictionaryRecursiveEvidence.Instance registry after model root key children := by
  obtain ⟨reserved,atoms,allocated,rfl⟩ := growth
  apply (GeneralDictionaryOrdinaryTransport.instance_extend_iff
    (allocated := allocated) (reserved := reserved) (atoms := atoms) registry before model root key children).mpr
  refine ⟨source,?_⟩
  exact (GeneralDictionaryOrdinaryTransport.models_extended
    (allocated := allocated) (reserved := reserved) (atoms := atoms) _ _).mp valid |>.2

theorem evidence_extension (registry : Registry)
    (before after : GeneralNominalCandidates.Context) (growth : Extension before after)
    (model : Assignment) (valid : GeneralNominalState.Models after.state model)
    (root : Occurrence roles) (payload : Payload)
    (source : GeneralDictionaryRecursiveEvidence.Evidence registry before model root payload) :
    GeneralDictionaryRecursiveEvidence.Evidence registry after model root payload := by
  obtain ⟨reserved,atoms,allocated,rfl⟩ := growth
  apply (GeneralDictionaryOrdinaryTransport.evidence_extend_iff allocated reserved atoms
    registry before model root payload).mpr
  exact ⟨source,(GeneralDictionaryOrdinaryTransport.models_extended allocated reserved atoms _ _).mp valid |>.2⟩

theorem evidence_extension_backward (registry : Registry)
    (before after : GeneralNominalCandidates.Context) (growth : Extension before after)
    (model : Assignment) (root : Occurrence roles) (payload : Payload)
    (source : GeneralDictionaryRecursiveEvidence.Evidence registry after model root payload) :
    GeneralDictionaryRecursiveEvidence.Evidence registry before model root payload := by
  obtain ⟨reserved,atoms,allocated,rfl⟩ := growth
  exact ((GeneralDictionaryOrdinaryTransport.evidence_extend_iff allocated reserved atoms
    registry before model root payload).mp source).1

/-- The install function under Installable, followed by an ordinary-only feedback trace, yields
source evidence at the FINAL inspection context, not only the stored context.
The initial install is a Step only with generated-focus and novelty premises. -/
theorem installed_trace_current_instance (registry : Registry) (root : Occurrence roles)
    (before after : State roles) (packet : Packet roles)
    (enabled : GeneralNominalFeedbackSteps.Installable registry before packet)
    (path : B4Target.Steps (OrdinaryStep registry root)
      (GeneralNominalFeedbackSites.install before packet (GeneralNominalFeedbackSites.emitted packet)) after)
    (model : Assignment) (valid : Models after model) :
    GeneralDictionaryRecursiveEvidence.Instance packet.registry after.context model
      packet.site.occurrence packet.declaration.id packet.children := by
  have realPath := ordinary_trace_feedback registry root _ after path
  have source := (GeneralDictionaryFeedbackEvidence.installed_trace_instance
    registry root before after packet enabled realPath).1 model valid
  have growth := extension_trans (packet_extension packet)
    (ordinary_trace_extension registry root _ after path)
  exact instance_extension packet.registry packet.context after.context growth model valid.1
    packet.site.occurrence packet.declaration.id packet.children source

/-- With generated-focus and novelty supplied, the first installation and all
following ordinary steps form one actual feedback trace. -/
theorem installed_trace_execution (registry : Registry) (root : Occurrence roles)
    (before after : State roles) (packet : Packet roles)
    (enabled : GeneralNominalFeedbackSteps.Installable registry before packet)
    (reached : Generated before root packet.site.occurrence)
    (novel : ¬ GeneralNominalFeedbackSteps.Committed before packet)
    (path : B4Target.Steps (OrdinaryStep registry root)
      (GeneralNominalFeedbackSites.install before packet (GeneralNominalFeedbackSites.emitted packet)) after) :
    B4Target.Steps (GeneralNominalFeedbackSteps.Step registry root) before after := by
  have initial : GeneralNominalFeedbackSteps.Step registry root before
      (GeneralNominalFeedbackSites.install before packet (GeneralNominalFeedbackSites.emitted packet)) :=
    ⟨packet.site.occurrence,reached,.install packet enabled novel⟩
  induction path with
  | refl => exact .tail .refl initial
  | tail _ step ih => exact .tail ih step.1

/-- Same-final-model child evidence assembles the actual installed source node.
This does not assert that every newly selected stable node was installed. -/
theorem installed_trace_current_evidence (registry : Registry) (root : Occurrence roles)
    (before after : State roles) (packet : Packet roles)
    (enabled : GeneralNominalFeedbackSteps.Installable registry before packet)
    (path : B4Target.Steps (OrdinaryStep registry root)
      (GeneralNominalFeedbackSites.install before packet (GeneralNominalFeedbackSites.emitted packet)) after)
    (model : Assignment) (valid : Models after model) (dictionaries : List Payload)
    (given : CommonRoleOutermostResolver.All₂
      (GeneralDictionaryRecursiveEvidence.Evidence packet.registry after.context model)
      packet.children dictionaries) :
    GeneralDictionaryRecursiveEvidence.Evidence packet.registry after.context model packet.site.occurrence
      (.node packet.declaration.id dictionaries) :=
  GeneralDictionaryRecursiveEvidence.evidence_node packet.registry after.context model packet.site.occurrence
    packet.declaration.id packet.children dictionaries
    (installed_trace_current_instance registry root before after packet enabled path model valid) given

end Yulang.GeneralDictionaryOrdinaryTrace
