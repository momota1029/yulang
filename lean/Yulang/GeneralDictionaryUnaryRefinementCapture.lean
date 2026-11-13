import Yulang.GeneralDictionaryBindingSchemaReplay
import Yulang.GeneralNominalUnaryCaptureFacts

/-! Source-ID capture and origin preservation for a unary nominal-variable
head under arbitrary source-preserving Refines. Carrier sizes may differ.
This is not arbitrary structural inspection or arbitrary descriptor revision. -/
namespace Yulang.GeneralDictionaryUnaryRefinementCapture
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalUnaryCaptureFacts GeneralNominalInspection
open GeneralDeclarations

variable (before after : Context)
variable (refinement : GeneralNominalRefinements.Refines before.state after.state)
variable (interpretation : after.interpretation = before.interpretation)
variable (declaration : Declaration)
variable (slot : Fin before.state.base.slots)
variable (descriptor : GeneralNominalState.Descriptor before.state.base.slots)
variable (recorded : before.state.nominals slot = some descriptor)
variable (binder : Nat) (bounds : Bounds before.state)
variable (parameters : descriptor.arguments = [.type bounds])
variable (query : queries before.state before.interpretation declaration =
  [.nominal descriptor.declaration.name [.variables [binder]]])

abbrev renamedBounds : Bounds after.state := (refinement.base.embed bounds.1,refinement.base.embed bounds.2)

include refinement interpretation in
theorem queries_preserved : queries after.state after.interpretation declaration =
    queries before.state before.interpretation declaration := by
  unfold queries
  rw [refinement.constructors,interpretation]

include refinement interpretation recorded parameters query

theorem report_refined : report after declaration [(refinement.base.embed slot,refinement.base.embed slot)] =
    captured after.state (refinement.base.embed slot) descriptor.declaration.name binder
      (renamedBounds before after refinement bounds) := by
  apply report_exact after declaration (refinement.base.embed slot)
    (GeneralNominalRefinements.renameDescriptor refinement.base.embed descriptor)
    (refinement.nominals slot descriptor recorded) binder (renamedBounds before after refinement bounds)
  · simp [GeneralNominalRefinements.renameDescriptor,parameters,GeneralNominalRefinements.renameParameter,renamedBounds]
  · rw [queries_preserved before after refinement interpretation declaration]
    exact query

theorem bindings_preserved : bindings after.state
    (report after declaration [(refinement.base.embed slot,refinement.base.embed slot)]) =
    bindings before.state (report before declaration [(slot,slot)]) := by
  rw [report_refined before after refinement interpretation declaration slot descriptor recorded binder bounds parameters query,
    report_exact before declaration slot descriptor recorded binder bounds parameters query]
  simp [GeneralNominalRecursiveInspection.bindings,captured,renamedBounds,refinement.base.source]

/-- Every current capture keeps the same name and source-based nominal origin.
No semantic validity or final-report equality is assumed. -/
theorem origins_preserved : ∀ current ∈
    (report after declaration [(refinement.base.embed slot,refinement.base.embed slot)]).captures,
    ∃ old ∈ (report before declaration [(slot,slot)]).captures,
      old.name = current.name ∧ old.origin = current.origin := by
  rw [report_refined before after refinement interpretation declaration slot descriptor recorded binder bounds parameters query,
    report_exact before declaration slot descriptor recorded binder bounds parameters query]
  intro current member
  have equal := List.mem_singleton.mp member
  subst current
  refine ⟨_,List.mem_cons_self,rfl,?_⟩
  simp [refinement.base.source]

end Yulang.GeneralDictionaryUnaryRefinementCapture

namespace Yulang.GeneralDictionaryUnaryRefinementCapture
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalUnaryCaptureFacts GeneralNominalInspection
open GeneralDeclarations GeneralNominalSaturationState

/-- An arbitrary recorded unary nominal-variable packet replays its complete
named schema across a source-preserving carrier refinement. No computed binding
or final Models conclusion is among the transport hypotheses. -/
theorem recorded_schema (root : GeneralSourceDictionaries.Occurrence roles)
    (state : GeneralNominalSupport.Tracked roles) (packet : Packet roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) packet.registry root state)
    (recorded : packet ∈ state.current.packets)
    (refinement : GeneralNominalRefinements.Refines packet.context.state state.current.context.state)
    (interpretation : state.current.context.interpretation = packet.context.interpretation)
    (slot : Fin packet.context.state.base.slots)
    (descriptor : GeneralNominalState.Descriptor packet.context.state.base.slots)
    (nominal : packet.context.state.nominals slot = some descriptor)
    (binder : Nat) (bounds : Bounds packet.context.state)
    (parameters : descriptor.arguments = [.type bounds])
    (query : queries packet.context.state packet.context.interpretation packet.declaration =
      [.nominal descriptor.declaration.name [.variables [binder]]])
    (packetBounds : packet.bounds = [(slot,slot)])
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    let currentBounds := [(refinement.base.embed slot,refinement.base.embed slot)]
    GeneralNominalMaterialization.Models state.current.context.state packet.declaration
      (GeneralNominalAllocation.capture state.current.context.state packet.registry packet.site.occurrence.identity
        packet.declaration.id (GeneralNominalRecursiveInspection.bindings state.current.context.state
          (report state.current.context packet.declaration currentBounds)))
      (report state.current.context packet.declaration currentBounds)
      (generated packet.registry state.current.context packet.site.occurrence packet.declaration packet.checked currentBounds) model := by
  apply GeneralDictionaryBindingSchemaReplay.replay packet.registry root state reachable packet recorded
  · unfold Packet.bindings
    rw [packetBounds]
    exact bindings_preserved packet.context state.current.context refinement interpretation packet.declaration
      slot descriptor nominal binder bounds parameters query
  · intro entry member captured present same actual origin known
    obtain ⟨old,oldMember,names,origins⟩ := origins_preserved packet.context state.current.context refinement interpretation
      packet.declaration slot descriptor nominal binder bounds parameters query captured present
    refine ⟨old,?_,names,origins.trans known⟩
    change old ∈ (report packet.context packet.declaration packet.bounds).captures
    rw [packetBounds]
    exact oldMember
  · exact valid

/-- Full current private/projection/materialization branch for the one-binder fragment. -/
theorem recorded_branch (root : GeneralSourceDictionaries.Occurrence roles)
    (state : GeneralNominalSupport.Tracked roles) (packet : Packet roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) packet.registry root state)
    (recorded : packet ∈ state.current.packets)
    (refinement : GeneralNominalRefinements.Refines packet.context.state state.current.context.state)
    (interpretation : state.current.context.interpretation = packet.context.interpretation)
    (slot : Fin packet.context.state.base.slots)
    (descriptor : GeneralNominalState.Descriptor packet.context.state.base.slots)
    (nominal : packet.context.state.nominals slot = some descriptor)
    (binder : Nat) (bounds : Bounds packet.context.state)
    (parameters : descriptor.arguments = [.type bounds])
    (query : queries packet.context.state packet.context.interpretation packet.declaration =
      [.nominal descriptor.declaration.name [.variables [binder]]])
    (packetBounds : packet.bounds = [(slot,slot)])
    (names : packet.declaration.inputNames = [binder])
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    BranchModels packet.registry state.current.context packet.site.occurrence packet.declaration packet.checked
      [(refinement.base.embed slot,refinement.base.embed slot)] model := by
  have currentQuery : queries state.current.context.state state.current.context.interpretation packet.declaration =
      [.nominal descriptor.declaration.name [.variables [binder]]] := by
    rw [queries_preserved packet.context state.current.context refinement interpretation packet.declaration]
    exact query
  have currentParameters : (GeneralNominalRefinements.renameDescriptor refinement.base.embed descriptor).arguments =
      [.type (refinement.base.embed bounds.1,refinement.base.embed bounds.2)] := by
    simp [GeneralNominalRefinements.renameDescriptor,parameters,GeneralNominalRefinements.renameParameter]
  have privateModel := private_models state.current.context packet.registry packet.site.occurrence packet.declaration
    (refinement.base.embed slot) (GeneralNominalRefinements.renameDescriptor refinement.base.embed descriptor)
    (refinement.nominals slot descriptor nominal) binder names
    (refinement.base.embed bounds.1,refinement.base.embed bounds.2) currentParameters currentQuery model valid.1
  exact ⟨privateModel.1,privateModel.2,recorded_schema root state packet reachable recorded refinement interpretation
    slot descriptor nominal binder bounds parameters query packetBounds model valid⟩
end Yulang.GeneralDictionaryUnaryRefinementCapture
