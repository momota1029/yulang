import Yulang.GeneralNominalIdentityLeaf
import Yulang.GeneralDictionarySharedRecordedEvidence

/-! Current-context terminal evidence for the syntactic point identity fragment.
No ordinary-extension premise is needed; current location and metadata remain explicit. -/
namespace Yulang.GeneralDictionaryIdentityCurrentEvidence
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalIdentityLeaf GeneralNominalRecursiveCandidates
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalSupport
open GeneralDictionaryRecursiveEvidence

variable {roles : Roles.RoleDecls}

def rebase (packet : Packet roles) (context : Context)
    (slot : Fin context.state.base.slots) : Packet roles :=
  ⟨packet.registry,context,packet.site,packet.declaration,packet.checked,[(slot,slot)]⟩

theorem rebase_outputs (packet : Packet roles) (shape : Shape packet.declaration)
    (old : Fin packet.context.state.base.slots) (bounds : packet.bounds = [(old,old)])
    (context : Context) (slot : Fin context.state.base.slots)
    (same : context.state.base.source slot = packet.context.state.base.source old)
    (model : Assignment) (outputs : GeneralNominalPacketSupport.Outputs packet model) :
    GeneralNominalPacketSupport.Outputs (rebase packet context slot) model := by
  apply (outputs_exact (packet := rebase packet context slot) shape rfl model).mpr
  intro target member
  have eq := (outputs_exact shape bounds model).mp outputs target member
  simpa only [rebase,same] using eq

theorem rebase_holds (packet : Packet roles) (shape : Shape packet.declaration)
    (old : Fin packet.context.state.base.slots) (bounds : packet.bounds = [(old,old)])
    (context : Context) (slot : Fin context.state.base.slots)
    (same : context.state.base.source slot = packet.context.state.base.source old)
    (model : Assignment) (valid : GeneralNominalState.Models context.state model)
    (outputs : GeneralNominalPacketSupport.Outputs packet model) :
    (rebase packet context slot).Holds model :=
  (GeneralNominalPacketSupport.packet_exact _ model).mpr
    ⟨valid,inputs_valid (packet := rebase packet context slot) shape rfl model,rebase_outputs packet shape old bounds context slot same model outputs⟩

theorem recorded_current_instance {registry : Registry} {root : Occurrence roles}
    {state : Tracked roles} (formed : GeneralNominalSharedSteps.SourceFormed registry root state)
    (packet : Packet roles) (member : packet ∈ state.current.packets)
    (shape : Shape packet.declaration) (input : Nat)
    (point : Point packet.site.occurrence input)
    (slot : Fin state.current.context.state.base.slots)
    (source : state.current.context.state.base.source slot = input)
    (located : arguments state.current.context packet.site.occurrence = some [(slot,slot)])
    (metadata : GeneralNominalCandidates.Metadata registry state.current.context)
    (model : Assignment) (valid : Models state.current model) :
    Instance registry state.current.context model packet.site.occurrence packet.declaration.id [] := by
  obtain ⟨same,visible,role,oldLocated,prepared⟩ :=
    (GeneralDictionarySharedRecordedEvidence.formed_recorded formed packet member).1
  obtain ⟨old,bounds,oldSource⟩ := located_point point oldLocated
  have outputs := ((GeneralNominalPacketSupport.packet_exact packet model).mp
    (valid.2.1 packet member)).2.2
  have holds := rebase_holds packet shape old bounds state.current.context slot
    (source.trans oldSource.symm) model valid.1 outputs
  obtain ⟨_,_,_,bs,found,_,ready,_⟩ := prepared
  have equal := Option.some.inj (oldLocated.symm.trans found)
  subst bs
  have schema := named_schema (packet := rebase packet state.current.context slot) shape
  have currentReady : RequestReady packet.registry state.current.context packet.site.occurrence
      packet.declaration packet.checked [(slot,slot)] := by
    refine ⟨ready.1,?_⟩
    change (GeneralNominalPacketSupport.namedSchema (rebase packet state.current.context slot)).unknown = false
    rw [schema]
    rfl
  rw [← same] at metadata ⊢
  refine ⟨packet.declaration,visible,packet.checked,rfl,role,[(slot,slot)],located,?_,currentReady,?_,metadata,holds⟩
  · rw [report_exact shape]
    simp [GeneralNominalRecursiveInspection.Finished,pointReport]
  · exact (children_empty (rebase packet state.current.context slot) shape.terminal).symm

theorem recorded_current_evidence {registry : Registry} {root : Occurrence roles}
    {state : Tracked roles} (formed : GeneralNominalSharedSteps.SourceFormed registry root state)
    (packet : Packet roles) (member : packet ∈ state.current.packets)
    (shape : Shape packet.declaration) (input : Nat)
    (point : Point packet.site.occurrence input)
    (slot : Fin state.current.context.state.base.slots)
    (source : state.current.context.state.base.source slot = input)
    (located : arguments state.current.context packet.site.occurrence = some [(slot,slot)])
    (metadata : GeneralNominalCandidates.Metadata registry state.current.context)
    (model : Assignment) (valid : Models state.current model) :
    Evidence registry state.current.context model packet.site.occurrence (.node packet.declaration.id []) :=
  evidence_node _ _ _ _ _ _ _
    (recorded_current_instance formed packet member shape input point slot source located metadata model valid) .nil

end Yulang.GeneralDictionaryIdentityCurrentEvidence
