import Yulang.GeneralRebaseDisplayExecutor276
import Yulang.GeneralNominalVersionedMixedSourceBoundary234

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseCompiledRetag277
open GeneralDeclarations GeneralNominalCenters
open GeneralNominalSaturationState (Packet)
open GeneralNominalCommonBridge (Assignment)

def retagPacket (p : Packet roles) (r : Registry) (ctors : r.constructors = p.registry.constructors) :
    Packet roles :=
  { p with registry := r, checked := ctors.symm ▸ p.checked }

def retag (p : Plan roles) (r : Registry) (ctors : r.constructors = p.packet.registry.constructors) :
    Plan roles := ⟨retagPacket p.packet r ctors,p.input,p.input_exact⟩

theorem report_eq (p : Packet roles) (r : Registry) (ctors) :
    GeneralNominalPacketSupport.report (retagPacket p r ctors) = GeneralNominalPacketSupport.report p := rfl

theorem capture_eq (p : Packet roles) (r : Registry) (ctors) :
    GeneralNominalVersionedFrame231.capture (retagPacket p r ctors) =
      GeneralNominalVersionedFrame231.capture p := rfl

theorem children_eq (p : Packet roles) (r : Registry) (ctors) :
    GeneralNominalVersionedFrame231.children (retagPacket p r ctors) =
      GeneralNominalVersionedFrame231.children p := rfl

theorem ordinary (p : Packet roles) (r : Registry) (ctors) (m : Assignment) :
    GeneralNominalVersionedPlans231.Ordinary (retagPacket p r ctors) m ↔
      GeneralNominalVersionedPlans231.Ordinary p m := Iff.rfl

theorem headModels (p : Packet roles) (r : Registry) (ctors) (m : Assignment) :
    GeneralNominalVersionedPlans231.HeadModels (retagPacket p r ctors) m ↔
      GeneralNominalVersionedPlans231.HeadModels p m := by
  unfold GeneralNominalVersionedPlans231.HeadModels
  rw [GeneralNominalVersionedPlans231.private_models_iff,GeneralNominalVersionedPlans231.private_models_iff]
  rw [ordinary]
  rfl

theorem schema_eq (p : Plan roles) (r : Registry) (ctors) :
    GeneralNominalVersionedPlans231.emittedSchema (retag p r ctors) =
      GeneralNominalVersionedPlans231.emittedSchema p := by
  change GeneralNominalCenteredHeadMatSchemas.generated r.constructors _ _ =
    GeneralNominalCenteredHeadMatSchemas.generated p.packet.registry.constructors _ _
  rw [ctors]
  rfl

theorem childSite_eq (p : Plan roles) (r : Registry) (ctors) (clause : Clause)
    (valid : clause.Signature roles) :
    GeneralNominalVersionedFrame231.childSite (retag p r ctors) clause valid =
      GeneralNominalVersionedFrame231.childSite p clause valid := rfl

theorem childSchema_eq (p : Plan roles) (r : Registry) (ctors) (clause : Clause)
    (valid : clause.Signature roles) :
    GeneralNominalVersionedPlans231.childSchema (retag p r ctors) clause valid =
      GeneralNominalVersionedPlans231.childSchema p clause valid := by
  unfold GeneralNominalVersionedPlans231.childSchema
  change GeneralNominalCenteredHeadMatSchemas.generated r.constructors _ _ =
    GeneralNominalCenteredHeadMatSchemas.generated p.packet.registry.constructors _ _
  rw [ctors]
  rfl

theorem holds (p : Plan roles) (r : Registry) (ctors) (m : Assignment) :
    GeneralNominalVersionedPlans231.Holds (retag p r ctors) m ↔
      GeneralNominalVersionedPlans231.Holds p m := by
  unfold GeneralNominalVersionedPlans231.Holds GeneralNominalVersionedPlans231.Inputs
    GeneralNominalVersionedPlans231.Outputs
  rw [schema_eq]
  simp only [childSchema_eq]
  rfl

theorem plan_ne (p : Plan roles) (r : Registry) (ctors) (different : r ≠ p.packet.registry) :
    retag p r ctors ≠ p := by
  intro same
  exact different (congrArg (fun p : Plan roles => p.packet.registry) same)

end Yulang.GeneralRebaseCompiledRetag277
