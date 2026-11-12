import Yulang.GeneralNominalCaptureAnchors
import Yulang.GeneralNominalSourceFormation

/-! Source readback as interval containment, retaining actual observation
origins. This is model-sound before commitment under BranchModels and in every
journal model after commitment. It does not replace the missing finite-pattern
size correspondence with an endpoint equality. -/
namespace Yulang.GeneralNominalSourceReadback

open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalRecursiveInspection GeneralNominalRecursiveCandidates

abbrev input (packet : Packet roles) (name : Nat) : GeneralSourceState.Interval :=
  (GeneralNominalAllocation.capture packet.context.state packet.registry packet.site.occurrence.identity
    packet.declaration.id packet.bindings).inputs name

theorem packet_capture_exact (packet : Packet roles) (model : GeneralNominalCommonBridge.Assignment)
    (valid : packet.Holds model) (name : Nat) (declared : name ∈ packet.declaration.inputNames)
    (nonempty : GeneralNominalAllocation.occurrences packet.bindings name ≠ [])
    (actual : CommonNominalFullCarrier.Ty) :
    GeneralNominalCaptureMerges.Fits model (input packet name) actual ↔
      ∀ bounds ∈ GeneralNominalAllocation.occurrences packet.bindings name,
        GeneralNominalCaptureMerges.Fits model bounds actual :=
  GeneralNominalCaptureMerges.propagated_capture_exact packet.context.state packet.registry
    packet.site.occurrence.identity packet.declaration packet.bindings model
    ((GeneralNominalState.extend_models ..).mp valid.1).1 name declared nonempty actual

theorem committed_capture_exact (state : State roles) (packet : Packet roles)
    (committed : GeneralNominalCycleSteps.Committed state packet)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model)
    (name : Nat) (declared : name ∈ packet.declaration.inputNames)
    (nonempty : GeneralNominalAllocation.occurrences packet.bindings name ≠ [])
    (actual : CommonNominalFullCarrier.Ty) :
    GeneralNominalCaptureMerges.Fits model (input packet name) actual ↔
      ∀ bounds ∈ GeneralNominalAllocation.occurrences packet.bindings name,
        GeneralNominalCaptureMerges.Fits model bounds actual :=
  packet_capture_exact packet model (committed.1 model valid) name declared nonempty actual

theorem stable_capture_exact (registry : Registry) (state : State roles) (root : Occurrence roles)
    (stable : GeneralNominalCycleSteps.Stable registry state root) (packet : Packet roles)
    (same : packet.site.occurrence = root) (enabled : GeneralNominalCycleSteps.Installable registry state packet)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model)
    (name : Nat) (declared : name ∈ packet.declaration.inputNames)
    (nonempty : GeneralNominalAllocation.occurrences packet.bindings name ≠ [])
    (actual : CommonNominalFullCarrier.Ty) :
    GeneralNominalCaptureMerges.Fits model (input packet name) actual ↔
      ∀ bounds ∈ GeneralNominalAllocation.occurrences packet.bindings name,
        GeneralNominalCaptureMerges.Fits model bounds actual :=
  committed_capture_exact state packet ((stable root .root).2.1 packet same enabled)
    model valid name declared nonempty actual

theorem variable_child_origin (registry : Registry) (context : Context) (root : Occurrence roles)
    (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration)
    (bounds : List (GeneralNominalInspection.Bounds context.state))
    (model : GeneralNominalCommonBridge.Assignment) (models : BranchModels registry context root declaration checked bounds model)
    (capture : Capture context.state) (member : capture ∈ (report context declaration bounds).captures)
    (declared : capture.name ∈ declaration.inputNames) (origin : Origin) (recorded : capture.origin = some origin)
    (clause : Clause) (valid : clause.Signature roles) (index : Fin (roles clause.role).arity)
    (pattern : GeneralDeclarationPatterns.normalize (clause.arguments[index.val]'(by rw [valid.1]; exact index.isLt)) = .var capture.name) :
    let child := GeneralDeclarationDemands.childDemand declaration clause valid
      (GeneralNominalAllocation.capture context.state registry root.identity declaration.id
        (bindings context.state (report context declaration bounds)))
      (GeneralNominalAllocation.allocation context.state registry root.identity declaration.id clause)
    (∃ actual, Observes model origin actual) ∧
      ∀ actual, Observes model origin actual → GeneralNominalCaptureMerges.Fits model (child.arguments index) actual :=
  GeneralNominalCapturedChildOrigins.captured_child_origin registry context root declaration checked bounds model models
    capture member declared origin recorded
    (GeneralNominalCaptureAnchors.report_anchored context declaration bounds capture member origin recorded)
    clause valid index pattern

end Yulang.GeneralNominalSourceReadback
