import Yulang.GeneralLiveCompoundProposedRepair316
import Yulang.GeneralVersionedEndpointSourceKey315

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralWhereVersionCompiler317
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries GeneralNominalCenters
open GeneralDeclarationDemands
open GeneralVersionedEndpointAddress315 (Side atCell)
open GeneralNominalCenteredHeadMatExpressions (translate)
open GeneralNominalCenteredHeadMatSchemas (generated emissionRequests)
open GeneralNominalVersionedFrame231 (capture)
open GeneralNominalMaterialization (rootRequests)

def args (p : Plan roles) (clause : Clause) : Fin (roles clause.role).arity → GeneralSourceState.Interval :=
  fun i =>
    let prior := ((GeneralNominalVersionedFrame231.frame p.packet).allocation p.packet.declaration.id clause).arguments i
    match clause.arguments[i.val]? with
    | none => prior
    | some pat =>
      match translate p.packet.registry.constructors p.packet.context.interpretation pat with
      | none => prior
      | some code => (atCell p .lower clause.id i.val code,atCell p .upper clause.id i.val code)

def allocation (p : Plan roles) (clause : Clause) : Allocation roles clause :=
  ⟨args p clause,((GeneralNominalVersionedFrame231.frame p.packet).allocation p.packet.declaration.id clause).outputs⟩

def emit (p : Plan roles) (clause : Clause) (proof : clause.Signature roles) : Emission roles :=
  GeneralDeclarationDemands.emit p.packet.site.occurrence.identity p.packet.declaration clause proof
    (capture p.packet) (allocation p clause)

def child (p : Plan roles) (clause : Clause) (proof : clause.Signature roles) : Site roles :=
  ⟨GeneralDictionaryEmissionPlans.occurrence (GeneralNominalVersionedFrame231.frame p.packet) (emit p clause proof),
   fun i => GeneralNominalVersionedFrame231.emittedCenter p clause.id i.val
     (clause.arguments[i.val]'(by rw [proof.1]; exact i.isLt))⟩

def emissions (p : Plan roles) :=
  GeneralCanonicalChildOrder.canonicalEmit p.packet.site.occurrence.identity p.packet.declaration p.packet.checked
    (capture p.packet) (allocation p)

def schema (p : Plan roles) :=
  generated p.packet.registry.constructors p.packet.context.interpretation
    (rootRequests p.packet.declaration p.packet.site.occurrence ++ (emissions p).flatMap emissionRequests)

def children (p : Plan roles) := (emissions p).map
  (GeneralDictionaryEmissionPlans.occurrence (GeneralNominalVersionedFrame231.frame p.packet))

theorem child_owner (p : Plan roles) (clause : Clause) (proof : clause.Signature roles) :
    (child p clause proof).occurrence.identity = (GeneralNominalVersionedFrame231.childSite p clause proof).occurrence.identity := rfl

theorem child_role (p : Plan roles) (clause : Clause) (proof : clause.Signature roles) :
    (child p clause proof).occurrence.demand.role = clause.role := rfl

theorem child_outputs (p : Plan roles) (clause : Clause) (proof : clause.Signature roles) :
    (child p clause proof).occurrence.demand.outputs =
      (GeneralNominalVersionedFrame231.childSite p clause proof).occurrence.demand.outputs := rfl

theorem child_center (p : Plan roles) (clause : Clause) (proof : clause.Signature roles)
    (i : Fin (roles clause.role).arity) :
    (child p clause proof).center i = (GeneralNominalVersionedFrame231.childSite p clause proof).center i := rfl

theorem original_bare (p : Plan roles) (clause : Clause) (proof : clause.Signature roles)
    (i : Fin (roles clause.role).arity) (named : normalize
      (clause.arguments[i.val]'(by rw [proof.1]; exact i.isLt)) = .var name) :
    (child p clause proof).occurrence.demand.arguments i =
      (GeneralNominalVersionedFrame231.childSite p clause proof).occurrence.demand.arguments i := by
  change GeneralDeclarationDemands.inputInterval (capture p.packet) _ _ =
    GeneralDeclarationDemands.inputInterval (capture p.packet) _ _
  simp [GeneralDeclarationDemands.inputInterval,named]

end Yulang.GeneralWhereVersionCompiler317
