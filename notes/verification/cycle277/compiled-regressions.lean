import Yulang.GeneralRebaseCompiledObservables277
import Yulang.GeneralRebaseFiniteCodeAcc277

set_option maxRecDepth 24000
set_option maxHeartbeats 9000000
namespace Yulang.Cycle277Regression
open GeneralRebaseCompiledDisplay277 (compiled after)
open GeneralRebaseCompiledPublic277 (Public Model decode)
open GeneralRebaseCompiledExecutor277 (raw)
open GeneralRebaseDisplayExecutor276 (run)
open GeneralRebaseDisplayPayload276 (accepts)
open GeneralRebaseInstallGrowth277 (reserveBudget centerBudget)
open GeneralNominalExamples (registry displayRoot)
open GeneralDeclarationExamples (roles)
open GeneralNominalVersionedJournal232 (Models)

def realEndpoints : Public :=
  (CommonNominalFullCarrier.nominal 0 [.inl (.base .int)], .base .int)

example : Model realEndpoints :=
  ⟨⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩,_,
   ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩,
   ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩⟩

example : Models (raw .settled) (decode realEndpoints) ∧
    (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Evidence registry
      (raw .settled) (decode realEndpoints) displayRoot (.node 1 [.node 3 []]) :=
  GeneralRebaseCompiledExecutor277.readback 1 .settled _ realEndpoints (by
    exact ⟨⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩,_,
       ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩,
       ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩⟩) rfl

#eval reserveBudget compiled
#eval centerBudget compiled
#eval (run 1).isSome
#eval (run 3).isNone
#eval accepts .parent (.node 1 [.node 3 []])
#eval accepts .parent (.node 1 [.node 3 [],.node 3 []])
#eval accepts .child (.node 3 [])

end Yulang.Cycle277Regression
