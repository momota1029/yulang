import Yulang.GeneralDeclarativeEndpointResidualLift336
import Yulang.GeneralDeclarativeEndpointChildModels336

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeEndpointResidualFixture336
open GeneralDeclarativeEndpointChildren336 (initial support root)
open GeneralDeclarativeEndpointChildModels336 (sourceModel source_valid)
open GeneralDeclarativeEndpointResidualLift336 (nonunique)
open GeneralDeclarativeEndpointResidual336 (peel)
open GeneralDeclarativeEndpointRecord336 (interp)
open GeneralDeclarativeWhere319 (InInterval)
open GeneralDeclarativeHead320 (Models)
open GeneralDeclarativeExampleSource320 (int)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans eqv_symm)
open GeneralDeclarativeWitnessCutDecl334 (arg)
open CommonNominalFullCarrier (Ty Equivalent exactEmpty emptyRecord mask)

def ResidualFits (v : Ty) : Prop :=
  InInterval exactEmpty emptyRecord v ∧ Equivalent (mask [7] v) (mask [7] (sourceModel 1).1)

theorem has_two_standalone :
    Models initial sourceModel ∧ ResidualFits exactEmpty ∧ ResidualFits (mask [7] exactEmpty) ∧
      ¬ Equivalent (mask [7] exactEmpty) exactEmpty := by
  obtain ⟨first,second,same,different⟩ := nonunique [7] 7 (by decide)
  have outer : Equivalent (mask [7] (sourceModel 1).1) (mask [7] exactEmpty) := by
    exact peel (key := 7) List.mem_cons_self [] (.primitive .exactEmpty []) .exactEnd
      (.variable 3) sourceModel
  exact ⟨source_valid,⟨first,eqv_symm outer⟩,⟨second,eqv_trans same (eqv_symm outer)⟩,different⟩

end Yulang.GeneralDeclarativeEndpointResidualFixture336
