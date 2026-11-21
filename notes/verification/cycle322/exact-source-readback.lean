import Yulang.GeneralDeclarativeEmissionErasure322
import Yulang.GeneralDeclarativeProducerFixture322
import Yulang.GeneralDeclarativeOverwriteFixture322

namespace Yulang.C322Readback

open GeneralDeclarationExamples (wrap roles wrap_checked)
open GeneralDeclarativeExistingFixture322 (state equations parentCapture)
open GeneralDeclarativeEmissionFixture322 (names place)
open GeneralDeclarativeEmissionErasure322 (Requests forgetCenter oldDemand oldPlacement)
open GeneralDeclarativeEmissionForest322 (children)
open GeneralDeclarativeProducerFixture322 (actual_map occurrence pool)
open GeneralDeclarativeOrdinaryProducer322 (namesOf)

abbrev expected : List Requests := [(2,[(3,3)],[⟨1,5⟩])]

theorem exact_old_source_emitter :
    (GeneralDeclarationDemands.emitAll 20 wrap wrap_checked.signature names.old
      (oldPlacement (roles := roles) place)).map (fun e => oldDemand e.demand) = expected := rfl

theorem exact_centered_source_emitter :
    (children wrap names place).map forgetCenter = expected :=
  (GeneralDeclarativeEmissionErasure322.all_source wrap wrap_checked.signature names place 20).trans
    exact_old_source_emitter

theorem same_binder_placement :
    children wrap (namesOf state [occurrence] pool parentCapture) place = children wrap names place := by
  have same : namesOf state [occurrence] pool parentCapture = names := by
    unfold namesOf
    change GeneralDeclarativeSourceEmission322.Names.mk
      (namesOf state [occurrence] pool parentCapture).input
      (fun binder => ((namesOf state [occurrence] pool parentCapture).input binder).center) = names
    rw [actual_map]
  rw [same]

#print axioms exact_old_source_emitter
#print axioms exact_centered_source_emitter
#print axioms same_binder_placement

end Yulang.C322Readback
