import Yulang.GeneralStoppedProjectedTrace335
import Yulang.GeneralStoppedI61Endpoint335
import Yulang.GeneralStoppedCanonicalChoice335
import Yulang.GeneralStoppedDisplayLiteral335
import Yulang.GeneralStoppedDisplayHistory335

open Yulang
open GeneralStoppedDisplayProjection335 (initialOrdinary ordinary initial_read stopped_read actual_model)
open GeneralStoppedProjectedTrace335 (Trace source_slice)
open GeneralNominalExamples (registry displayRoot model state_models)
open GeneralRebaseDisplayFrame276 (before after after_models)

theorem display_trace : Trace registry displayRoot before after initialOrdinary ordinary :=
  .tail (.refl initial_read) GeneralRebaseDisplayStep276.actual_step stopped_read

example : GeneralDeclarativeGrowth327.Extends initialOrdinary ordinary :=
  GeneralStoppedProjectedTrace335.sources_preserved display_trace model ((after_models _).mpr (state_models true))

example :
    ∃ (p : GeneralDeclarativeOrigins321.Supported ordinary (fun _ => False)),
      Nonempty (GeneralDeclarativeWitnessHead334.Slice p) :=
  source_slice display_trace ((after_models _).mpr (state_models true)) (fun _ => False)

#print axioms Yulang.GeneralStoppedSourceRefinement335.normal_preserved
#print axioms Yulang.GeneralStoppedSourceRefinement335.preserves
#print axioms Yulang.GeneralStoppedSourceRefinement335.stopped_models
#print axioms Yulang.GeneralStoppedScalarStorage335.storage_of_inhabited
#print axioms Yulang.GeneralStoppedScalarStorage335.inhabited_refinement
#print axioms Yulang.GeneralStoppedProjectedTrace335.lowered_point_closed
#print axioms Yulang.GeneralStoppedProjectedTrace335.step_refinement
#print axioms Yulang.GeneralStoppedProjectedTrace335.sources_preserved
#print axioms Yulang.GeneralStoppedProjectedTrace335.source_slice
#print axioms display_trace
#print axioms Yulang.GeneralStoppedDisplayLiteral335.actual_success
#print axioms Yulang.GeneralStoppedDisplayCut335.not_same_literal_child
#print axioms Yulang.GeneralStoppedDisplayOriginal335.actual_success
#print axioms Yulang.GeneralStoppedDisplayHistory335.selected_not_installed
#print axioms Yulang.GeneralStoppedCanonicalChoice335.election_exact
#print axioms Yulang.GeneralStoppedI61Endpoint335.center_is_record
#print axioms Yulang.GeneralStoppedI61Endpoint335.Cut.actual_selected
#print axioms Yulang.GeneralStoppedI61Endpoint335.Cut.actual_repaired
