import Yulang.GeneralDeclarativeWitnessNativeValue360

namespace Yulang.GeneralDeclarativeI65.I72.PreparationAddress467
open GeneralDeclarativeWitnessNativeValue360
open GeneralDeclarativeWitnessNativePreparation360 (Prepared)
open GeneralDeclarativeWitnessAssociatedDescriptor359 (Wire)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarativeWitnessScopedBindings359 (FrameKey slots)
open GeneralDeclarativeDemand320 (Demand)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeHead320 (Models)

theorem compile_none_at_unrequested_ordinal
    {e f d l} (p : Prepared e f d l) (table : _)
    (w : Wire) (version : Nat) (absent : d.outputs[w.ordinal]? = none) :
    compile p table w version = none := by
  cases actual : compile p table w version with
  | none => rfl
  | some got =>
    have existsOutput := got.supplied.indexed
    rw [absent] at existsOutput
    contradiction

theorem prepared_without_outputs_cannot_produce_native_value
    {e f d l} (p : Prepared e f d l) (table : _)
    (w : Wire) (version : Nat) (noOutputs : d.outputs = []) :
    compile p table w version = none :=
  compile_none_at_unrequested_ordinal p table w version (by simp [noOutputs])

theorem compilation_returns_exact_requested_associated_output_address
    {e f d l} {p : Prepared e f d l} {table w version}
    (got : @Compiled e f d l p table w version) :
    d.outputs[w.ordinal]? = some got.supplied.requested ∧
    got.write.address.owner = owner p version ∧
    got.write.address.declarationOrdinal = f.sourceOrdinal ∧
    got.write.address.outputOrdinal = w.ordinal ∧
    got.write.address.name = got.supplied.requested.name ∧
    got.write.address.target = got.supplied.requested.target ∧
    got.write.address.sourceEquation = w.sourceEquation :=
  ⟨got.supplied.indexed,rfl,rfl,rfl,rfl,got.supplied.fixed.symm,rfl⟩

theorem exact_compiled_address_at_prepared_source_and_model
    {e f d l} {p : Prepared e f d l} {table w version}
    (got : @Compiled e f d l p table w version) (m : Assignment)
    (fit : Models p.stage m) :
    e.source.declarations[got.write.address.declarationOrdinal]? = some got.supplied.declaration ∧
    d.outputs[got.write.address.outputOrdinal]? = some got.supplied.requested ∧
    FromCenters (slots [p.captures] f) w.route got.write.code ∧
    Models l.named m := by
  refine ⟨?_, got.supplied.indexed, (emitted_exact.mp got.produced),?_⟩
  · change e.source.declarations[f.sourceOrdinal]? = some got.supplied.declaration
    rw [got.sourceSame]
    exact p.authored
  · exact (GeneralDeclarativeWitnessNativePreparation360.same_model_of_prepared p m fit).1

end Yulang.GeneralDeclarativeI65.I72.PreparationAddress467
