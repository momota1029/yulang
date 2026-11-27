import Yulang.GeneralDeclarativeI65I74NativeProducerNoField465
namespace Yulang.GeneralDeclarativeI65.I72.NativeProducer465
open Checker408 (Problem)
open PreparedDeclarations463
open GeneralDeclarativeWitnessNativePreparation360 (Prepared)
open GeneralDeclarativeWitnessNativeValue360 (compile)
open GeneralDeclarativeWitnessNativeInstall360 (Board install)
open GeneralDeclarativeWitnessNativeRelease360 (ReleaseAuthority)
open NamedProjection464 (exactOrdinaryState)

theorem compiler_owned_field_needs_an_origin_outside_the_native360_image
    {p : Problem} {frame demand layout}
    (ready : Prepared p.state.core.current.environment frame demand layout)
    (board : Board) (grant : ReleaseAuthority)
    (tab : CheckedTable p.state.core.current)
    (w : CompiledFieldData p)
    (only : InlineBoundary.OnlyNative360 p.state.core) :
    readCompilerOwnedField ready board grant tab w = none := by
  unfold readCompilerOwnedField
  cases c : compile ready p.state.core.modes w.compiledRequest w.version with
  | none => rfl
  | some emitted =>
    change (do
      let stage ← install ready emitted board
      if same : exactOrdinaryState stage.ordinary p.state.core.current.ordinary = true then
        readSingleCandidatePhaseField (phase := ⟨stage,(NamedProjection464.exact_ordinary_snapshot_iff ..).mp same,grant⟩)
          tab ⟨w.field,⟨w.selectedHop,w.originOrdinal,emitted.write⟩⟩
      else none) = none
    cases i : install ready emitted board with
    | none => rfl
    | some stage =>
      dsimp only [Bind.bind, Option.bind]
      split
      · unfold readSingleCandidatePhaseField
        split
        · unfold readFieldWithPhaseOwner
          simp [InlineBoundary.no_prechecked_field_receipt_on_a_sole_native360_origin_list only]
        · rfl
      · rfl
end Yulang.GeneralDeclarativeI65.I72.NativeProducer465
