import Yulang.GeneralDeclarativeI65I74NativeProducerInstall465
import Yulang.GeneralDeclarativeWitnessNativePipeline360
import Yulang.GeneralDeclarativeWitnessInheritedModeFixture357

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 10000000
namespace Yulang.GeneralDeclarativeI65.I72.NativeProducer465.ActualAudit
open Yulang.GeneralDeclarativeI65
open GeneralDeclarativeWitnessNativePipeline360
open GeneralDeclarativeWitnessInheritedModeFixture357 (table)
open GeneralDeclarativeWitnessNativeValue360 (Write)
open GeneralDeclarativeWitnessNativeInstall360 (Board)
open GeneralDeclarativeWitnessNativeRelease360 (ReleaseAuthority)
open GeneralDeclarativeHead320 (Equation)

private def sameOrdinary (r : Run false) (rows : List Origin) (routing : List GeneralDeclarativeI65.Alias)
    : GeneralDeclarativeI65.State :=
  ⟨⟨r.env,r.current.ordinary,[]⟩,table,rows,routing⟩

private def tests (r : Run false) : List Bool :=
  let actual := originalOfWrite r.output.write
  let route : List GeneralDeclarativeI65.Alias := [⟨107,101,[5]⟩]
  let good := sameOrdinary r [actual] route
  let noRoute := sameOrdinary r [actual] []
  let noRow := sameOrdinary r [] route
  let wrongRoute := sameOrdinary r [actual] [⟨107,101,[55]⟩]
  let other : Equation := ⟨999,.variable 999⟩
  let wrongPhase : GeneralDeclarativeI65.State :=
    {good with current := {good.current with ordinary := {good.current.ordinary with
      equations := good.current.ordinary.equations ++ [other]}}}
  [checkProducedOrigin (s := good) r.prepared gate authority (wire false) 3 107 0,
    checkProducedOrigin (s := good) r.prepared gate authority (wire false) 3 101 0,
    checkProducedOrigin (s := good) r.prepared gate authority (wire false) 3 107 1,
    checkProducedOrigin (s := noRow) r.prepared gate authority (wire false) 3 107 0,
    checkProducedOrigin (s := noRoute) r.prepared gate authority (wire false) 3 107 0,
    checkProducedOrigin (s := wrongRoute) r.prepared gate authority (wire false) 3 107 0,
    checkProducedOrigin (s := wrongPhase) r.prepared gate authority (wire false) 3 107 0,
    checkProducedOrigin (s := good) r.prepared gate (⟨[]⟩ : ReleaseAuthority) (wire false) 3 107 0,
    checkProducedOrigin (s := good) r.prepared gate authority (wire false) 2 107 0,
    checkProducedOrigin (s := good) r.prepared r.current.board authority (wire false) 3 107 0]

theorem actual_compiler_phase_requires_literal_retained_ordinal_route_and_grant :
    (run false).map tests = some [true,true,false,false,false,false,false,false,false,false] := by
  decide +kernel

#print axioms actual_compiler_phase_requires_literal_retained_ordinal_route_and_grant
end Yulang.GeneralDeclarativeI65.I72.NativeProducer465.ActualAudit
