import Yulang.GeneralDeclarativeI65I74NativeProducerMergedReceipt465

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.NativeProducer465
open Yulang.GeneralDeclarativeI65
open Checker408 (Problem)
open PreparedDeclarations463
open PhysicalVisit463.IssuedProjection464 (logicalBeforeHop)
open GeneralDeclarativeWitnessAssociatedDescriptor359 (Wire)
open GeneralDeclarativeWitnessNativePreparation360 (Prepared)
open GeneralDeclarativeWitnessNativeValue360 (Compiled compile)
open GeneralDeclarativeWitnessNativeInstall360 (Board World Committed install current check_exact)
open GeneralDeclarativeWitnessNativeRelease360 (ReleaseAuthority)
open NamedProjection464 (exactOrdinaryState exact_ordinary_snapshot_iff)

structure CompiledFieldData (p : Problem) where
  compiledRequest : Wire
  version : Nat
  selectedHop : Nat
  originOrdinal : Nat
  field : HeadFieldWire p

/-- Glue only an existing compiler-write phase to the existing field
receipt. The issued origin does not come from constructing the field
wire, and the older resolver is not passed a new candidate branch. -/
def readCompilerOwnedField {p : Problem} {frame demand layout}
    (ready : Prepared p.state.core.current.environment frame demand layout)
    (inBoard : Board) (grant : ReleaseAuthority) (tab : CheckedTable p.state.core.current)
    (w : CompiledFieldData p) : Option HeadFieldReceipt := do
  let literal ← compile ready p.state.core.modes w.compiledRequest w.version
  let stage ← install ready literal inBoard
  if same : exactOrdinaryState stage.ordinary p.state.core.current.ordinary = true then
    let phase : CheckedPhase p.state.core := ⟨stage,(exact_ordinary_snapshot_iff ..).mp same,grant⟩
    readSingleCandidatePhaseField (phase := phase) tab
      ⟨w.field,⟨w.selectedHop,w.originOrdinal,literal.write⟩⟩
  else none

def ActualCompilerOwnerField {p : Problem} {frame demand layout}
    (ready : Prepared p.state.core.current.environment frame demand layout)
    (inBoard : Board) (grant : ReleaseAuthority) (tab : CheckedTable p.state.core.current)
    (wire : Wire) (version hop ordinal : Nat) (r : HeadFieldReceipt) : Prop :=
  ∃ literal : Compiled ready p.state.core.modes wire version,
    Committed inBoard literal.write ∧
    ∃ same : ready.stage = p.state.core.current.ordinary,
      ExactSingleCandidatePhaseField ⟨current ready inBoard literal.write,same,grant⟩ tab
        ⟨hop,ordinal,literal.write⟩ r

theorem actual_existing_compiler_and_field_have_finite_same_phase_witness
    {p : Problem} {frame demand layout}
    (ready : Prepared p.state.core.current.environment frame demand layout)
    (inBoard : Board) (grant : ReleaseAuthority) (tab : CheckedTable p.state.core.current)
    (wire : Wire) (version hop ordinal : Nat) (r : HeadFieldReceipt) :
    ActualCompilerOwnerField ready inBoard grant tab wire version hop ordinal r ↔
    ∃ f, readCompilerOwnedField ready inBoard grant tab ⟨wire,version,hop,ordinal,f⟩ = some r := by
  constructor
  · rintro ⟨literal,commit,same,field⟩
    have compiled := actual_native_compilation_replays_from_independent_described_code literal
    have installed := (compiler_install_exactly_commits_given_actual_source literal inBoard).mpr commit
    have eq : exactOrdinaryState (current ready inBoard literal.write).ordinary
        p.state.core.current.ordinary = true := (exact_ordinary_snapshot_iff ..).mpr same
    obtain ⟨w,hit,found⟩ := (exact_single_candidate_phase_field_has_finite_wire ..).mp field
    cases w with
    | mk observed hard =>
      dsimp at hit
      subst hard
      exact ⟨observed,by simpa [readCompilerOwnedField,compiled,installed,eq,Option.bind] using found⟩
  · rintro ⟨w,read⟩
    cases compiler : compile ready p.state.core.modes wire version with
    | none => simp [readCompilerOwnedField,compiler,Option.bind] at read
    | some literal =>
      by_cases commit : Committed inBoard literal.write
      · have installed := (compiler_install_exactly_commits_given_actual_source literal inBoard).mpr commit
        by_cases same : ready.stage = p.state.core.current.ordinary
        · have eq : exactOrdinaryState (current ready inBoard literal.write).ordinary
                  p.state.core.current.ordinary = true := (exact_ordinary_snapshot_iff ..).mpr same
          have inspected : readSingleCandidatePhaseField
              (phase := ⟨current ready inBoard literal.write,same,grant⟩) tab
              ⟨w,⟨hop,ordinal,literal.write⟩⟩ = some r := by
            simpa [readCompilerOwnedField,compiler,installed,eq,Option.bind] using read
          exact ⟨literal,commit,same,
            (exact_single_candidate_phase_field_has_finite_wire ..).mpr ⟨_,rfl,inspected⟩⟩
        · have not : exactOrdinaryState (current ready inBoard literal.write).ordinary
                  p.state.core.current.ordinary ≠ true := fun eq => same
                    ((exact_ordinary_snapshot_iff ..).mp eq)
          simp [readCompilerOwnedField,compiler,installed,not,Option.bind] at read
      · have no : GeneralDeclarativeWitnessNativeInstall360.check inBoard literal.write ≠ true :=
          fun h => commit (check_exact.mp h)
        simp [readCompilerOwnedField,compiler,install,no,Option.bind] at read

theorem a_compiled_owner_for_the_exact_report_is_genuinely_released_and_located
    {p : Problem} {frame demand layout}
    (ready : Prepared p.state.core.current.environment frame demand layout)
    (base : Board) (grant : ReleaseAuthority) (tab : CheckedTable p.state.core.current)
    (w : CompiledFieldData p) (r : HeadFieldReceipt)
    (ok : readCompilerOwnedField ready base grant tab w = some r) :
    ∃ logical,
      ProducedAndPlaced ready base grant w.compiledRequest w.version logical w.originOrdinal ∧
        ∃ c, p.root.demand.arguments[r.authored.headArgument]? = some c ∧
          logicalBeforeHop c.lower r.path w.selectedHop = some logical := by
  obtain ⟨write,committed,same,actual⟩ :=
    (actual_existing_compiler_and_field_have_finite_same_phase_witness ..).mpr ⟨w.field,ok⟩
  obtain ⟨cap,logical,_,_,capAt,place,_,_,_,_,needed⟩ := actual.2.2
  exact ⟨logical,⟨write,committed,same,needed⟩,cap,capAt,place⟩

end Yulang.GeneralDeclarativeI65.I72.NativeProducer465
