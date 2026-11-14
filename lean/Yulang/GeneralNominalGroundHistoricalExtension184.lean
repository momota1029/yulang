import Yulang.GeneralNominalOverlapProvenance184
import Yulang.GeneralNominalOriginAgreement183

/-! The actual reachable journal produces all historical overlap witnesses.
The residual criterion retains candidate-versus-historical origin agreement,
not an assumed global extension or EvidenceNode conclusion. -/
namespace Yulang.GeneralNominalGroundHistoricalExtension184
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralNominalCenteredGroundBoundary (groundBoundary)
open GeneralNominalRecursiveInspection (Origin Observes)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredModelExtension (originSource)
open GeneralNominalModeLedger181 (fullSources)
open GeneralNominalSupportProvenance182 (ActualBinder)
open GeneralNominalOriginTerms (Same)
open CommonNominalFullCarrier
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles} {state : State roles}

def BinderNames (state : State roles) (names : Fin count → Nat) : Prop :=
  ∀ index, ∃ invocation declaration owner position,
    names index = fresh state.erased.current.context.state.seed invocation declaration 8 owner position

theorem historical_witnesses
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (names : Fin count → Nat) (allocated : BinderNames state names) :
    ∃ historical : Fin count → Origin,
      ∀ index, names index ∈ fullSources state → ActualBinder state (names index) (historical index) := by
  classical
  have witnessed index : ∃ origin, names index ∈ fullSources state → ActualBinder state (names index) origin := by
    by_cases member : names index ∈ fullSources state
    · obtain ⟨invocation,declaration,owner,position,equal⟩ := allocated index
      have present : fresh state.erased.current.context.state.seed invocation declaration 8 owner position ∈
          fullSources state := equal ▸ member
      obtain ⟨origin,actual⟩ := GeneralNominalOverlapProvenance184.ground_overlap_actual reachable present
      exact ⟨origin,fun _ => equal.symm ▸ actual⟩
    · exact ⟨.source (names index),fun impossible => False.elim (member impossible)⟩
  exact ⟨fun index => Classical.choose (witnessed index),fun index => Classical.choose_spec (witnessed index)⟩

theorem ground_historical_criterion
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (arguments : Fin count → NominalArgument)
    (allocated : BinderNames state (fun index => (arguments index).argument.center))
    (previous : Assignment) (valid : Models state previous)
    (linked : ∀ i, (arguments i).argument.endpoints.1 ∈ fullSources state ∧
      (arguments i).argument.endpoints.2 ∈ fullSources state ∧ originSource (arguments i).origin ∈ fullSources state) :
    ∃ historical : Fin count → Origin,
      (∀ index, (arguments index).argument.center ∈ fullSources state →
        ActualBinder state (arguments index).argument.center (historical index)) ∧
      ((∃ extended, Models state extended ∧
        (∀ name ∈ fullSources state, extended name = previous name) ∧ ∀ i, (arguments i).Holds extended) ↔
      (∀ i, ∃ actual, Observes previous (arguments i).origin actual) ∧
      (∀ i actual, Observes previous (arguments i).origin actual →
        GeneralNominalCaptureMerges.Fits previous (arguments i).argument.endpoints actual) ∧
      (∀ i j first last, (arguments i).argument.center = (arguments j).argument.center →
        Observes previous (arguments i).origin first → Observes previous (arguments j).origin last → Equivalent first last) ∧
      (∀ i, (arguments i).argument.center ∈ fullSources state → Same previous (arguments i).origin (historical i))) := by
  obtain ⟨historical,provenance⟩ := historical_witnesses reachable _ allocated
  exact ⟨historical,provenance,
    GeneralNominalOriginAgreement183.extension_iff_historical arguments historical previous valid linked provenance⟩

end Yulang.GeneralNominalGroundHistoricalExtension184
