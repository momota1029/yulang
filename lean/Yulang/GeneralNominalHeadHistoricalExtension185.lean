import Yulang.GeneralNominalHeadFullOverlap185
import Yulang.GeneralNominalHeadLedgerExtension182

/-! Exact finite extension criterion for actual WF states with historical
witnesses produced by reachability, including both effect-ledger components.
Observation existence, bounds, equal-center coherence and candidate/history
agreement remain explicit. This is not general candidate installation. -/
namespace Yulang.GeneralNominalHeadHistoricalExtension185
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects
open GeneralNominalCenteredHeadWFBoundary (boundary)
open GeneralNominalHeadLedgerFrame182 (fullSources)
open GeneralNominalHeadFullOverlap185 (BinderNames)
open GeneralNominalRecursiveInspection
open GeneralNominalOriginTerms (Same same_trans same_symm)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredModelExtension (originSource)
open CommonNominalFullCarrier
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}
variable {model : Assignment} {historical candidate : Origin} {name : Nat}

theorem historical_agreement_iff (recorded : Same model historical (.source name)) :
    ((∃ value, Observes model candidate value) ∧
      ∀ value, Observes model candidate value → Equivalent value (model name).1) ↔
    Same model candidate historical := by
  constructor
  · rintro ⟨observed,readback⟩
    apply fun named => same_trans named (same_symm recorded)
    refine ⟨observed,⟨_,.source _⟩,?_⟩
    intro value other seen named
    cases named
    exact readback value seen
  · intro equal
    have named := same_trans equal recorded
    exact ⟨named.1,fun value seen => named.2.2 value (model name).1 seen (.source _)⟩

theorem wf_extension_iff_historical
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (arguments : Fin count → NominalArgument)
    (allocated : BinderNames state (fun index => (arguments index).argument.center))
    (previous : Assignment) (valid : Models state previous)
    (linked : ∀ i, (arguments i).argument.endpoints.1 ∈ fullSources state ∧
      (arguments i).argument.endpoints.2 ∈ fullSources state ∧ originSource (arguments i).origin ∈ fullSources state) :
    ∃ historical : Fin count → Origin,
      (∀ i, (arguments i).argument.center ∈ fullSources state →
        ∀ model, Models state model → Same model (historical i) (.source (arguments i).argument.center)) ∧
      ((∃ extended, Models state extended ∧
        (∀ name ∈ fullSources state, extended name = previous name) ∧ ∀ i, (arguments i).Holds extended) ↔
      (∀ i, ∃ actual, Observes previous (arguments i).origin actual) ∧
      (∀ i actual, Observes previous (arguments i).origin actual →
        GeneralNominalCaptureMerges.Fits previous (arguments i).argument.endpoints actual) ∧
      (∀ i j first last, (arguments i).argument.center = (arguments j).argument.center →
        Observes previous (arguments i).origin first → Observes previous (arguments j).origin last → Equivalent first last) ∧
      (∀ i, (arguments i).argument.center ∈ fullSources state → Same previous (arguments i).origin (historical i))) := by
  obtain ⟨historical,recorded⟩ := GeneralNominalHeadFullOverlap185.wf_historical_witnesses reachable
    (fun index => (arguments index).argument.center) allocated
  refine ⟨historical,recorded,?_⟩
  rw [GeneralNominalHeadLedgerExtension182.extension_iff state arguments previous valid linked]
  constructor
  · rintro ⟨observed,bounds,coherent,overlap⟩
    refine ⟨observed,bounds,coherent,?_⟩
    intro index present
    exact (historical_agreement_iff (recorded index present previous valid)).mp
      ⟨observed index,fun value seen => overlap index value present seen⟩
  · rintro ⟨observed,bounds,coherent,agreement⟩
    refine ⟨observed,bounds,coherent,?_⟩
    intro index value present seen
    exact ((historical_agreement_iff (recorded index present previous valid)).mpr (agreement index present)).2 value seen

end Yulang.GeneralNominalHeadHistoricalExtension185
