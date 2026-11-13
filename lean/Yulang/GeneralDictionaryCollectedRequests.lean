import Yulang.GeneralDictionaryInstalledRequestProvenance

/-! Request collection on real Value histories. Constructors carry actual steps,
structural observations, and variable-free installation syntax, never a final
provenance or semantic request-validity premise. This restricted history does not
assert that all language-generated requests are variable-free or collected. -/
namespace Yulang.GeneralDictionaryCollectedRequests
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalMaterialization
open GeneralDictionaryRequestProvenance
variable {roles : Roles.RoleDecls}

/-- A finite operational history, allowing structural observations at intermediate
states and exact emitted request batches at actual installation transitions. -/
inductive Collected (registry : Registry) (root : Occurrence roles) :
    Tracked roles → List Request → Prop where
  | initial (context : GeneralNominalCandidates.Context)
      (source : GeneralNominalSourceFormation.InitialSource registry context root) :
      Collected registry root (GeneralNominalSupport.initial context root) []
  | observe {state batch} (prior : Collected registry root state batch) (extra : List Request)
      (observed : GeneralDictionaryObservedFiniteRequests.Observed state.current.context.state
        state.current.context.interpretation extra) :
      Collected registry root state (batch ++ extra)
  | advance {before after batch} (prior : Collected registry root before batch)
      (step : GeneralNominalValueSteps.Step registry root before after) :
      Collected registry root after batch
  | install {before batch} (prior : Collected registry root before batch)
      (packet : Packet roles) (support : List (Occurrence roles))
      (step : GeneralNominalValueSteps.Step registry root before
        (GeneralNominalValueSteps.install before packet support))
      (closed : (GeneralNominalPacketSupport.namedSchema packet).variables = []) :
      Collected registry root (GeneralNominalValueSteps.install before packet support)
        (batch ++ requests packet.context.state packet.registry packet.site.occurrence
          packet.declaration packet.checked packet.bindings)

theorem reachable {registry : Registry} {root : Occurrence roles} {state batch}
    (history : Collected registry root state batch) :
    B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state := by
  induction history with
  | initial context source => exact ⟨_,⟨context,source,rfl⟩,.refl⟩
  | observe _ _ _ ih => exact ih
  | advance _ step ih =>
    exact GeneralDictionaryRequestProvenanceTrace.reachable_trace registry root _ _ ih (.tail .refl step)
  | install _ _ _ step _ ih =>
    exact GeneralDictionaryRequestProvenanceTrace.reachable_trace registry root _ _ ih (.tail .refl step)

theorem supported {registry : Registry} {root : Occurrence roles} {state batch}
    (history : Collected registry root state batch) : Supported registry root state batch := by
  induction history with
  | initial => intro request member; cases member
  | observe prior extra observed ih =>
    apply (supported_append ..).mpr
    exact ⟨ih,supported_of_observed registry root _ _ (reachable prior) .refl extra observed⟩
  | advance _ step ih =>
    exact GeneralDictionaryRequestProvenanceTrace.supported_step registry root _ _ step _ ih
  | install _ packet support step closed ih =>
    exact GeneralDictionaryInstalledRequestProvenance.supported_install_append
      registry root _ packet support step _ ih closed

/-- A consumer may select, duplicate or reorder requests already collected. -/
theorem supported_subset {registry : Registry} {root : Occurrence roles} {state batch}
    (history : Collected registry root state batch) (selected : List Request)
    (included : ∀ request ∈ selected, request ∈ batch) :
    Supported registry root state selected :=
  fun request member => supported history request (included request member)

theorem shape {registry : Registry} {root : Occurrence roles} {state batch}
    (history : Collected registry root state batch) (selected : List Request)
    (included : ∀ request ∈ selected, request ∈ batch) :
    (generated state.current.context.state state.current.context.interpretation selected).variables = [] ∧
    (generated state.current.context.state state.current.context.interpretation selected).unknown = false :=
  GeneralDictionaryRequestProvenance.shape registry root state (reachable history) selected
    (supported_subset history selected included)

theorem models {registry : Registry} {root : Occurrence roles} {state batch}
    (history : Collected registry root state batch) (selected : List Request)
    (included : ∀ request ∈ selected, request ∈ batch)
    (declaration : Declaration) (capture : GeneralDeclarationDemands.Capture)
    (report : GeneralNominalRecursiveInspection.Report state.current.context.state)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    GeneralNominalMaterialization.Models state.current.context.state declaration capture report
      (generated state.current.context.state state.current.context.interpretation selected) model :=
  GeneralDictionaryRequestProvenance.models registry root state (reachable history) selected
    (supported_subset history selected included) declaration capture report model valid
end Yulang.GeneralDictionaryCollectedRequests
