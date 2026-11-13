import Yulang.GeneralDictionary170NamedSpine
import Yulang.GeneralDictionary169NamedPersistence

/-! Finite nominal-input/named-output certificates transport through ordinary
context extension. The physical slots, spine queries and ordered requests are
preserved; this does not cover descriptor-changing refresh or discover coverage. -/
namespace Yulang.GeneralDictionary171NamedSpinePersistence
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalRecursiveCandidates
open GeneralDictionaryOrdinaryTransport GeneralNominalSaturationState GeneralNominalRecursiveInspection
open GeneralDictionary170NamedSpine
variable {roles : Roles.RoleDecls}

/-- Only constraints and reservation/allocation ledgers grow. No Evidence,
Instance, model existence, or semantic selection is a transport premise. -/
def shape (registry : Registry) (context : Context) (reserved atoms allocated)
    {root : Occurrence roles} {declaration : Declaration}
    {checked : DeclarationChecked registry.constructors roles declaration}
    (certificate : Shape registry context root declaration checked) :
    Shape registry (extend context reserved atoms allocated) root declaration checked where
  terminal := certificate.terminal
  role := certificate.role
  slot := certificate.slot
  arity := certificate.arity
  names := certificate.names
  distinct := certificate.distinct
  inputs := certificate.inputs
  bounds := certificate.bounds
  spine := GeneralDictionary169LeafPersistence.spine context.state reserved atoms allocated certificate.spine
  query := by
    rw [GeneralDictionary169LeafPersistence.spine_query]
    exact certificate.query
  located := certificate.located
  defined := certificate.defined
  observed := by
    rw [candidate_report_extended,bindings_report]
    exact GeneralDictionary169NamedPersistence.observed context.state reserved atoms allocated
      context.interpretation _ certificate.observed

/-- Exact ordered requests are preserved, not merely their model meanings. -/
theorem requests_eq (registry : Registry) (context : Context) (reserved atoms allocated)
    {root : Occurrence roles} {declaration : Declaration}
    {checked : DeclarationChecked registry.constructors roles declaration}
    (certificate : Shape registry context root declaration checked) :
    GeneralNominalMaterialization.requests
      (extend context reserved atoms allocated).state registry root declaration checked
      (bindings (extend context reserved atoms allocated).state
        (report (extend context reserved atoms allocated) declaration
          [(certificate.slot,certificate.slot)])) =
    GeneralNominalMaterialization.requests context.state registry root declaration checked
      (bindings context.state (report context declaration [(certificate.slot,certificate.slot)])) := by
  rw [candidate_report_extended,bindings_report]
  rfl

/-- The transported certificate refers to the identical physical root slot. -/
theorem shape_slot (registry : Registry) (context : Context) (reserved atoms allocated)
    {root : Occurrence roles} {declaration : Declaration}
    {checked : DeclarationChecked registry.constructors roles declaration}
    (certificate : Shape registry context root declaration checked) :
    (shape registry context reserved atoms allocated certificate).slot = certificate.slot := rfl

/-- The entire finite spine query, including parameter order, is unchanged. -/
theorem shape_query (registry : Registry) (context : Context) (reserved atoms allocated)
    {root : Occurrence roles} {declaration : Declaration}
    {checked : DeclarationChecked registry.constructors roles declaration}
    (certificate : Shape registry context root declaration checked) :
    (shape registry context reserved atoms allocated certificate).spine.query = certificate.spine.query :=
  GeneralDictionary169LeafPersistence.spine_query context.state reserved atoms allocated certificate.spine

/-- Arbitrary ordinary context extensions retain a structural certificate.
The existential is over syntax/state witnesses, not over semantic Evidence. -/
theorem extension {registry : Registry} {before after : Context}
    {root : Occurrence roles} {declaration : Declaration}
    {checked : DeclarationChecked registry.constructors roles declaration}
    (growth : GeneralDictionaryOrdinaryTrace.Extension before after)
    (certificate : Shape registry before root declaration checked) :
    Nonempty (Shape registry after root declaration checked) := by
  obtain ⟨reserved,atoms,allocated,rfl⟩ := growth
  exact ⟨shape registry before reserved atoms allocated certificate⟩

/-- Actual Shared ordinary traces preserve the structural witness. Arbitrary
Shared steps, in particular descriptor refresh, are not claimed here. -/
theorem ordinary_steps {registry : Registry} {root occurrence : Occurrence roles}
    {before after : GeneralNominalSupport.Tracked roles} {declaration : Declaration}
    {checked : DeclarationChecked registry.constructors roles declaration}
    (path : B4Target.Steps (GeneralDictionarySharedEvidenceTrace.OrdinaryStep registry root) before after)
    (certificate : Shape registry before.current.context occurrence declaration checked) :
    Nonempty (Shape registry after.current.context occurrence declaration checked) :=
  extension (GeneralDictionarySharedEvidenceTrace.ordinary_trace_extension _ _ _ _ path) certificate

/-- The terminal payload is unchanged and interpreted in every final model.
Final source formation supplies metadata; source satisfiability is not concluded. -/
theorem current_evidence {registry : Registry} {root occurrence : Occurrence roles}
    {before after : GeneralNominalSupport.Tracked roles} {declaration : Declaration}
    (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (path : B4Target.Steps (GeneralDictionarySharedEvidenceTrace.OrdinaryStep registry root) before after)
    (formed : GeneralNominalSharedSteps.SourceFormed registry root after)
    (certificate : Shape registry before.current.context occurrence declaration checked)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models after.current model) :
    GeneralDictionaryRecursiveEvidence.Evidence registry after.current.context model occurrence
      (.node declaration.id []) := by
  obtain ⟨transported⟩ := ordinary_steps path certificate
  exact evidence_of_shape _ _ _ _ visible checked transported
    (GeneralDictionarySharedMetadata.formed_metadata formed) model valid.1
end Yulang.GeneralDictionary171NamedSpinePersistence
