import Yulang.GeneralDictionaryObservedFiniteRequests
import Yulang.GeneralDictionaryFinishedTrace

/-! Finite structural request observations survive real view-preserving feedback
refreshes. Arbitrary descriptor changes and fresh targets are not covered. -/
namespace Yulang.GeneralDictionaryObservedRefreshTransport
open GeneralDictionaryObservedFiniteRequests
open GeneralDictionaryInspectionTransport
open GeneralNominalMaterialization
open GeneralNominalRecursiveCandidates (Context)

/-- Retention of every nominal node follows from Refines on the fixed carrier;
only scalar observations additionally use unchanged normalized view. -/
noncomputable def tree_reobserve (context : Context) (next : Observation context.state)
    (view : next.view = context.state.view)
    (refinement : GeneralNominalRefinements.Refines context.state (reobserve context next).state)
    {slot query} (tree : Tree context.state slot query) :
    Tree (reobserve context next).state slot query := by
  rcases next with ⟨v,n,c,o⟩
  dsimp only at view
  subst v
  let next : Observation context.state := ⟨context.state.view,n,c,o⟩
  induction tree with
  | scalar slot base head => exact @Tree.scalar (reobserve context next).state slot base head
  | nominal slot descriptor recorded slots queries parameters branches ih =>
    exact @Tree.nominal (reobserve context next).state _ slot descriptor
      (GeneralDictionaryRefreshDescriptors.descriptor_preserved context next refinement slot descriptor recorded)
      slots queries parameters ih

/-- One-way structural preservation. Newly observed source descriptors may add
certificates, so no converse is asserted. -/
theorem observed_reobserve (context : Context) (next : Observation context.state)
    (view : next.view = context.state.view)
    (refinement : GeneralNominalRefinements.Refines context.state (reobserve context next).state)
    (requests : List Request) (observed : Observed context.state context.interpretation requests) :
    Observed (reobserve context next).state (reobserve context next).interpretation requests := by
  intro request member
  obtain ⟨slot,target,⟨tree⟩⟩ := observed request member
  exact ⟨slot,target,⟨tree_reobserve context next view refinement tree⟩⟩

/-- The structural fields are unchanged by ordinary extension. -/
noncomputable def tree_extension (context : Context)
    (reserved : List Nat) (atoms : List (PresenceNormalForm.Atom Nat))
    (allocated : List GeneralNominalIdentities.Origin)
    {slot query} (tree : Tree context.state slot query) :
    Tree (GeneralDictionaryOrdinaryTrace.extendContext context reserved atoms allocated).state slot query := by
  induction tree with
  | scalar slot base head =>
    exact @Tree.scalar (GeneralDictionaryOrdinaryTrace.extendContext context reserved atoms allocated).state slot base head
  | nominal slot descriptor recorded slots queries parameters branches ih =>
    exact @Tree.nominal (GeneralDictionaryOrdinaryTrace.extendContext context reserved atoms allocated).state _
      slot descriptor recorded slots queries parameters ih

theorem observed_extension (before after : Context)
    (growth : GeneralDictionaryOrdinaryTrace.Extension before after) (requests : List Request)
    (observed : Observed before.state before.interpretation requests) :
    Observed after.state after.interpretation requests := by
  obtain ⟨reserved,atoms,allocated,rfl⟩ := growth
  intro request member
  obtain ⟨slot,target,⟨tree⟩⟩ := observed request member
  exact ⟨slot,target,⟨tree_extension before reserved atoms allocated tree⟩⟩

/-- Each transition is already an actual feedback transition; this result adds
preservation of request certificates, not a new executor. -/
theorem observed_step {roles : Roles.RoleDecls} (registry : GeneralDeclarations.Registry)
    (root : GeneralSourceDictionaries.Occurrence roles)
    (before after : GeneralNominalSaturationState.State roles)
    (step : GeneralDictionaryFinishedTrace.Step registry root before after)
    (requests : List Request)
    (observed : Observed before.context.state before.context.interpretation requests) :
    Observed after.context.state after.context.interpretation requests := by
  cases step with
  | ordinary actual => exact observed_extension _ _ actual.2 requests observed
  | refresh next view certificate actual =>
    exact observed_reobserve _ next view certificate.refines requests observed

theorem observed_trace {roles : Roles.RoleDecls} (registry : GeneralDeclarations.Registry)
    (root : GeneralSourceDictionaries.Occurrence roles)
    (before after : GeneralNominalSaturationState.State roles)
    (path : B4Target.Steps (GeneralDictionaryFinishedTrace.Step registry root) before after)
    (requests : List Request)
    (observed : Observed before.context.state before.context.interpretation requests) :
    Observed after.context.state after.context.interpretation requests := by
  induction path with
  | refl => exact observed
  | tail _ step ih => exact observed_step registry root _ _ step requests ih

/-- All final models satisfy generated materialization constraints. The initial
hypothesis is a structural finite tree certificate, never generated Models. -/
theorem generated_models_after_trace {roles : Roles.RoleDecls}
    (registry : GeneralDeclarations.Registry) (root : GeneralSourceDictionaries.Occurrence roles)
    (before after : GeneralNominalSaturationState.State roles)
    (path : B4Target.Steps (GeneralDictionaryFinishedTrace.Step registry root) before after)
    (requests : List Request)
    (observed : Observed before.context.state before.context.interpretation requests)
    (declaration : GeneralDeclarations.Declaration) (capture : GeneralDeclarationDemands.Capture)
    (report : GeneralNominalRecursiveInspection.Report after.context.state)
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models after.context.state model) :
    Models after.context.state declaration capture report
      (generated after.context.state after.context.interpretation requests) model :=
  generated_models _ _ _ (observed_trace registry root before after path requests observed)
    declaration capture report model valid
/-- Named outputs survive actual refresh traces when variable-only where
clauses reduce materialization to those outputs. -/
theorem actual_requests_models_after_trace {roles : Roles.RoleDecls}
    (registry : GeneralDeclarations.Registry) (root : GeneralSourceDictionaries.Occurrence roles)
    (before after : GeneralNominalSaturationState.State roles)
    (path : B4Target.Steps (GeneralDictionaryFinishedTrace.Step registry root) before after)
    (declaration : GeneralDeclarations.Declaration)
    (checked : GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
    (captures : GeneralNominalAllocation.Bindings)
    (variables : GeneralDictionaryVariableRequirements.VariableClauses declaration)
    (observed : Observed before.context.state before.context.interpretation (rootRequests declaration root))
    (capture : GeneralDeclarationDemands.Capture)
    (report : GeneralNominalRecursiveInspection.Report after.context.state)
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models after.context.state model) :
    Models after.context.state declaration capture report
      (generated after.context.state after.context.interpretation
        (requests after.context.state registry root declaration checked captures)) model := by
  rw [GeneralDictionaryObservedScalarRequests.requests_root _ _ _ _ _ _ variables]
  exact generated_models_after_trace registry root before after path _ observed declaration capture report model valid

/-- The generated schema is closed after a real feedback trace, independently
of whether any source model exists. -/
theorem generated_shape_after_trace {roles : Roles.RoleDecls}
    (registry : GeneralDeclarations.Registry) (root : GeneralSourceDictionaries.Occurrence roles)
    (before after : GeneralNominalSaturationState.State roles)
    (path : B4Target.Steps (GeneralDictionaryFinishedTrace.Step registry root) before after)
    (requests : List Request)
    (observed : Observed before.context.state before.context.interpretation requests) :
    (generated after.context.state after.context.interpretation requests).variables = [] ∧
    (generated after.context.state after.context.interpretation requests).unknown = false :=
  generated_shape _ _ _ (observed_trace registry root before after path requests observed)

end Yulang.GeneralDictionaryObservedRefreshTransport
