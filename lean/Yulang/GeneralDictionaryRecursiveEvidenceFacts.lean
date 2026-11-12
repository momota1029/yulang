import Yulang.GeneralDictionaryRecursiveEvidence

/-!
# Semantic consequences of recursive dictionary branch evidence

These facts expose actual interval, projection and source-equation content.
In particular a projected value fits the merged capture used by variable where
inputs even when captures are repeated and endpoint intervals are non-singleton.
No value is selected by the dictionary resolver, and no original-state model is
asserted to satisfy branch constraints merely because the branch is consistent.
-/
namespace Yulang.GeneralDictionaryRecursiveEvidence

open GeneralDeclarations GeneralDeclarationDemands
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRecursiveCandidates (Context report generated BranchModels)
open GeneralNominalRecursiveInspection (bindings Observes)

/-- EvidenceNode inspects no transition, stability or generation field. Merely
changing those three fields cannot repair an all-model node obstruction. -/
theorem boundary_evidenceNode_independent (roles : Roles.RoleDecls)
    (first last : GeneralNominalLocalBoundary.Remaining (GeneralNominalCandidates.vocabulary roles)) :
    B4TargetV3.EvidenceNode (boundary roles first) ↔
      B4TargetV3.EvidenceNode (boundary roles last) := Iff.rfl

/-- Exact decomposition of the private branch semantics. The original-state
model is only one conjunct; repeated-capture, interval, projection and generated
source equations are additional obligations, not consequences of consistency. -/
theorem branch_models_iff (registry : Registry) (context : Context)
    (root : Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (bounds : List (GeneralNominalInspection.Bounds context.state)) (model : Assignment) :
    BranchModels registry context root declaration checked bounds model ↔
      GeneralNominalState.Models context.state model ∧
      GeneralNominalAllocation.Compatible (bindings context.state (report context declaration bounds)) model ∧
      PresenceNormalForm.All CommonNominalFullCarrier.model model
        (GeneralNominalAllocation.merges context.state registry root.identity declaration
          (bindings context.state (report context declaration bounds))) ∧
      PresenceNormalForm.All CommonNominalFullCarrier.model model
        (GeneralNominalRecursiveInspection.selfChecks context.state (report context declaration bounds)) ∧
      GeneralNominalRecursiveInspection.ProjectionModels context.state
        (report context declaration bounds) model ∧
      GeneralNominalMaterialization.Models context.state declaration
        (GeneralNominalAllocation.capture context.state registry root.identity declaration.id
          (bindings context.state (report context declaration bounds)))
        (report context declaration bounds) (generated registry context root declaration checked bounds) model := by
  constructor
  · intro branch
    have extended := (GeneralNominalState.extend_models ..).mp branch.1
    have propagated := (GeneralNominalAllocation.propagate_models ..).mp extended.1
    exact ⟨propagated.1, propagated.2.1, propagated.2.2, extended.2, branch.2.1, branch.2.2⟩
  · rintro ⟨original, compatible, merged, intervals, projections, materialized⟩
    refine ⟨?_, projections, materialized⟩
    apply (GeneralNominalState.extend_models ..).mpr
    exact ⟨(GeneralNominalAllocation.propagate_models ..).mpr ⟨original, compatible, merged⟩, intervals⟩

/-- Each captured source interval occurs in the computed binder group. -/
theorem capture_occurs (context : Context) (declaration : Declaration)
    (bounds : List (GeneralNominalInspection.Bounds context.state))
    (captured : GeneralNominalRecursiveInspection.Capture context.state)
    (present : captured ∈ (report context declaration bounds).captures) :
    (context.state.base.source captured.bounds.1, context.state.base.source captured.bounds.2) ∈
      GeneralNominalAllocation.occurrences (bindings context.state (report context declaration bounds)) captured.name := by
  apply List.mem_map.mpr
  refine ⟨(captured.name, context.state.base.source captured.bounds.1, context.state.base.source captured.bounds.2), ?_, rfl⟩
  apply List.mem_filter.mpr
  exact ⟨List.mem_map.mpr ⟨captured, present, rfl⟩, by simp⟩

/-- The actual value observed at one occurrence fits every interval of its binder,
then fits the merged capture used by all variable where inputs. -/
theorem projected_value_fits_capture (registry : Registry) (context : Context)
    (root : Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (bounds : List (GeneralNominalInspection.Bounds context.state))
    (model : Assignment) (branch : BranchModels registry context root declaration checked bounds model)
    (captured : GeneralNominalRecursiveInspection.Capture context.state)
    (present : captured ∈ (report context declaration bounds).captures)
    (declared : captured.name ∈ declaration.inputNames)
    (origin : GeneralNominalRecursiveInspection.Origin) (source : captured.origin = some origin)
    (actual : CommonNominalFullCarrier.Ty) (seen : Observes model origin actual) :
    GeneralNominalCaptureMerges.Fits model
      ((GeneralNominalAllocation.capture context.state registry root.identity declaration.id
        (bindings context.state (report context declaration bounds))).inputs captured.name) actual := by
  have nonempty : GeneralNominalAllocation.occurrences
      (bindings context.state (report context declaration bounds)) captured.name ≠ [] := by
    intro empty
    have member := capture_occurs context declaration bounds captured present
    rw [empty] at member
    cases member
  apply (GeneralNominalCaptureMerges.propagated_capture_exact context.state registry root.identity
    declaration (bindings context.state (report context declaration bounds)) model
    ((GeneralNominalState.extend_models ..).mp branch.1).1 captured.name declared nonempty actual).mpr
  intro interval member
  obtain ⟨binding, filtered, rfl⟩ := List.mem_map.mp member
  obtain ⟨bindingMember, same⟩ := List.mem_filter.mp filtered
  obtain ⟨other, otherPresent, rfl⟩ := List.mem_map.mp bindingMember
  have names : other.name = captured.name := by simpa using same
  exact branch.2.1.2.2.1 captured present other otherPresent names.symm origin source actual seen

/-- The original emitted variable child uses that same merged capture, rather
than a fresh unconstrained representative of a repeated binder. -/
theorem projected_value_fits_child (registry : Registry) (context : Context)
    (root : Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (bounds : List (GeneralNominalInspection.Bounds context.state))
    (model : Assignment) (branch : BranchModels registry context root declaration checked bounds model)
    (captured : GeneralNominalRecursiveInspection.Capture context.state)
    (present : captured ∈ (report context declaration bounds).captures)
    (declared : captured.name ∈ declaration.inputNames)
    (origin : GeneralNominalRecursiveInspection.Origin) (source : captured.origin = some origin)
    (actual : CommonNominalFullCarrier.Ty) (seen : Observes model origin actual)
    (clause : Clause) (valid : clause.Signature roles)
    (index : Fin (roles clause.role).arity)
    (pattern : GeneralDeclarationPatterns.normalize
      (clause.arguments[index.val]'(by rw [valid.1]; exact index.isLt)) = .var captured.name) :
    let captures := bindings context.state (report context declaration bounds)
    let child := childDemand declaration clause valid
      (GeneralNominalAllocation.capture context.state registry root.identity declaration.id captures)
      (GeneralNominalAllocation.allocation context.state registry root.identity declaration.id clause)
    GeneralNominalCaptureMerges.Fits model (child.arguments index) actual := by
  dsimp only
  simpa only [childDemand, inputInterval, pattern] using
    projected_value_fits_capture registry context root declaration checked bounds model branch
      captured present declared origin source actual seen

/-- A generated scalar source request has its actual source target equal to the
specified scalar in this model. This covers associated outputs as well as child
requests when the actual generated schema contains the named request. -/
theorem generated_scalar_equation (registry : Registry) (context : Context)
    (root : Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (bounds : List (GeneralNominalInspection.Bounds context.state))
    (model : Assignment) (branch : BranchModels registry context root declaration checked bounds model)
    (target : Nat) (scalar : Inference.Base)
    (present : (.source target, .scalar scalar) ∈
      (generated registry context root declaration checked bounds).tests) :
    CommonNominalFullCarrier.Equivalent (model target).1 (.base scalar) :=
  (branch.2.2.1 _ present).2 (model target).1 (.source target)

/-- A generated output-only binder equation retains its deterministic capture
identity. It is not merely an existential choice of an equivalent output. -/
theorem generated_output_binder_equation (registry : Registry) (context : Context)
    (root : Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (bounds : List (GeneralNominalInspection.Bounds context.state))
    (model : Assignment) (branch : BranchModels registry context root declaration checked bounds model)
    (name target : Nat) (outputOnly : name ∈ declaration.outputNames)
    (present : (⟨name, .source target, .actual⟩ : GeneralNominalMaterialization.Use) ∈
      (generated registry context root declaration checked bounds).variables) :
    CommonNominalFullCarrier.Equivalent (model target).1
      (model ((GeneralNominalAllocation.capture context.state registry root.identity declaration.id
        (bindings context.state (report context declaration bounds))).outputs name)).1 :=
  GeneralNominalMaterialization.output_variable_equation context.state declaration _ _ _ model
    branch.2.2 name target outputOnly present

end Yulang.GeneralDictionaryRecursiveEvidence
