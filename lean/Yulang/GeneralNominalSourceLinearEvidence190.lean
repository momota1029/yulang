import Yulang.GeneralNominalSourceLinearShape190
import Yulang.GeneralNominalSourceOutputReady190
import Yulang.GeneralNominalLinearNamedEvidence189

/-! Source-derived finite linear leaf Evidence at the actual WF/V6 boundary.
Named requests may be nonempty. Initiality, leaf shape, distinct head variables,
request coverage and complete translated RHS queries are real restrictions;
no claim about arbitrary reachable states or nonleaf EvidenceNode is made. -/
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalSourceLinearEvidence190
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadOutputs
open GeneralNominalCenteredHeadWFBoundary (boundary Local)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles} {state : State roles}

theorem selected_installable (checked : Checked registry)
    (source : (boundary roles).Initial registry root state)
    (selected : Local registry state root (.selected key children))
    (candidate : Plan roles) (frame : Frame registry state.core root key candidate)
    (names : List Nat) (distinct : names.Nodup)
    (head : candidate.packet.declaration.head = names.map Pattern.var)
    (leaf : candidate.packet.declaration.requirements = [])
    (coverage : ∀ output ∈ root.demand.outputs,
      ∃ equation ∈ candidate.packet.declaration.associated, equation.name = output.name)
    (translated : ∀ equation ∈ candidate.packet.declaration.associated,
      GeneralNominalHeadMatchMass.Complete (GeneralNominalInspection.translate
        candidate.packet.context.state.constructors candidate.packet.context.interpretation (normalize equation.rhs))) :
    ∃ support, GeneralNominalCenteredHeadStepKernel.Installable registry state candidate support := by
  obtain ⟨entries,namesEq,bounds,query,inputNames⟩ :=
    GeneralNominalSourceLinearShape190.initial_entries source candidate frame names head
  exact GeneralNominalLinearNamedPlan189.selected_named_installable checked source selected candidate frame entries
    (namesEq.symm ▸ distinct) query bounds inputNames leaf
    (GeneralNominalSourceOutputReady190.source_effects_ready source candidate coverage translated)

/-- The actual selected survivor supplies Frame and plan; source declarations
supply finite head shape, with no caller-supplied inspection/bounds plumbing. -/
theorem selected_source_candidate (checked : Checked registry)
    (source : (boundary roles).Initial registry root state)
    (selected : Local registry state root (.selected key children))
    (declarations : ∀ declaration ∈ registry.declarations, declaration.id = key →
      (∃ names : List Nat, names.Nodup ∧ declaration.head = names.map Pattern.var) ∧
      declaration.requirements = [] ∧
      (∀ output ∈ root.demand.outputs, ∃ equation ∈ declaration.associated, equation.name = output.name) ∧
      ∀ equation ∈ declaration.associated, GeneralNominalHeadMatchMass.Complete
        (GeneralNominalInspection.translate state.core.erased.current.context.state.constructors
          state.core.erased.current.context.interpretation (normalize equation.rhs))) :
    ∃ candidate support, Frame registry state.core root key candidate ∧
      candidate.packet.children = children ∧ GeneralNominalCenteredHeadStepKernel.Installable registry state candidate support := by
  have old := GeneralNominalCenteredHeadWFBoundary.local_iff.mp selected
  have unique : GeneralNominalCenteredHeadCandidates.Unique registry state.core.erased.current.context root key children := by
    cases old with
    | selected _ unique _ => exact unique
  obtain ⟨candidate,frame,kids⟩ := GeneralNominalHeadInitialFrame188.initial_frame state source unique.1
  obtain ⟨⟨names,distinct,head⟩,leaf,coverage,translated⟩ :=
    declarations candidate.packet.declaration frame.visible frame.key_eq
  have supported : ∀ equation ∈ candidate.packet.declaration.associated,
      GeneralNominalHeadMatchMass.Complete (GeneralNominalInspection.translate candidate.packet.context.state.constructors
        candidate.packet.context.interpretation (normalize equation.rhs)) := by
    rw [frame.context_eq]
    exact translated
  obtain ⟨support,enabled⟩ := selected_installable checked source selected candidate frame names distinct head leaf coverage supported
  exact ⟨candidate,support,frame,kids,enabled⟩

/-- Soundness: every current model has the actual leaf Evidence. The statement
quantifies over arbitrary finite linear source heads, not a fixed fixture. -/
theorem stable_selected_evidence (checked : Checked registry)
    (source : (boundary roles).Initial registry root state)
    (stable : (boundary roles).Stable registry state root)
    (selected : Local registry state root (.selected key children))
    (declarations : ∀ declaration ∈ registry.declarations, declaration.id = key →
      (∃ names : List Nat, names.Nodup ∧ declaration.head = names.map Pattern.var) ∧
      declaration.requirements = [] ∧
      (∀ output ∈ root.demand.outputs, ∃ equation ∈ declaration.associated, equation.name = output.name) ∧
      ∀ equation ∈ declaration.associated, GeneralNominalHeadMatchMass.Complete
        (GeneralNominalInspection.translate state.core.erased.current.context.state.constructors
          state.core.erased.current.context.interpretation (normalize equation.rhs))) :
    children = [] ∧ ∀ model, Models state model →
      (boundary roles).Evidence registry state model root (.node key []) := by
  obtain ⟨candidate,support,frame,kids,enabled⟩ :=
    selected_source_candidate checked source selected declarations
  have leaf := (declarations candidate.packet.declaration frame.visible frame.key_eq).2.1
  have committed := GeneralNominalInitialLeafEvidence189.stable_committed stable candidate frame enabled
  refine ⟨kids.symm.trans (GeneralNominalHeadLeafPlan189.children_empty candidate leaf),?_⟩
  intro model valid
  have ready : EffectsReady state.core root candidate := by
    simpa only [frame.occurrence_eq] using enabled.ready
  exact GeneralDictionaryRecursiveEvidence.evidence_node registry state.core.erased.current.context model
    root key [] [] (GeneralNominalInitialNamedEvidence189.committed_instance source candidate frame leaf ready committed model valid) .nil

end Yulang.GeneralNominalSourceLinearEvidence190
