import Yulang.GeneralNominalCenteredProgress

/-! Constructor production over the surviving original holes. Child trees
are composed with actual recorded projections and their actual graph edges;
the later state's frontier is never substituted for the initial frontier. -/
namespace Yulang.GeneralNominalConstructorSourceExpansion
open GeneralNominalSaturationState GeneralNominalRecursiveInspection GeneralNominalOriginTerms
open GeneralNominalIndexedHoleReadback GeneralNominalHoleElimination GeneralNominalReadbackFunctionality
open GeneralNominalScopedRecipeLabels GeneralNominalBackedHoleElimination GeneralNominalSourceHoleExposure
open GeneralNominalSourceProducerHandoff

variable {roles : Roles.RoleDecls} {state : State roles} {identities : Nat → Nat}
variable {inventory : Inventory} {tests : List Test}

def Represented (state : State roles) (identities : Nat → Nat) (remaining : List Nat)
    (tests : List Test) (source : Nat) : Prop :=
  ∃ term, Readback (Models state) (fun name => .source (identities name)) remaining (.source source) term ∧
    Canonical term ∧ Vocabulary tests term ∧ Backed state identities source term

theorem structural (parent : Fin state.context.state.base.slots)
    (kind : Fin state.context.state.view.kinds)
    (slots : Fin (state.context.state.view.shapes kind).arity → Fin state.context.state.base.slots)
    (recorded : state.context.state.view.heads parent = .structural kind slots)
    (vocabulary : Test.structural (state.context.state.view.shapes kind) ∈ tests)
    (children : ∀ position, Represented state identities inventory.holes tests
      (state.context.state.base.source (slots position))) :
    ConstructorExpansion state identities inventory tests (state.context.state.base.source parent) := by
  classical
  let trees := fun position => Classical.choose (children position)
  have child := fun position => Classical.choose_spec (children position)
  refine ⟨.structural (state.context.state.view.shapes kind),trees,?_,
    ⟨state.context.state.view.canonical kind,fun position => (child position).2.1⟩,
    ⟨vocabulary,fun position => (child position).2.2.1⟩,?_⟩
  · constructor
    · intro model valid
      refine ⟨((structural_readback state parent kind slots recorded).1 model valid).1,?_⟩
      intro position
      exact holds_transport (same_symm (GeneralNominalStructuralReadback.actual_structural_readback
        state parent kind slots recorded position model valid)) ((child position).1.1 model valid)
    · intro name member
      obtain ⟨parts,present,member⟩ := List.mem_flatten.mp member
      obtain ⟨position,rfl⟩ := List.mem_ofFn.mp present
      exact (child position).1.2 name member
  · apply Backed.node (.structural (state.context.state.view.shapes kind)) trees (fun position => state.context.state.base.source (slots position))
    · intro position
      exact ⟨slot_source _ parent,slot_source _ (slots position),Or.inl
        ⟨parent,slots position,⟨kind,slots,recorded,position,rfl⟩,
          GeneralNominalFeedbackK2.equal_refl state _,GeneralNominalFeedbackK2.equal_refl state _⟩⟩
    · exact fun position => (child position).2.2.2

theorem point_nominal (parent : Fin state.context.state.base.slots)
    (descriptor : GeneralNominalState.Descriptor state.context.state.base.slots)
    (recorded : state.context.state.nominals parent = some descriptor)
    (points : List (Fin state.context.state.base.slots))
    (found : typeArguments descriptor.arguments = some (points.map fun slot => (slot,slot)))
    (vocabulary : Test.nominal descriptor.declaration.name points.length ∈ tests)
    (children : ∀ position : Fin points.length, Represented state identities inventory.holes tests
      (state.context.state.base.source (points[position.val]'position.isLt))) :
    ConstructorExpansion state identities inventory tests (state.context.state.base.source parent) := by
  classical
  let trees := fun position => Classical.choose (children position)
  have child := fun position => Classical.choose_spec (children position)
  refine ⟨.nominal descriptor.declaration.name points.length,trees,?_,
    ⟨True.intro,fun position => (child position).2.1⟩,
    ⟨vocabulary,fun position => (child position).2.2.1⟩,?_⟩
  · constructor
    · intro model valid
      refine ⟨((nominal_readback state parent descriptor recorded points found).1 model valid).1,?_⟩
      intro position
      exact holds_transport (same_symm (GeneralNominalActualInspectionSteps.point_argument_readback
        state parent (points[position.val]'position.isLt) descriptor recorded (point_parameter descriptor points found position) model valid))
        ((child position).1.1 model valid)
    · intro name member
      obtain ⟨parts,present,member⟩ := List.mem_flatten.mp member
      obtain ⟨position,rfl⟩ := List.mem_ofFn.mp present
      exact (child position).1.2 name member
  · apply Backed.node (.nominal descriptor.declaration.name points.length) trees (fun position => state.context.state.base.source (points[position.val]'position.isLt))
    · intro position
      exact ⟨slot_source _ parent,slot_source _ (points[position.val]'position.isLt),Or.inr
        (GeneralNominalFeedbackK2.endpoint_argument state parent (points[position.val]'position.isLt) (points[position.val]'position.isLt) descriptor recorded
          position.val (point_parameter descriptor points found position) (GeneralNominalFeedbackK2.equal_refl state _))⟩
    · exact fun position => (child position).2.2.2

theorem scalar (head : ∀ model, Models state model → Head model (.source actual) (.scalar base))
    (vocabulary : Test.scalar base ∈ tests) : ConstructorExpansion state identities inventory tests actual := by
  refine ⟨.scalar base,Fin.elim0,⟨fun model valid => ⟨head model valid,fun position => Fin.elim0 position⟩,?_⟩,
    ⟨True.intro,fun position => Fin.elim0 position⟩,⟨vocabulary,fun position => Fin.elim0 position⟩,?_⟩
  · intro name member
    simp only [Expr.leaves,arity,List.ofFn_zero,List.flatten_nil,List.not_mem_nil] at member
  · exact .node _ _ Fin.elim0 (fun position => Fin.elim0 position) (fun position => Fin.elim0 position)

theorem expansion_discharge (templates : NodeTemplates context keys tests)
    (old : Readback (Models state) (fun name => .source (identities name)) inventory.holes
      (.source actual) (.leaf hole))
    (expanded : ConstructorExpansion state identities inventory tests actual)
    (inhabited : ∃ model, Models state model) (safe : ¬ GeneralNominalFeedbackK2.RecursAt state actual) :
    ∃ replacement : GeneralNominalLabelledOriginClosure.Value (Models state) context
        (fun name => .source (identities name)) (inventory.holes.erase hole) keys (.source (identities hole)),
      (∃ test children, replacement.term = .node test children) ∧
      ∃ extra, Trace (GeneralNominalSourceLabelVocabulary.tests keys) (fun _ => extra) inventory
        (eliminate inventory hole (GeneralNominalPatternInventory.encode replacement.pattern) extra) 1 := by
  obtain ⟨test,children,readback,canonical,vocabulary,backed⟩ := expanded
  obtain ⟨replacement,equal,trace,agreement⟩ := GeneralNominalLabelledExposureElimination.discharge state templates
    old readback canonical vocabulary backed inhabited safe
  exact ⟨replacement,⟨test,children,equal⟩,trace⟩

theorem tested_discharge {state : GeneralNominalSupport.Tracked roles} {observed : Origin}
    (templates : NodeTemplates context keys tests)
    (member : (observed,tested) ∈ (GeneralNominalActualInspectionSteps.inspection state.current packet).tests)
    (located : GeneralNominalActualInspectionSteps.Represents state.current observed actual)
    (guard : GeneralNominalActualInspectionSteps.PacketGuard state packet support)
    (old : Readback (Models state.current) (fun name => .source (identities name)) inventory.holes
      (.source actual) (.leaf hole))
    (expanded : ConstructorExpansion state.current identities inventory tests actual) :
    (¬ ∃ model, Models state.current model) ∨
    ∃ replacement : GeneralNominalLabelledOriginClosure.Value (Models state.current) context
        (fun name => .source (identities name)) (inventory.holes.erase hole) keys (.source (identities hole)),
      (∃ test children, replacement.term = .node test children) ∧
      ∃ extra, Trace (GeneralNominalSourceLabelVocabulary.tests keys) (fun _ => extra) inventory
        (eliminate inventory hole (GeneralNominalPatternInventory.encode replacement.pattern) extra) 1 := by
  classical
  by_cases inhabited : ∃ model, Models state.current model
  · apply Or.inr
    apply expansion_discharge templates old expanded inhabited
    intro recursive
    exact (guard.2.1.2 (observed,tested) member).2 ⟨actual,located,recursive⟩
  · exact Or.inl inhabited

theorem centered_tested_discharge {state : GeneralNominalCenteredSteps.State roles} {observed : Origin}
    (templates : NodeTemplates context keys tests)
    (member : (observed,tested) ∈ (GeneralNominalCenteredSteps.inspection plan).tests)
    (located : GeneralNominalActualInspectionSteps.Represents state.erased.current observed actual)
    (guard : GeneralNominalCenteredSteps.PacketGuard state plan support)
    (old : Readback (Models state.erased.current) (fun name => .source (identities name)) inventory.holes
      (.source actual) (.leaf hole))
    (expanded : ConstructorExpansion state.erased.current identities inventory tests actual) :
    ∃ replacement : GeneralNominalLabelledOriginClosure.Value (Models state.erased.current) context
        (fun name => .source (identities name)) (inventory.holes.erase hole) keys (.source (identities hole)),
      (∃ test children, replacement.term = .node test children) ∧
      ∃ extra, Trace (GeneralNominalSourceLabelVocabulary.tests keys) (fun _ => extra) inventory
        (eliminate inventory hole (GeneralNominalPatternInventory.encode replacement.pattern) extra) 1 := by
  obtain ⟨model,valid,branch⟩ := guard.2.2.2.2.2.2
  apply expansion_discharge templates old expanded ⟨model,valid.1⟩
  intro recursive
  exact guard.2.2.2.1.2 (observed,tested) member (Or.inl ⟨actual,located,recursive⟩)

end Yulang.GeneralNominalConstructorSourceExpansion
