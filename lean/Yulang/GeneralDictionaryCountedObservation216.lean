import Yulang.GeneralDictionaryCountedBracket216
import Yulang.GeneralDictionaryStructuralProjection215
import Yulang.GeneralDictionaryDefaultNominalProjection215
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryCountedObservation216
open CommonNominalFullCarrier GeneralDeclarationPatterns GeneralPatternNormalForm
open GeneralNominalCenteredHeadMatPatternSemantics
open GeneralNominalCenteredHeadMatCompilerSemantics (algebra)
open GeneralNominalCenteredHeadMatHeadParts (CompleteLabel)
open GeneralNominalRecursiveInspection GeneralNominalOriginTerms GeneralNominalFiniteMeaning
open GeneralNominalReadbackFunctionality
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryStructuralProjection215 (Bounded)
variable {model : Assignment} {state : GeneralNominalState.State}

def Labelled (constructors : Constructors) (interpretation : GeneralNominalInspection.Interpretation)
    (model : Assignment) (origin : Origin) : Prop :=
  ∃ pattern, CompleteLabel pattern ∧ At model .actual origin (eval (algebra constructors interpretation) (fun _ => .bottom) pattern)

theorem counted_source
    (known : GeneralNominalCenteredHeadMatSemanticLabels.CountedMeaning (algebra constructors interpretation) (model source).1 pattern) :
    Labelled constructors interpretation model (.source source) := by
  refine ⟨normalize (normalize pattern),⟨?_,normalized _ known.2.1⟩,⟨⟨_,.source _⟩,?_⟩⟩
  · exact GeneralNominalCenteredHeadMatSemanticSubstitution.normalized_closed known.1
  · intro value seen
    cases seen
    exact eqv_trans known.2.2 (normalize_sound _)

theorem labelled_project (known : Labelled constructors interpretation model origin)
    (tested : Head model origin test) (canonical : TestCanonical test) (index : Fin (arity test)) :
    Labelled constructors interpretation model (project origin test index) := by
  obtain ⟨pattern,complete,meaning⟩ := known
  obtain ⟨value,seen⟩ := meaning.1
  have head : test.Holds (eval (algebra constructors interpretation) (fun _ => .bottom) pattern) :=
    GeneralNominalCenteredHeadMatHeadShape.holds_congr (meaning.2 value seen) (tested.2 value seen)
  obtain ⟨pieces,len,parts,equal,bound⟩ := GeneralNominalCenteredHeadMatHeadParts.inversion complete canonical head
  have located : At model .actual origin (GeneralNominalCenteredHeadMatHeadParts.realize test
      (pieces.map (eval (algebra constructors interpretation) (fun _ => .bottom)))) :=
    ⟨meaning.1,fun actual observed => eqv_trans (meaning.2 actual observed) equal⟩
  rw [GeneralNominalCenteredHeadMatHeadParts.realize_build (by simp [len])] at located
  have projected := project_value test canonical _ located index
  refine ⟨pieces[index.val]'(by rw [len]; exact index.isLt),parts _ (List.getElem_mem ..),?_⟩
  simpa only [List.getElem_map] using projected

theorem scalar (valid : GeneralNominalState.Models state model)
    (known : Labelled constructors interpretation model origin)
    (bounded : Bounded state model bounds origin) (recorded : state.view.heads bounds.1 = .scalar base) :
    Head model origin (.scalar base) := by
  obtain ⟨pattern,complete,meaning⟩ := known
  obtain ⟨value,seen⟩ := meaning.1
  have slot := GeneralNominalInspectionFiniteValues.scalar_slot state model valid bounds.1 recorded
  have rigid := GeneralDictionaryCountedRoot216.scalar_rigid complete.2
    (subtype_trans slot.2 (subtype_trans (bounded.2 value seen).1 (meaning.2 value seen).1))
  exact ⟨meaning.1,fun actual observed => eqv_trans (meaning.2 actual observed) rigid⟩

theorem structural (valid : GeneralNominalState.Models state model)
    (known : Labelled constructors interpretation model origin)
    (bounded : Bounded state model bounds origin)
    (lowerAt : state.view.heads bounds.1 = .structural lowerKind lows)
    (upperAt : state.view.heads bounds.2 = .structural upperKind ups)
    (one : state.view.shapes lowerKind = shape) (two : state.view.shapes upperKind = shape)
    (canonical : shape.Canonical) : Head model origin (.structural shape) := by
  obtain ⟨pattern,complete,meaning⟩ := known
  obtain ⟨value,seen⟩ := meaning.1
  have lowerValue := GeneralNominalFiniteBracket.structural_slot state model valid bounds.1 lowerKind lows lowerAt one
  have upperValue := GeneralNominalFiniteBracket.structural_slot state model valid bounds.2 upperKind ups upperAt two
  have tested := GeneralDictionaryCountedBracket216.structural complete.1 complete.2 canonical
    (List.length_ofFn) (List.length_ofFn)
    (subtype_trans lowerValue.2 (subtype_trans (bounded.2 value seen).1 (meaning.2 value seen).1))
    (subtype_trans (meaning.2 value seen).2 (subtype_trans (bounded.2 value seen).2 upperValue.1))
  refine ⟨meaning.1,fun actual observed => ?_⟩
  exact GeneralNominalCenteredHeadMatHeadShape.holds_congr (eqv_symm (meaning.2 actual observed)) tested

theorem nominal (valid : GeneralNominalState.Models state model)
    (known : Labelled constructors interpretation model origin)
    (bounded : Bounded state model bounds origin)
    (recorded : state.nominals bounds.1 = some descriptor)
    (length : descriptor.arguments.length = count) :
    Head model origin (.nominal descriptor.declaration.name count) := by
  obtain ⟨pattern,complete,meaning⟩ := known
  obtain ⟨value,seen⟩ := meaning.1
  obtain ⟨arguments,fits,equal⟩ := valid.2.1 bounds.1 descriptor recorded
  have size := GeneralNominalLinearMaterializationFacts.fitsAll_length _ _ _ _ fits
  have rigid := GeneralDictionaryCountedRoot216.nominal_rigid complete.2
    (subtype_trans equal.2 (subtype_trans (bounded.2 value seen).1 (meaning.2 value seen).1))
  exact ⟨meaning.1,fun actual observed => ⟨arguments,size.trans length,eqv_trans (meaning.2 actual observed) rigid⟩⟩
end Yulang.GeneralDictionaryCountedObservation216
