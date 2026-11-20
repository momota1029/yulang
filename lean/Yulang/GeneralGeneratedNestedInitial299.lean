import Yulang.GeneralGeneratedNestedSource299

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 26000
set_option maxHeartbeats 9500000
namespace Yulang.GeneralGeneratedNestedInitial299
open GeneralGeneratedNestedSource299
open GeneralNominalExamples (registry interpretation intDisplay)
open GeneralDeclarationExamples (roles constructors display)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedJournal232 (Models)
open GeneralDeclarationPatterns (Pattern)
open GeneralNominalOriginTerms
open GeneralNominalCompoundReadback
open GeneralNominalGroundAccessibility (GroundRoots ClosedTerm)
open GeneralNominalRecursiveInspection

abbrev labels : List Pattern := [.app 0 [.app 0 [.app 2 []]]]
abbrev intExpr : Expr Nat := .node (.scalar .int) Fin.elim0
abbrev listExpr : Expr Nat := .node (.nominal 0 1) (fun _ => intExpr)
abbrev sourceExpr : Expr Nat := .node (.nominal 0 1) (fun _ => listExpr)

theorem closed_label : ClosedTerm context labels[0] sourceExpr := by
  refine ⟨?_,rfl,⟨trivial,fun _ => ⟨trivial,fun _ => ⟨trivial,fun i => Fin.elim0 i⟩⟩⟩⟩
  simp [labels,GeneralDeclarationPatterns.normalize,GeneralDeclarationPatterns.normalizeArgs,
    GeneralNominalInspection.translate,interpretation,quote,
    List.ofFn_succ,arity]

theorem scalar (m : Assignment) (valid : GeneralNominalState.Models snapshot m) :
    Equivalent (m 2).1 intTy :=
  GeneralNominalState.normalized_models snapshot m valid (2 : Fin 3) (.base .int) rfl

theorem one_level (m : Assignment) (valid : GeneralNominalState.Models snapshot m) :
    Equivalent (m 1).1 listTy := by
  have linked := (GeneralNominalState.denotes_singleton_exact base m (1 : Fin 3) (2 : Fin 3)
    (listDescriptor 2) rfl).mp (valid.2.1 1 _ rfl)
  have next := GeneralNominalPeelingExamples.nominal_congr (scalar m valid) 0
  exact ⟨subtype_trans linked.1 next.1,subtype_trans next.2 linked.2⟩

theorem two_levels (m : Assignment) (valid : GeneralNominalState.Models snapshot m) :
    Equivalent (m 0).1 nestedTy := by
  have linked := (GeneralNominalState.denotes_singleton_exact base m (0 : Fin 3) (1 : Fin 3)
    (listDescriptor 1) rfl).mp (valid.2.1 0 _ rfl)
  have next := GeneralNominalPeelingExamples.nominal_congr (one_level m valid) 0
  exact ⟨subtype_trans linked.1 next.1,subtype_trans next.2 linked.2⟩

theorem ground : GroundRoots context root labels := by
  refine ⟨rfl,?_⟩
  intro index
  have zero : index.val = 0 := by have bounded := index.isLt; change index.val < 1 at bounded; omega
  simp only [zero]
  exact ⟨sourceExpr,closed_label,two_levels⟩

theorem initial_source : GeneralNominalSourceFormation.InitialSource registry context root := by
  refine ⟨rfl,⟨rfl,GeneralDictionarySupportRecursiveExample.initial_source.metadata.2⟩,?_,
    (by intro _ _ _; exact subtype_refl _),?_,rfl⟩
  · constructor
    · intro index
      have present := GeneralNominalAllocationSupport.slot_source snapshot (0 : Fin 3)
      exact ⟨present,present⟩
    · intro output no; cases no
  · intro i present
    have small : i = 0 ∨ i = 1 ∨ i = 2 := by
      simpa [GeneralNominalState.sources,List.ofFn_succ,
        GeneralNominalState.atomSources,GeneralNominalState.typeSources,
        GeneralSourceState.equationAtoms,or_assoc,or_left_comm,or_comm] using present
    change i ≤ 2
    omega

theorem actual_initial : (boundary roles).Initial registry root initial := by
  refine ⟨_,⟨context,labels,initial_source,(fun _ => rfl),ground,
    GeneralNominalCenteredHeadWFFixtures.display_coverage,rfl⟩,rfl⟩

theorem grounded_reachable :
    B4TargetV8.Reachable (boundary roles) registry root initial ∧ Models initial model :=
  ⟨⟨initial,actual_initial,.refl⟩,initial_model⟩

end Yulang.GeneralGeneratedNestedInitial299
