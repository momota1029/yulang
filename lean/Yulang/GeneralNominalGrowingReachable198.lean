import Yulang.GeneralNominalGrowingEvidence198

set_option backward.isDefEq.respectTransparency false
/-! The growing-refresh fixture starts at the real WF Initial predicate,
including a ground root and constructor coverage, not just an initial constructor. -/
namespace Yulang.GeneralNominalGrowingReachable198
open GeneralDeclarations GeneralSourceDictionaries GeneralDeclarationPatterns
open GeneralNominalGrowingRefresh198
open GeneralDeclarationExamples (roles constructors)
open GeneralNominalCenteredHeadWFBoundary (boundary)
open CommonNominalFullCarrier

theorem checked : Checked registry :=
  ⟨by simp,fun d member => (List.mem_singleton.mp member) ▸ GeneralNominalGrowingEvidence198.declaration_checked⟩

theorem metadata : GeneralNominalRecursiveCandidates.Metadata registry oldContext := by
  refine ⟨rfl,?_⟩
  intro name primitive recorded
  by_cases two : name = 2
  · subst name
    have same : GeneralCandidateInspection.Primitive.scalar .int = primitive := Option.some.inj recorded
    subst primitive
    exact ⟨⟨[],2⟩,rfl,rfl⟩
  · simp [two] at recorded

theorem source : GeneralNominalSourceFormation.InitialSource registry oldContext root where
  roles_agree := rfl
  metadata := metadata
  linked := by
    constructor
    · intro index
      constructor <;> simp [GeneralNominalState.sources,List.ofFn_succ]
    · intro output member
      cases member
  intervals := fun _ _ _ => subtype_refl _
  below_seed := by
    intro name member
    simp [GeneralNominalState.sources,List.ofFn_succ] at member
    rcases member with h | h | h | h <;> subst name <;> decide
  unallocated := rfl

theorem ground : GeneralNominalGroundAccessibility.GroundRoots oldContext root [.app 2 []] := by
  refine ⟨rfl,?_⟩
  intro index
  let term : GeneralNominalOriginTerms.Expr Nat := .node (.scalar .int) Fin.elim0
  refine ⟨term,?_,?_⟩
  · refine ⟨?_,?_,?_⟩
    · simp [normalize,normalizeArgs,GeneralNominalInspection.translate,GeneralNominalExamples.interpretation,
        GeneralNominalCompoundReadback.quote,term]
    · simp [term,GeneralNominalOriginTerms.Expr.leaves,List.ofFn_zero,GeneralNominalOriginTerms.arity]
    · exact ⟨trivial,fun index => Fin.elim0 index⟩
  · intro model valid
    constructor
    · exact valid.1.1 _ (List.mem_cons_self)
    · exact valid.1.1 _ (List.mem_cons_of_mem _ (List.mem_cons_self))

theorem coverage : GeneralNominalCenteredHeadWFSource.Coverage registry oldContext.interpretation := by
  constructor
  · intro d member
    cases List.mem_singleton.mp member
    simp [GeneralNominalCenteredHeadWFSource.DeclarationCovered,
      GeneralNominalCenteredHeadWFSource.PatternsCovered,GeneralNominalCenteredHeadWFSource.PatternCovered]
  · intro role name body found
    by_cases one : role = 1
    · simp [roles,one,GeneralDeclarationExamples.outputRole] at found
    · by_cases two : role = 2
      · simp [roles,two,GeneralDeclarationExamples.outputRole] at found
      · by_cases four : role = 4 <;>
          simp [roles,one,two,four,GeneralDeclarationExamples.binaryRole,GeneralDeclarationExamples.bareRole] at found

theorem initial_source : (boundary roles).Initial registry root start :=
  ⟨⟨oldContext,[.app 2 []],source,(fun _ => rfl),ground,rfl⟩,coverage⟩

theorem reachable : B4TargetV6.Reachable (boundary roles) registry root finish :=
  ⟨start,initial_source,.tail .refl actual_step.1⟩

theorem inhabited_reachable : Checked registry ∧
    B4TargetV6.Reachable (boundary roles) registry root finish ∧
    ∃ model, GeneralNominalCenteredHeadStepEffects.Models finish model ∧
      (boundary roles).Evidence registry finish model root (.node 1980 []) := by
  obtain ⟨model,_,final,_,evidence⟩ := GeneralNominalGrowingEvidence198.inhabited_evidence
  exact ⟨checked,reachable,model,final,evidence⟩
end Yulang.GeneralNominalGrowingReachable198
