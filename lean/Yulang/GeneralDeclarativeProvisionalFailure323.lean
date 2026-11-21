import Yulang.GeneralDeclarativeProvisionalSelect323

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeProvisionalFailure323
open GeneralDeclarativeProvisionalFixture323
open GeneralDeclarativeProvisionalSelect323 (localRule before_tree)
open GeneralDeclarativeExampleSource320 (root child registry interp leaf checked point)
open GeneralDeclarativeExampleRead320 (leaf_only)
open GeneralDeclarativeExampleTree320 (dictionary)
open GeneralDeclarativeEmissionFixture322 (leafNames)
open GeneralDeclarativeExistingFixture322 (productType parentCapture nominalCode)
open GeneralDeclarativeHead320 (Models Equation)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralDeclarativeNodeFacts320 (nodeFacts)
open GeneralDeclarativeNamedTree320 (position)
open GeneralDeclarativeOutputExact323 (root_exact)
open GeneralDeclarativeOutputFacts320 (rootFact)
open GeneralDeclarativeOutputs320 (OutputMeaning)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralDeclarativeCompilerTree320 (Compiles compile_classify)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans eqv_symm)
open CommonNominalFullCarrier (Ty Equivalent)
open GeneralNominalBranchingReadback (scalar_not_pair)
open GeneralDeclarationExamples (wrap containerChild itemEquation)
open GeneralDeclarativeExampleRead320 (root_only)
open GeneralDeclarativeOutputs320 (bodyCapture bodyPattern)
open GeneralDeclarativeDemand320 (sourceValue)
open CommonNominalFullCarrier (nominal nominal_regular_invariant_exact)
open CommonRoleOutermostResolver (Classify All₂)

theorem real_fixed_row : rootFact registry interp leaf child leafNames.input ⟨1,5⟩ = some [row] := rfl

theorem real_child_compiler : nodeFacts registry interp leafNames.input leaf child [] =
    some [⟨3,.variable 3⟩,row] := rfl

theorem root_output_already_holds :
    OutputMeaning registry.roles registry.constructors interp wrap root parentCapture countermodel ⟨0,6⟩ :=
  (root_exact checked List.mem_cons_self
    (show rootFact registry interp wrap root parentCapture ⟨0,6⟩ =
      some [(⟨6,nominalCode (.variable 5)⟩ : Equation)] from rfl) countermodel).mpr (by
    exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _)

theorem no_child_evidence : ¬Evidence registry interp countermodel child (.node leaf.id []) := by
  intro proof
  cases proof with
  | node typed forest =>
    obtain ⟨decl,cap,_,node⟩ := typed
    cases leaf_only decl node.visible node.role
    have actual := position node.head
      (show child.arguments[0]? = some (point 3) from rfl)
      (show leaf.head[0]? = some (.var 0) from rfl)
    have head : Equivalent productType (countermodel (cap 0).center).1 := actual.1
    have exactRow : rootFact registry interp leaf child cap ⟨1,5⟩ =
        some [(⟨5,.variable (cap 0).center⟩ : Equation)] := rfl
    have output := (root_exact checked (List.mem_cons_of_mem _ List.mem_cons_self)
      exactRow countermodel).mp (node.outputs ⟨1,5⟩ List.mem_cons_self)
    have out : Equivalent (.base .int : Ty) (countermodel (cap 0).center).1 := output
    exact scalar_not_pair .int (.base .int) .top (eqv_trans out (eqv_symm head)).1

theorem nominal_payload {x y : Ty} (eq : Equivalent (nominal 0 [.inl x]) (nominal 0 [.inl y])) :
    Equivalent x y :=
  ((nominal_regular_invariant_exact ..).mp eq.1).2.2 0 (.inl x) (.inl y) rfl rfl

theorem no_root_evidence : ¬Evidence registry interp countermodel root dictionary := by
  intro proof
  cases proof with
  | node meaning kids =>
    obtain ⟨parentDecl,capture,_,parent⟩ := meaning
    cases root_only parentDecl parent.visible parent.role
    cases kids with
    | cons first tail =>
      cases tail
      have outer := (position parent.head
        (show root.arguments[0]? = some GeneralDeclarativeExampleSource320.input from rfl)
        (show wrap.head[0]? = some (.app 0 [.var 0]) from rfl)).1
      have input : Equivalent productType (countermodel (capture 0).center).1 := nominal_payload outer
      have rootRow : rootFact registry interp wrap root capture ⟨0,6⟩ =
          some [(⟨6,nominalCode (.variable (capture 1).center)⟩ : Equation)] := rfl
      have ret : Equivalent (.base .int : Ty) (countermodel (capture 1).center).1 :=
        nominal_payload ((root_exact checked List.mem_cons_self rootRow countermodel).mp
          (parent.outputs ⟨0,6⟩ List.mem_cons_self))
      rename_i childDemand
      have generated := position parent.children
        (show wrap.requirements[0]? = some containerChild from rfl)
        (show [childDemand][0]? = some childDemand from rfl)
      cases childDemand with
      | mk childRole args outs =>
        cases generated.arguments with
        | cons arg tailArgs =>
          cases tailArgs
          obtain ⟨_,_,_,_,actual⟩ := arg
          cases generated.outputs with
          | cons request restOut =>
            cases restOut
            cases first with
            | node childNode below =>
              obtain ⟨chosen,values,_,resolved⟩ := childNode
              cases leaf_only chosen resolved.visible (resolved.role.trans generated.role)
              cases resolved.head with
              | cons fromHead afterHead =>
                cases afterHead
                obtain ⟨body,supplied,read⟩ := resolved.outputs _ List.mem_cons_self
                cases supplied with
                | explicit eq member _ =>
                  cases List.mem_singleton.mp member
                  have atChild := eqv_trans (eqv_symm actual.1) fromHead.1
                  have equal : Equivalent productType (.base .int : Ty) :=
                    eqv_trans input (eqv_trans atChild (eqv_trans (eqv_symm read)
                      (eqv_trans request.2 (eqv_symm ret))))
                  exact scalar_not_pair .int (.base .int) .top equal.2
                | default rhs _ impossible =>
                  rw [request.1] at impossible
                  change some (none : Option Yulang.Roles.Term) = some (some rhs) at impossible
                  cases Option.some.inj impossible

/-- This is a counterexample for using syntax-only provisional selection
as the final all-model judgment, not for the approved closed-state rule. -/
theorem provisional_counterexample :
    Classify localRule root (.selected dictionary) ∧ Models before countermodel ∧
      ¬Evidence registry interp countermodel root dictionary :=
  ⟨before_tree,before_model,no_root_evidence⟩

theorem not_compiles : ¬Compiles before registry interp localRule :=
  fun all => no_root_evidence (compile_classify checked all countermodel before_model before_tree)

end Yulang.GeneralDeclarativeProvisionalFailure323
