import Yulang.GeneralNominalTraceDictionary197
import Yulang.GeneralNominalRefinements

set_option backward.isDefEq.respectTransparency false
/-! Actual source-preserving refinements with unchanged source slots retain every
old nominal descriptor. Successful nominal-only observation trees consequently
recheck without any caller-supplied agreement about new descriptors or reports.
Scalar and structural observations are deliberately outside this theorem. -/
namespace Yulang.GeneralNominalRefinementTrace197
open GeneralNominalInspection (Query Bounds)
open GeneralNominalRecursiveInspection
open GeneralNominalViewTransport196
open GeneralNominalInspectionTrace197

mutual
  inductive Observed (state : GeneralNominalState.State) : Query → Bounds state → Prop where
    | variables : Observed state (.variables names) bounds
    | point (recorded : state.nominals slot = some descriptor)
        (name : descriptor.declaration.name = expected)
        (arguments : typeArguments descriptor.arguments = some actuals)
        (children : ObservedMany state patterns actuals) :
        Observed state (.nominal expected patterns) (slot,slot)
    | interval (different : bounds.1 ≠ bounds.2)
        (lowerRecorded : state.nominals bounds.1 = some lower)
        (upperRecorded : state.nominals bounds.2 = some upper)
        (lowerName : lower.declaration.name = expected)
        (upperName : upper.declaration.name = expected)
        (lowerArguments : typeArguments lower.arguments = some left)
        (upperArguments : typeArguments upper.arguments = some right)
        (lowerChildren : ObservedMany state patterns left)
        (upperChildren : ObservedMany state patterns right) :
        Observed state (.nominal expected patterns) bounds
  inductive ObservedMany (state : GeneralNominalState.State) : List Query → List (Bounds state) → Prop where
    | nil : ObservedMany state [] []
    | cons : Observed state query bounds → ObservedMany state queries intervals →
        ObservedMany state (query :: queries) (bounds :: intervals)
end

theorem embedding_identity (refinement : GeneralNominalRefinements.Refines state (replace state next)) :
    refinement.base.embed = id := by
  funext slot
  apply state.base.source_injective
  exact refinement.base.source slot

theorem rename_identity (descriptor : GeneralNominalState.Descriptor count) :
    GeneralNominalRefinements.renameDescriptor id descriptor = descriptor := by
  have identity : GeneralNominalRefinements.renameParameter (id : Fin count → Fin count) = id := by
    funext parameter
    cases parameter <;> rfl
  cases descriptor
  simp only [GeneralNominalRefinements.renameDescriptor, identity, List.map_id]

theorem nominal_preserved
    (refinement : GeneralNominalRefinements.Refines state (replace state next))
    (recorded : state.nominals slot = some descriptor) :
    next.nominals slot = some descriptor := by
  have preserved := refinement.nominals slot descriptor recorded
  rw [embedding_identity refinement,rename_identity] at preserved
  exact preserved

mutual
  theorem traced (refinement : GeneralNominalRefinements.Refines state (replace state next))
      (observed : Observed state query bounds) : Trace state next query bounds := by
    cases observed with
    | variables => exact .variables
    | point recorded name arguments children =>
      exact .nominalPoint recorded (nominal_preserved refinement recorded) name arguments
        (tracedMany refinement children)
    | interval different lower upper lowerName upperName lowerArgs upperArgs left right =>
      exact .nominalInterval different lower (nominal_preserved refinement lower)
        upper (nominal_preserved refinement upper) lowerName upperName lowerArgs upperArgs
        (tracedMany refinement left) (tracedMany refinement right)
  termination_by sizeOf query
  theorem tracedMany (refinement : GeneralNominalRefinements.Refines state (replace state next))
      (observed : ObservedMany state queries bounds) : Traces state next queries bounds := by
    cases observed with
    | nil => exact .nil
    | cons head tail => exact .cons (traced refinement head) (tracedMany refinement tail)
  termination_by sizeOf queries
end

theorem rechecked (old : GeneralNominalCandidates.Context) (next : View old.state)
    (declaration : GeneralDeclarations.Declaration) (bounds : List (Bounds old.state))
    (refinement : GeneralNominalRefinements.Refines old.state (replace old.state next))
    (observed : ObservedMany old.state
      (GeneralNominalInspection.queries old.state old.interpretation declaration) bounds) :
    Rechecked old next declaration bounds :=
  rechecked_of_trace old next declaration bounds (tracedMany refinement observed)

/-- Evidence-independent observations from only the old context, at actual used
keys and argument lookups. No future descriptor or report appears here. -/
def AtNode (registry : GeneralDeclarations.Registry) (old : GeneralNominalCandidates.Context)
    (root : GeneralSourceDictionaries.Occurrence roles) (key : Nat) : Prop :=
  ∀ declaration ∈ registry.declarations, declaration.id = key →
    ∀ bounds, GeneralNominalRecursiveCandidates.arguments old root = some bounds →
      ObservedMany old.state
        (GeneralNominalInspection.queries old.state old.interpretation declaration) bounds

inductive TreeObserved (registry : GeneralDeclarations.Registry)
    (old : GeneralNominalCandidates.Context) : GeneralSourceDictionaries.Dictionary roles → Prop where
  | node (atNode : AtNode registry old root key)
      (children : ∀ child ∈ trees, TreeObserved registry old child) :
      TreeObserved registry old (.node root key trees)

theorem tree_traced {old : GeneralNominalCandidates.Context} {next : View old.state}
    (refinement : GeneralNominalRefinements.Refines old.state (replace old.state next))
    (observed : TreeObserved registry old tree) :
    GeneralNominalTraceDictionary197.TreeTrace registry old next tree := by
  induction observed with
  | node atNode _ ih =>
    exact .node (fun declaration member key bounds lookup =>
      tracedMany refinement (atNode declaration member key bounds lookup)) ih

/-- The actual refresh certificate supplies nominal preservation automatically.
Only old successful nominal observations and old model evidence are needed. -/
theorem universal_refresh {state : GeneralNominalCenteredHeadStepEffects.State roles}
    {next : View state.core.erased.current.context.state}
    (certificate : GeneralNominalCenteredSteps.Refresh state.core
      (context state.core.erased.current.context next))
    (observed : TreeObserved registry state.core.erased.current.context tree)
    (readback : GeneralSourceDictionaries.Readback root payload tree)
    (source : ∀ model, GeneralNominalCenteredHeadStepEffects.Models state model →
      GeneralSourceDictionaries.Evidence
        (GeneralDictionaryRecursiveEvidence.Instance registry state.core.erased.current.context model) tree) :
    ∀ model, GeneralNominalCenteredHeadStepEffects.Models
      (GeneralNominalCenteredHeadStepKernel.refresh state (context state.core.erased.current.context next)) model →
      (GeneralNominalCenteredHeadWFBoundary.boundary roles).Evidence registry
        (GeneralNominalCenteredHeadStepKernel.refresh state (context state.core.erased.current.context next))
        model root payload :=
  GeneralNominalTraceDictionary197.universal_refresh certificate
    (tree_traced certificate.refines observed) readback source
end Yulang.GeneralNominalRefinementTrace197
