import Yulang.GeneralDeclarativeExistingLocal322
import Yulang.GeneralNominalCenteredHeadMatSemanticSubstitution

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeDemandAliases322
open CommonNominalFullCarrier (Equivalent subtype_trans)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl eqv_trans eqv_symm)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Demand HeadMeaning sourceValue)
open GeneralDeclarativeOutputs320 (positional bodyCapture bodyPattern)
open GeneralDeclarativeAssembly320 (Meaning Node)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralSourceState (Output)
open CommonRoleOutermostResolver (All₂)

structure Arg (m : Assignment) (a b : Capture) : Prop where
  lower : Equivalent (m a.lower).1 (m b.lower).1
  actual : Equivalent (m a.center).1 (m b.center).1
  upper : Equivalent (m a.upper).1 (m b.upper).1

structure Name (m : Assignment) (a b : Output) : Prop where
  same : a.name = b.name
  value : Equivalent (m a.target).1 (m b.target).1

structure Same (m : Assignment) (a b : Demand) : Prop where
  role : a.role = b.role
  args : All₂ (Arg m) a.arguments b.arguments
  outputs : All₂ (Name m) a.outputs b.outputs

theorem head_transport {m : Assignment} {a b : Capture}
    (agree : Arg m a b) (head : HeadMeaning c interp capture m a p) :
    HeadMeaning c interp capture m b p :=
  ⟨eqv_trans (eqv_symm agree.actual) head.1,
    subtype_trans agree.lower.2 (subtype_trans head.2.1 agree.actual.1),
    subtype_trans agree.actual.2 (subtype_trans head.2.2 agree.upper.1)⟩

theorem transport_heads {m : Assignment} {fromArgs toArgs : List Capture}
    (same : All₂ (Arg m) fromArgs toArgs)
    (heads : All₂ (HeadMeaning c interp capture m) fromArgs patterns) :
    All₂ (HeadMeaning c interp capture m) toArgs patterns := by
  induction same generalizing patterns with
  | nil => cases heads; exact .nil
  | cons here _ ih =>
    cases heads with
    | cons first rest => exact .cons (head_transport here first) (ih rest)

theorem at_index {m : Assignment} {xs ys : List Capture}
    (args : All₂ (Arg m) xs ys) (i : Nat) :
    Equivalent (m ((xs[i]?.map Capture.center).getD 0)).1
      (m ((ys[i]?.map Capture.center).getD 0)).1 := by
  induction args generalizing i with
  | nil => exact eqv_refl _
  | cons here _ ih =>
    cases i with
    | zero => exact here.actual
    | succ j => exact ih j

theorem body_agrees {m : Assignment} {a b : Demand} (args : All₂ (Arg m) a.arguments b.arguments)
    (body : GeneralDictionaryAssociatedProvenance.Body) :
    Equivalent (sourceValue c interp (bodyCapture a capture body) m (bodyPattern body))
      (sourceValue c interp (bodyCapture b capture body) m (bodyPattern body)) := by
  cases body with
  | explicit eqn => exact eqv_refl _
  | default role name term =>
    apply GeneralNominalCenteredHeadMatSemanticSubstitution.eval_congr
    intro binder _
    exact at_index args binder

theorem lookup_prior {relation : α → β → Prop} {as : List α} {bs : List β}
    (order : All₂ relation as bs) {b : β} (there : b ∈ bs) :
    ∃ a ∈ as, relation a b := by
  induction order with
  | nil => cases there
  | cons first tail ih =>
    rcases List.mem_cons.mp there with rfl|later
    · exact ⟨_,List.mem_cons_self,first⟩
    · obtain ⟨a,seen,rel⟩ := ih later
      exact ⟨a,List.mem_cons_of_mem _ seen,rel⟩

/-- Logical aliases preserve semantic evidence, not literal emitted names.
No classification transport is claimed. Child order is unchanged.
The default RHS is read at equivalent actual positions, not at endpoints. -/
theorem node_transport {m : Assignment} {a b : Demand}
    (same : Same m a b) (node : Node r interp m a key children) :
    Node r interp m b key children := by
  obtain ⟨impl,capture,chosen,typing⟩ := node
  refine ⟨impl,capture,chosen,typing.visible,typing.role.trans same.role,typing.captures,
    transport_heads same.args typing.head,typing.children,?_⟩
  intro out there
  obtain ⟨prior,seen,alias⟩ := lookup_prior same.outputs there
  obtain ⟨body,supplies,returns⟩ := typing.outputs prior seen
  refine ⟨body,alias.same ▸ supplies,eqv_trans (eqv_symm alias.value) ?_⟩
  exact eqv_trans returns (body_agrees same.args body)

theorem evidence_transport {m : Assignment} {a b : Demand}
    (same : Same m a b) (proof : Evidence r interp m a dict) : Evidence r interp m b dict := by
  cases proof with
  | node nodeProof kids => exact .node (node_transport same nodeProof) kids

end Yulang.GeneralDeclarativeDemandAliases322
