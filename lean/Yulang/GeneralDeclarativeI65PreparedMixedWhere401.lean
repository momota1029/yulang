import Yulang.GeneralDeclarativeI65SingleStoredFrame401
import Yulang.GeneralDeclarativeI65PreparedSourceBindings395

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open CommonRoleOutermostResolver (Dictionary)
open GeneralDeclarations (Checked OutputBinder Equation)
open GeneralDictionaryAssociatedProvenance (Supplies)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open CommonNominalFullCarrier (Ty)
open GeneralDeclarationPatterns (normalize)
open GeneralDeclarativeOutputs320 (bodyPattern)

theorem prepared_source_has_exact_mixed_output401 {s q}
    (prepared : PreparedSourceFrame395 s q) (selected : PreparedSelection395 prepared)
    (checked : Checked (authoredRegistry s.current)) (declared : DeclaredOriginalOutputs400 s q)
    (atlas : B6OccurrenceAtlas401 s) (input : NamedInputAtStoredHead401 atlas prepared.frame)
    (i : Fin q.demand.outputs.length) :
    ∃ output : NamedMixedOutput401 atlas prepared.frame i,
      ∀ m : Model, ∃ ty, output.receipt.actualEquation m = some (q.demand.outputs[i].target,ty) ∧
        evaluateMixedRhs401 (sourceRead401 m (prepared.frame.slots output.body)) output.plan = some ty := by
  have localDecl := checked.2 prepared.ctx.decl (List.mem_of_getElem? prepared.authored)
  have role := (visible_exact s q prepared.ctx.decl).mp prepared.visibleIn |>.2
  have original : q.demand.arguments.length = prepared.frame.decl.head.length :=
    observed_preoutput_demand_head_lengths399 selected.origin.pick.head
  obtain ⟨body,which⟩ := GeneralDictionaryAssociatedProvenance.declared_covered
    (authoredRegistry s.current).roles prepared.ctx.decl localDecl.signature
    q.demand.outputs[i].name (role ▸ declared i)
  obtain ⟨plan,typed⟩ := input i body which
  have covered := original_frame_slot_coverage399 prepared.frame checked original
    (default_positions_from_authored_role_decl399 s) which
  obtain ⟨rhs,formed⟩ := exact_mixed_names_are_substitutable401 (prepared.frame.slots body) plan covered
  let output : NamedMixedOutput401 atlas prepared.frame i := ⟨body,which,plan,typed,rhs,formed⟩
  exact ⟨output,fun m => named_mixed_output_is_fixed_equation401 output m⟩

structure ChildMixedReceiptTree401 {source s} (atlas : B6OccurrenceAtlas401 s)
    (child : Request) (dicts : List Dictionary) (ordinal : Nat) where
  chosen : Dictionary
  atOriginal : dicts[ordinal]? = some chosen
  subtree : GuardedFrameTree400 source s child chosen
  sameReceipts : MixedReceiptsAtTree401 atlas subtree

/-- Structural lookup in the original addressed where forest (including
duplicates), not by numerical target or equal diagnostic summary. -/
def mixedChildTreeAt401 {source s atlas nodes dicts child}
    {forest : GuardedFrameForest400 source s nodes dicts}
    (retained : MixedReceiptsAtForest401 atlas forest)
    (i : Nat) (atNode : nodes[i]? = some child) :
    ChildMixedReceiptTree401 (source := source) atlas child dicts i := by
  cases retained with
  | nil => simp at atNode
  | cons first rest =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at atNode
      subst child
      exact ⟨_,rfl,_,first⟩
    | succ i =>
      let found := mixedChildTreeAt401 rest i (by simpa using atNode)
      exact ⟨found.chosen,by simpa using found.atOriginal,found.subtree,found.sameReceipts⟩

def MixedReceiptsAtTree401.atOriginalOutput {source s q d atlas}
    {tree : GuardedFrameTree400 source s q d} (retained : MixedReceiptsAtTree401 atlas tree)
    (i : Fin q.demand.outputs.length) :
    Σ f : AuthoredBodyFrame393 s q, MixedOutput401 atlas f i := by
  cases retained with
  | node out _ => exact ⟨_,out.each i⟩

/-- Exact child/ordinal and actual RHS on a parent where slot. Reading
the slot is in the same State/model and binds to the fixed target;
equating that target's assigned value with the RHS would need
retention and is *not* proved here. -/
theorem prepared_mixed_where_slot_reads_original_child401 {source s q atlas dicts binder body}
    (p : PreparedSourceFrame395 s q) (origin : OriginalWhereBinder395 p.frame binder body)
    {forest : GuardedFrameForest400 source s (frameWhereKids400 p.frame) dicts}
    (sameWhere : MixedReceiptsAtForest401 atlas forest) :
    let child := mixedChildTreeAt401 sameWhere origin.clauseOrdinal origin.child_position
    let output := child.sameReceipts.atOriginalOutput origin.outputIndex
    dicts[origin.clauseOrdinal]? = some child.chosen ∧
    output.2.receipt.occurrence = q.occurrence ++ [origin.clauseOrdinal] ∧
    output.2.receipt.ordinal = origin.outputOrdinal ∧
    output.2.receipt.requested = origin.output ∧
    p.frame.slots (.explicit body) binder.name =
      some ⟨output.2.receipt.requested.target,output.2.receipt.requested.target,
        output.2.receipt.requested.target⟩ ∧
    ∀ m : Model, ∃ v : Ty, output.2.receipt.actualEquation m = some (origin.output.target,v) ∧
      evaluateMixedRhs401 (sourceRead401 m (output.1.slots output.2.body)) output.2.plan = some v := by
  let child := mixedChildTreeAt401 sameWhere origin.clauseOrdinal origin.child_position
  let output := child.sameReceipts.atOriginalOutput origin.outputIndex
  have same : output.2.receipt.requested = origin.output :=
    (List.getElem?_eq_some_iff.mp origin.outputAt).2
  refine ⟨child.atOriginal,rfl,rfl,same,?_,?_⟩
  · rw [same]
    exact origin.slot
  · intro m
    obtain ⟨v,got,effects⟩ := mixed_write_same_model_fixed_target401 output.2 m
    have eq : origin.child.demand.outputs[origin.outputIndex].target = origin.output.target :=
      congrArg GeneralSourceState.Output.target same
    exact ⟨v,eq ▸ got,effects⟩

end Yulang.GeneralDeclarativeI65
