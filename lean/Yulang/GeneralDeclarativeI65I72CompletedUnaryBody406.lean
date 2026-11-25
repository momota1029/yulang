import Yulang.GeneralDeclarativeI65I72CompletedUnaryPayload406

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72
open GeneralDeclarativeI65
open GeneralDeclarations (Clause)
open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeHead320 (Equation environment)
open GeneralNominalCenteredHeadMatExpressions (Expr value)
open CommonNominalFullCarrier (Equivalent)

structure CompletedBody406 {s q row needs forest}
    {chosen : PreselectedUnary406 s q row (needs := needs) forest}
    (payload : OriginalPayload406 chosen) where
  output : ∀ i : Fin q.demand.outputs.length,
    NamedMixedOutput401 s.b6 (originalNativeFrame406 chosen payload) i

def CompletedBody406.written {s q row needs forest}
    {chosen : PreselectedUnary406 s q row (needs := needs) forest} {payload : OriginalPayload406 chosen}
    (body : CompletedBody406 payload) : List (NamedMixedReceipt401 s.core) :=
  List.ofFn (fun i => (body.output i).receipt)

def CompletedBody406.Fixed {s q row needs forest}
    {chosen : PreselectedUnary406 s q row (needs := needs) forest} {payload : OriginalPayload406 chosen}
    (body : CompletedBody406 payload) : Prop :=
  ∀ i : Fin q.demand.outputs.length, ∃ rhs : Expr,
    fixedValueCode403 (body.output i).rhs = some rhs ∧
    (⟨q.demand.outputs[i].target,rhs⟩ : Equation) ∈ s.core.current.ordinary.equations

/-- Emission is on the exact pre-output frame. Its arity is proved
from the literal original unary request and declaration, with no
old SourceHead/ModeWindow construction or replacement endpoint. -/
theorem original_completed_native_body_reads_B6406 {s q row needs forest}
    {chosen : PreselectedUnary406 s q row (needs := needs) forest} (payload : OriginalPayload406 chosen)
    (declared : DeclaredOriginalOutputs400 s.core q)
    (typed : NamedInputAtStoredHead401 s.b6 (originalNativeFrame406 chosen payload)) :
    Nonempty (CompletedBody406 payload) := by
  classical
  let f := originalNativeFrame406 chosen payload
  have check := chosen.gate.checked.2 f.decl (List.mem_of_getElem? f.authored)
  have role := (visible_exact s.core q f.decl).mp f.inScope |>.2
  have arity : q.demand.arguments.length = f.decl.head.length := by
    change q.demand.arguments.length = row.head.length
    rw [chosen.gate.exactArg,chosen.gate.exactHead]
    rfl
  have output (i : Fin q.demand.outputs.length) : Nonempty (NamedMixedOutput401 s.b6 f i) := by
    obtain ⟨body,supply⟩ := GeneralDictionaryAssociatedProvenance.declared_covered
      (authoredRegistry s.core.current).roles f.decl check.signature q.demand.outputs[i].name (role ▸ declared i)
    obtain ⟨plan,original⟩ := typed i body supply
    obtain ⟨rhs,substituted⟩ := exact_mixed_names_are_substitutable401 (f.slots body) plan
      (original_frame_slot_coverage399 f chosen.gate.checked arity
        (default_positions_from_authored_role_decl399 s.core) supply)
    exact ⟨⟨body,supply,plan,original,rhs,substituted⟩⟩
  exact ⟨⟨fun i => Classical.choice (output i)⟩⟩

theorem completed_body_keeps_original_replay_addresses406 {s q row needs forest}
    {chosen : PreselectedUnary406 s q row (needs := needs) forest} {payload : OriginalPayload406 chosen}
    (body : CompletedBody406 payload) :
    body.written.length = q.demand.outputs.length ∧
    ∀ i : Fin q.demand.outputs.length,
      body.written[i.val]? = some (body.output i).receipt ∧
      (body.output i).receipt.occurrence = q.occurrence ∧
      (body.output i).receipt.outputOrdinal = i.val ∧
      (body.output i).receipt.original = q.demand.outputs[i] := by
  refine ⟨by simp [CompletedBody406.written],fun i => ?_⟩
  rw [CompletedBody406.written,List.getElem?_ofFn,dite_eq_left i.isLt]
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem completed_body_exact_type_and_fixed_in_one_model406 {s q row needs forest}
    {chosen : PreselectedUnary406 s q row (needs := needs) forest} {payload : OriginalPayload406 chosen}
    (body : CompletedBody406 payload) (fixed : body.Fixed) (m : Model) (fit : Fits s m) :
    ∀ i : Fin q.demand.outputs.length,
      ExactNamedOutputMeaning401 m (body.output i) ∧
      ∃ v, (body.output i).receipt.actualEquation m = some (q.demand.outputs[i].target,v) ∧
        Equivalent (m.assignment q.demand.outputs[i].target).1 v := by
  intro i
  refine ⟨original_named_mixed_output_meaning401 m (body.output i) chosen.gate.checked,?_⟩
  obtain ⟨code,decoded,retained⟩ := fixed i
  have denotes := fixed_value_code_same_model403 (body.output i).rhs m code decoded
  refine ⟨value (environment m.assignment) .actual code,?_,fit.1.1.2 _ retained⟩
  simp only [NamedMixedReceipt401.actualEquation,NamedMixedOutput401.receipt,denotes,Option.map_some]

theorem completed_body_generates_exact_literal_where406 {s q row needs forest}
    {chosen : PreselectedUnary406 s q row (needs := needs) forest} (payload : OriginalPayload406 chosen)
    (clauses : LiteralVariableWhere403 row)
    {i : Nat} {clause : Clause} (written : row.requirements[i]? = some clause) :
    ∃ binders : List Nat, clause.arguments = binders.map Pattern.var ∧
      (frameWhereKids400 (originalNativeFrame406 chosen payload))[i]? =
        some (⟨q.occurrence ++ [i],⟨clause.role,binders.map (originalNativeFrame406 chosen payload).input,[]⟩⟩ :
          Request) :=
  literal_where_child_at403 (originalNativeFrame406 chosen payload) clauses chosen.gate.checked written

end Yulang.GeneralDeclarativeI65.I72
