import Yulang.GeneralRebasePrivateChild282

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebasePrivateRequests282
open GeneralNominalCenters (Plan)
open GeneralRebasePrivateKey282 (port Excludes)
open GeneralRebasePrivateChild282 (child_site child_arguments child_output_target)
open GeneralRebasePrivateHead282 (schema_private)
open GeneralNominalCenteredHeadMatSchemas (Schema Equation generated materialize emissionRequests inputRequests)
open GeneralNominalMaterialization (Request)
open GeneralNominalVersionedPlans231 (childRequests emittedRequests childSchema emittedSchema)
open GeneralDeclarations
open GeneralNominalVersionedFrame231 (frame capture childSite)
open GeneralRebaseAggregateTags281 (Tag)

theorem generated_target (catalogue : GeneralDeclarationPatterns.Constructors)
    (interp : GeneralNominalInspection.Interpretation) (requests : List Request)
    (equation : GeneralNominalCenteredHeadMatSchemas.Equation) (member : equation ∈ (generated catalogue interp requests).equations) :
    ∃ request ∈ requests, equation.target = request.target := by
  induction requests with
  | nil => cases member
  | cons first rest ih =>
    change equation ∈ (materialize catalogue interp first).equations ++ (generated catalogue interp rest).equations at member
    rcases List.mem_append.mp member with one|last
    · unfold materialize at one
      split at one
      · obtain rfl := List.mem_singleton.mp one
        exact ⟨first,List.mem_cons_self,rfl⟩
      · cases one
    · obtain ⟨req,found,same⟩ := ih last
      exact ⟨req,List.mem_cons_of_mem _ found,same⟩

theorem child_schema_private {q : Plan roles} (absent : Excludes q.packet owner decl tag)
    (clause : Clause) (valid : clause.Signature roles) :
    port q.packet.context.state.seed owner decl tag ∉
      GeneralNominalVersionedExpressionFrame236.schemaSources q (childSchema q clause valid) := by
  apply schema_private absent
  intro e listed
  obtain ⟨r,used,same⟩ := generated_target _ _ _ e listed
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp used
  rw [same]
  exact (child_site absent clause valid i).2.2

def OutputSafe (q : Plan roles) (target : Nat) : Prop :=
  ∀ output ∈ q.packet.site.occurrence.demand.outputs, target ≠ (output : GeneralSourceState.Output).target

theorem emitted_target {q : Plan roles} (absent : Excludes q.packet owner decl tag)
    (safe : OutputSafe q (port q.packet.context.state.seed owner decl tag))
    (r : Request) (listed : r ∈ emittedRequests q.packet) :
    port q.packet.context.state.seed owner decl tag ≠ r.target := by
  rcases List.mem_append.mp listed with root | child
  · obtain ⟨out,used,equal⟩ := GeneralNominalGeneratedSupport184.root_request_target _ _ r root
    rw [equal]
    exact safe out used
  · obtain ⟨emission,used,originMem⟩ := List.mem_flatMap.mp child
    unfold GeneralCanonicalChildOrder.canonicalEmit at used
    obtain ⟨clause,existsClause,rfl⟩ := List.mem_map.mp used
    let valid := q.packet.checked.signature.2.2.2 clause.val
      ((GeneralCanonicalChildOrder.canonicalRequirements_perm _).mem_iff.mpr clause.property)
    rcases List.mem_append.mp originMem with inputs | outputs
    · obtain ⟨inp,member,rule⟩ := List.mem_flatMap.mp inputs
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp member
      rcases List.mem_cons.mp rule with rfl|rule
      · exact (child_arguments absent clause.val valid i).1
      · obtain rfl := List.mem_singleton.mp rule
        exact (child_arguments absent clause.val valid i).2
    · obtain ⟨a,one,rfl⟩ := List.mem_map.mp outputs
      obtain ⟨eqn,two,rfl⟩ := List.mem_map.mp one
      exact child_output_target q tag clause.val eqn

theorem emitted_schema_private {q : Plan roles} (absent : Excludes q.packet owner decl tag)
    (safe : OutputSafe q (port q.packet.context.state.seed owner decl tag)) :
    port q.packet.context.state.seed owner decl tag ∉
      GeneralNominalVersionedExpressionFrame236.schemaSources q (emittedSchema q) := by
  apply schema_private absent
  intro e listed
  obtain ⟨r,used,same⟩ := generated_target _ _ _ e listed
  rw [same]
  exact emitted_target absent safe r used

end Yulang.GeneralRebasePrivateRequests282
