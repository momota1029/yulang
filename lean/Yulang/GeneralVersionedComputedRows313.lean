import Yulang.GeneralVersionedFirstInternal313

set_option backward.isDefEq.respectTransparency false
/-! Computed where outputs use the real purpose-5 allocator, which does
not carry a clause coordinate. Coherence therefore depends on the equation
ID across all clauses, unlike compound input cells. -/
namespace Yulang.GeneralVersionedComputedRows313
open GeneralDeclarations GeneralDeclarationPatterns GeneralNominalCenters
open GeneralNominalVersionedFrame231 (capture frame binder)
open GeneralNominalVersionedPlans231 (variables childSchema)
open GeneralNominalMaterialization (Mode Request)
open GeneralNominalCenteredHeadMatSchemas (generated materialize)
open GeneralNominalCenteredHeadMatExpressions (translate)
open GeneralNominalCommonBridge (Assignment)
open GeneralVersionedRootWrites312 (inner whereRequests from_request)
open GeneralVersionedCompoundRows313 (address Taut Cell materializes)
open GeneralVersionedNormalizedVariable313 (normalized_value)

abbrev Compiled := GeneralNominalCenteredHeadMatSchemas.Equation

def Forwarded (d : Declaration) (e : GeneralDeclarations.Equation) : Prop :=
  ∃ n, normalize e.rhs = .var n ∧ n ∈ d.outputNames

def OutputCell (p : Plan roles) (eq : Compiled) : Prop :=
  ∃ clause ∈ p.packet.declaration.requirements, ∃ rule ∈ clause.outputs,
    ¬ Forwarded p.packet.declaration rule ∧
    translate p.packet.registry.constructors p.packet.context.interpretation rule.rhs = some eq.expression ∧
    eq.target = address p 5 rule.id 0 ∧ eq.mode = .actual

def KeyCoherent (d : Declaration) : Prop :=
  ∀ first ∈ d.requirements, ∀ a ∈ first.outputs, ¬ Forwarded d a →
    ∀ last ∈ d.requirements, ∀ b ∈ last.outputs, ¬ Forwarded d b →
    a.id = b.id → a.rhs = b.rhs

theorem output_target (p : Plan roles) (clause : Clause) (rule : GeneralDeclarations.Equation)
    (computed : ¬ Forwarded p.packet.declaration rule) :
    GeneralDeclarationDemands.outputTarget p.packet.declaration (capture p.packet)
      ((frame p.packet).allocation p.packet.declaration.id clause).outputs rule = address p 5 rule.id 0 := by
  unfold GeneralDeclarationDemands.outputTarget
  split
  · rename_i name norm
    split
    · rename_i isOut
      exact False.elim (computed ⟨name,norm,isOut⟩)
    · rfl
  · rfl

theorem output_row (p : Plan roles) (clause : Clause) (inClause : clause ∈ p.packet.declaration.requirements)
    (rule : GeneralDeclarations.Equation) (inClauseOutput : rule ∈ clause.outputs)
    (eq : Compiled)
    (member : eq ∈ (materialize p.packet.registry.constructors p.packet.context.interpretation
      ⟨rule.rhs,GeneralDeclarationDemands.outputTarget p.packet.declaration (capture p.packet)
        ((frame p.packet).allocation p.packet.declaration.id clause).outputs rule,.actual⟩).equations) :
    Taut p eq ∨ OutputCell p eq := by
  classical
  obtain ⟨compiled,target,atMode⟩ := materializes member
  by_cases forwarded : Forwarded p.packet.declaration rule
  · obtain ⟨n,norm,out⟩ := forwarded
    left
    intro m
    have next : eq.target = (capture p.packet).outputs n := by
      rw [target]
      simp only [GeneralDeclarationDemands.outputTarget,norm,out,ite_true]
    have agreement := normalized_value rule.rhs norm compiled (variables p m) .actual
    unfold GeneralNominalCenteredHeadMatSchemas.Equation.Holds
    rw [next,atMode]
    simp only [variables,binder,out,ite_true] at agreement
    exact GeneralFiniteTypedWrites312.symmetric agreement
  · right
    exact ⟨clause,inClause,rule,inClauseOutput,forwarded,compiled,
      target.trans (output_target p clause rule forwarded),atMode⟩

theorem emitted_rows (p : Plan roles) (eq : Compiled)
    (found : eq ∈ (generated p.packet.registry.constructors p.packet.context.interpretation
      (whereRequests p)).equations) : Taut p eq ∨ Cell p eq ∨ OutputCell p eq := by
  obtain ⟨rq,seen,materialized⟩ := from_request found
  obtain ⟨emit,emitted,inside⟩ := List.mem_flatMap.mp seen
  have posted := (GeneralCanonicalChildOrder.canonicalEmit_perm p.packet.site.occurrence.identity p.packet.declaration
    p.packet.checked (capture p.packet) ((frame p.packet).allocation p.packet.declaration.id)).mem_iff.mpr emitted
  unfold GeneralDeclarationDemands.emitAll at posted
  obtain ⟨item,_,rfl⟩ := List.mem_map.mp posted
  let clause := item.val
  have requirement := p.packet.checked.signature.2.2.2 clause item.property
  unfold GeneralNominalCenteredHeadMatSchemas.emissionRequests at inside
  rcases List.mem_append.mp inside with input|output
  · have rule : Taut p eq ∨ Cell p eq := by
      obtain ⟨arg,args,byArg⟩ := List.mem_flatMap.mp input
      obtain ⟨index,rfl⟩ := List.mem_ofFn.mp args
      rcases List.mem_cons.mp byArg with rfl|next
      · exact GeneralVersionedCompoundRows313.lower_or_upper p clause item.property requirement index 3 (.inl rfl) eq materialized
      · cases List.mem_singleton.mp next
        exact GeneralVersionedCompoundRows313.lower_or_upper p clause item.property requirement index 4 (.inr rfl) eq materialized
    exact rule.elim Or.inl (fun h => .inr (.inl h))
  · obtain ⟨request,requestMember,rfl⟩ := List.mem_map.mp output
    obtain ⟨rule,ruleMember,rfl⟩ := List.mem_map.mp requestMember
    exact (output_row p clause item.property rule ruleMember eq materialized).elim Or.inl (fun h => .inr (.inr h))

theorem classifies (p : Plan roles) (eq : Compiled) (found : eq ∈ inner p) :
    Taut p eq ∨ Cell p eq ∨ OutputCell p eq := by
  rcases List.mem_append.mp found with whereEq|childEq
  · exact emitted_rows p eq whereEq
  · obtain ⟨clause,_,here⟩ := List.mem_flatMap.mp childEq
    exact (GeneralVersionedCompoundRows313.center p clause.val clause.property _ eq here).elim
      Or.inl (fun h => .inr (.inl h))

theorem addresses_disjoint {p : Plan roles} {a b : Compiled}
    (center : Cell p a) (output : OutputCell p b) : a.target ≠ b.target := by
  intro equal
  obtain ⟨clause,_,pos,kind,pat,kindProof,_,_,target,_⟩ := center
  obtain ⟨_,_,rule,_,_,_,second,_⟩ := output
  have key := (GeneralNominalIdentities.source_identity p.packet.context.state.seed _ _).mp (target.symm.trans (equal.trans second))
  have tag := congrArg (fun o : GeneralNominalIdentities.Origin => o.2.2.1) key
  change kind = 5 at tag
  rcases kindProof with h|h|h <;> omega

theorem output_coherent {p : Plan roles} {a b : Compiled}
    (keys : KeyCoherent p.packet.declaration)
    (left : OutputCell p a) (right : OutputCell p b) (same : a.target = b.target) : a = b := by
  obtain ⟨c,hc,x,one,notForwardOne,atX,ax,mx⟩ := left
  obtain ⟨d,hd,y,two,notForwardTwo,atY,byTarget,my⟩ := right
  have eq := (GeneralNominalIdentities.source_identity p.packet.context.state.seed _ _).mp
    (ax.symm.trans (same.trans byTarget))
  have outputKey : x.id = y.id := congrArg (fun o : GeneralNominalIdentities.Origin => o.2.2.2.1) eq
  have rhs := keys c hc x one notForwardOne d hd y two notForwardTwo outputKey
  rw [rhs] at atX
  have equal := Option.some.inj (atX.symm.trans atY)
  cases a; cases b; simp_all


theorem row_present {p : Plan roles} {eq : Compiled} (cell : OutputCell p eq) :
    eq ∈ (GeneralNominalVersionedPlans231.emittedSchema p).equations := by
  obtain ⟨clause,required,rule,requested,computed,compiled,target,mode⟩ := cell
  let signature := p.packet.checked.signature.2.2.2 clause required
  let allocation := (frame p.packet).allocation p.packet.declaration.id clause
  let emission := GeneralDeclarationDemands.emit p.packet.site.occurrence.identity p.packet.declaration
    clause signature (capture p.packet) allocation
  have member : emission ∈ GeneralDeclarationDemands.emitAll p.packet.site.occurrence.identity
      p.packet.declaration p.packet.checked.signature (capture p.packet) ((frame p.packet).allocation p.packet.declaration.id) :=
    List.mem_map.mpr ⟨⟨clause,required⟩,by simp,rfl⟩
  have canon := (GeneralCanonicalChildOrder.canonicalEmit_perm p.packet.site.occurrence.identity
    p.packet.declaration p.packet.checked (capture p.packet) ((frame p.packet).allocation p.packet.declaration.id)).mem_iff.mp member
  let rq : Request := ⟨rule.rhs,GeneralDeclarationDemands.outputTarget p.packet.declaration (capture p.packet)
    allocation.outputs rule,.actual⟩
  have req : rq ∈ GeneralNominalVersionedPlans231.emittedRequests p.packet :=
    List.mem_append_right _ (List.mem_flatMap.mpr ⟨emission,canon,List.mem_append_right _
      (List.mem_map.mpr ⟨_,List.mem_map.mpr ⟨rule,requested,rfl⟩,rfl⟩)⟩)
  have targetEq : eq.target = rq.target := target.trans (output_target p clause rule computed).symm
  have ready := GeneralNominalCenteredHeadMatSchemas.generated_contains req compiled
  change (⟨rq.target,rq.mode,eq.expression⟩ : Compiled) ∈
    (GeneralNominalVersionedPlans231.emittedSchema p).equations at ready
  rw [← targetEq] at ready
  have rqMode : rq.mode = eq.mode := mode.symm
  rw [rqMode] at ready
  cases eq
  exact ready

end Yulang.GeneralVersionedComputedRows313
