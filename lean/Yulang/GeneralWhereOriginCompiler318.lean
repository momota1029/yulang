import Yulang.GeneralWhereVersionRecordedReuse317

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 22000
set_option maxHeartbeats 16000000
namespace Yulang.GeneralWhereOriginCompiler318
open GeneralDeclarations GeneralDeclarationPatterns GeneralNominalCenters
open GeneralWhereVersionCompiler317 (args allocation emit emissions schema)
open GeneralVersionedEndpointAddress315 (Side atCell)
open GeneralWhereVersionStoredRow317 (Endpoint)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralNominalCenteredHeadMatSchemas (Equation emissionRequests inputRequests generated_contains)
open GeneralNominalVersionedFrame231 (capture)
open GeneralNominalMaterialization (Request)

/-- Exact materialized row from the same checked source and endpoint
allocation used by the compiler; no caller-supplied descriptor. -/
theorem materialized {p : Plan rs} {clause : Clause} {index : Nat}
    (listed : clause ∈ p.packet.declaration.requirements)
    {pattern : Pattern} (located : clause.arguments[index]? = some pattern)
    (compound : ∀ n, normalize pattern ≠ .var n)
    {expr : Expr} (code : translate p.packet.registry.constructors p.packet.context.interpretation pattern = some expr)
    (side : Side) :
    let row : GeneralNominalCenteredHeadMatSchemas.Equation := ⟨atCell p side clause.id index expr,side.mode,expr⟩
    row ∈ (schema p).equations ∧ Endpoint p side clause index row := by
  dsimp only
  refine ⟨?_,⟨⟨listed,⟨pattern,located,code⟩,rfl⟩,rfl⟩⟩
  let sig := p.packet.checked.signature.2.2.2 clause listed
  obtain ⟨inRange,equals⟩ := List.getElem?_eq_some_iff.mp located
  let i : Fin (rs clause.role).arity := ⟨index,by rw [← sig.1]; exact inRange⟩
  let em := emit p clause sig
  have member : em ∈ emissions p := by
    apply (GeneralCanonicalChildOrder.canonicalEmit_perm p.packet.site.occurrence.identity
      p.packet.declaration p.packet.checked (capture p.packet) (allocation p)).mem_iff.mp
    exact List.mem_map.mpr ⟨⟨clause,listed⟩,by simp,rfl⟩
  let pat := clause.arguments[i.val]'(by rw [sig.1]; exact i.isLt)
  have samePat : pat = pattern := equals
  have alloc : args p clause i =
      (atCell p .lower clause.id index expr,atCell p .upper clause.id index expr) := by
    unfold args
    have localLookup : clause.arguments[i.val]? = some pattern := located
    simp only [localLookup,code]
    rfl
  have bounds :
      GeneralDeclarationDemands.inputInterval (capture p.packet) ((allocation p clause).arguments i) pat =
      (atCell p .lower clause.id index expr,atCell p .upper clause.id index expr) := by
    rw [samePat]
    unfold GeneralDeclarationDemands.inputInterval
    split
    · rename_i n found
      exact False.elim (compound n found)
    · exact alloc
  let rq : Request := ⟨pattern,atCell p side clause.id index expr,side.mode⟩
  have req : rq ∈ emissionRequests em := by
    apply List.mem_append_left
    apply List.mem_flatMap.mpr
    refine ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,?_⟩
    change rq ∈ inputRequests ⟨_,pat,GeneralDeclarationDemands.inputInterval (capture p.packet)
      ((allocation p clause).arguments i) pat⟩
    unfold inputRequests
    dsimp only
    rw [bounds,samePat]
    cases side
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  unfold schema
  exact generated_contains (List.mem_append_right _
    (List.mem_flatMap.mpr ⟨em,member,req⟩)) code

end Yulang.GeneralWhereOriginCompiler318
