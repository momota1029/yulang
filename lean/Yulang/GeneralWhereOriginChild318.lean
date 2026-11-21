import Yulang.GeneralWhereOriginAssemble318

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 26000
set_option maxHeartbeats 18000000
namespace Yulang.GeneralWhereOriginChild318
open GeneralDeclarations (Clause)
open GeneralNominalCenters (Plan)
open GeneralNominalVersionedFrame231 (capture binder)
open GeneralWhereVersionCompiler317 (schema emissions allocation emit child)
open GeneralNominalVersionedPlans231 (variables childSchema)
open GeneralNominalCenteredHeadMatExpressions (Expr translate value)
open GeneralNominalCenteredHeadMatSchemas (generated_equation emissionRequests)
open GeneralNominalMaterialization (Request rootRequests)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

theorem endpoint_requests (p : Plan rs) (c : Clause)
    (listed : c ∈ p.packet.declaration.requirements) (sig : c.Signature rs)
    (i : Fin (rs c.role).arity) :
    let pattern := c.arguments[i.val]'(by rw [sig.1]; exact i.isLt)
    let ports := (child p c sig).occurrence.demand.arguments i
    let reqs := rootRequests p.packet.declaration p.packet.site.occurrence ++ (emissions p).flatMap emissionRequests
    (⟨pattern,ports.1,.lower⟩ : Request) ∈ reqs ∧ (⟨pattern,ports.2,.upper⟩ : Request) ∈ reqs := by
  have emitted : emit p c sig ∈ emissions p := by
    apply (GeneralCanonicalChildOrder.canonicalEmit_perm p.packet.site.occurrence.identity
      p.packet.declaration p.packet.checked (capture p.packet) (allocation p)).mem_iff.mp
    exact List.mem_map.mpr ⟨⟨c,listed⟩,by simp,rfl⟩
  constructor
  all_goals
    apply List.mem_append_right
    apply List.mem_flatMap.mpr
    refine ⟨_,emitted,List.mem_append_left _ (List.mem_flatMap.mpr ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,?_⟩)⟩
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self

/-- The old center placement is retained, but the interval check uses
the real corrected emission on both sides. The needed endpoint-read
bounds are explicit; hidden unused reads cannot be silently assumed. -/
theorem argument_fits (p : Plan rs) (m : Assignment) (c : Clause)
    (listed : c ∈ p.packet.declaration.requirements) (sig : c.Signature rs)
    (i : Fin (rs c.role).arity) (expr : Expr)
    (compiled : translate p.packet.registry.constructors p.packet.context.interpretation
      (c.arguments[i.val]'(by rw [sig.1]; exact i.isLt)) = some expr)
    (bounds : ∀ n ∈ GeneralNominalExpressionIntervals237.reads expr,
      GeneralNominalCaptureMerges.Fits m ((capture p.packet).inputs n) (m (binder p n)).1)
    (rows : (schema p).Holds (variables p m) m)
    (actual : (childSchema p c sig).Holds (variables p m) m) :
    GeneralNominalCaptureMerges.Fits m ((child p c sig).occurrence.demand.arguments i)
      (m ((child p c sig).center i)).1 := by
  have reqs := endpoint_requests p c listed sig i
  have lower := generated_equation rows reqs.1 compiled
  have upper := generated_equation rows reqs.2 compiled
  have body := generated_equation actual (List.mem_ofFn.mpr ⟨i,rfl⟩) compiled
  have span := GeneralNominalExpressionIntervals237.interval (variables p m) expr
    (fun n appears => GeneralNominalVersionedChildIntervals237.variables_interval p m n (bounds n appears))
  rw [GeneralWhereVersionCompiler317.child_center p c sig i]
  exact ⟨subtype_trans lower.1 (subtype_trans span.1 body.2),
    subtype_trans body.1 (subtype_trans span.2 upper.2)⟩

end Yulang.GeneralWhereOriginChild318
