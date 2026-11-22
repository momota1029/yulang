import Yulang.GeneralDeclarativeCommitSuffix344
import Yulang.GeneralWhereOriginSchema318

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeCommitModes344
open GeneralNominalCenters (Plan Site)
open GeneralDeclarations (Clause)
open GeneralNominalCommonBridge (Assignment)
open GeneralWhereVersionCompiler317 (emit emissions allocation args child schema)
open GeneralWhereVersionSemantics317 (Holds)
open GeneralNominalVersionedFrame231 (capture)
open GeneralNominalVersionedPlans231 (variables childRequests childSchema)
open GeneralNominalMaterialization (Mode Request rootRequests)
open GeneralNominalCenteredHeadMatSchemas (emissionRequests inputRequests generated_equation)
open GeneralWhereOriginSchema318 (pick input)
open GeneralVersionedEndpointAddress315 (Side atCell)
open GeneralNominalCenteredHeadMatExpressions (Expr translate value)
open CommonNominalFullCarrier (Equivalent)

theorem emitted_mem (p : Plan rs) (c : Clause) (inside : c ∈ p.packet.declaration.requirements)
    (sig : c.Signature rs) : emit p c sig ∈ emissions p := by
  apply (GeneralCanonicalChildOrder.canonicalEmit_perm p.packet.site.occurrence.identity
    p.packet.declaration p.packet.checked (capture p.packet) (allocation p)).mem_iff.mp
  unfold GeneralDeclarationDemands.emitAll
  exact List.mem_map.mpr ⟨⟨c,inside⟩,by simp,rfl⟩

theorem endpoint_request (p : Plan rs) (c : Clause) (sig : c.Signature rs)
    (i : Fin (rs c.role).arity) (side : Side) :
    input p c sig i side ∈ emissionRequests (emit p c sig) := by
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  refine ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,?_⟩
  cases side with
  | lower => exact List.mem_cons_self
  | upper => exact List.mem_cons_of_mem _ List.mem_cons_self

theorem endpoint (p : Plan rs) (c : Clause) (inside : c ∈ p.packet.declaration.requirements)
    (sig : c.Signature rs) (i : Fin (rs c.role).arity) (side : Side) (m : Assignment)
    (valid : Holds p m) (code : Expr)
    (print : translate p.packet.registry.constructors p.packet.context.interpretation (input p c sig i side).pattern =
      some code) :
    Equivalent (m (pick side ((child p c sig).occurrence.demand.arguments i))).1
      (value (variables p m) side.mode code) := by
  apply generated_equation valid.rows ?_ print
  apply List.mem_append_right
  exact List.mem_flatMap.mpr ⟨emit p c sig,emitted_mem p c inside sig,endpoint_request p c sig i side⟩

theorem center (p : Plan rs) (c : Clause) (inside : c ∈ p.packet.declaration.requirements)
    (sig : c.Signature rs) (i : Fin (rs c.role).arity) (m : Assignment)
    (valid : Holds p m) (code : Expr)
    (printed : translate p.packet.registry.constructors p.packet.context.interpretation
      (c.arguments[i.val]'(by rw [sig.1]; exact i.isLt)) = some code) :
    Equivalent (m ((child p c sig).center i)).1 (value (variables p m) .actual code) := by
  let req : Request := ⟨c.arguments[i.val]'(by rw [sig.1]; exact i.isLt),
    (GeneralNominalVersionedFrame231.childSite p c sig).center i,.actual⟩
  have listed : req ∈ childRequests p c sig := List.mem_ofFn.mpr ⟨i,rfl⟩
  exact generated_equation (valid.childSemantics c inside sig).2 listed printed

/-- Three separately derived values, indexed by the raw source argument
position. The endpoints may be nonpoint and need not denote the center. -/
theorem all_modes (p : Plan rs) (c : Clause) (inside : c ∈ p.packet.declaration.requirements)
    (sig : c.Signature rs) (i : Fin (rs c.role).arity) (m : Assignment)
    (valid : Holds p m) (code : Expr)
    (printed : translate p.packet.registry.constructors p.packet.context.interpretation
      (c.arguments[i.val]'(by rw [sig.1]; exact i.isLt)) = some code) :
    let s := child p c sig
    Equivalent (m (s.occurrence.demand.arguments i).1).1 (value (variables p m) .lower code) ∧
    Equivalent (m (s.center i)).1 (value (variables p m) .actual code) ∧
    Equivalent (m (s.occurrence.demand.arguments i).2).1 (value (variables p m) .upper code) :=
  ⟨endpoint p c inside sig i .lower m valid code printed,
   center p c inside sig i m valid code printed,
   endpoint p c inside sig i .upper m valid code printed⟩

end Yulang.GeneralDeclarativeCommitModes344
