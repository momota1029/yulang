import Yulang.GeneralWhereOriginCompiler318

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 2500000
namespace Yulang.GeneralWhereOriginDescriptor318
open GeneralNominalCenters (Plan)
open GeneralDeclarations (Clause)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralVersionedEndpointAddress315 (atCell)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralWhereVersionCompiler317 (child allocation args)
open GeneralNominalVersionedFrame231 (capture)
open GeneralDeclarationDemands (inputInterval)

theorem argument {p : Plan rs} {clause : Clause} (sig : clause.Signature rs)
    (i : Fin (rs clause.role).arity) {pat : Pattern}
    (entry : clause.arguments[i.val]? = some pat)
    (nonVar : ∀ n, normalize pat ≠ .var n)
    {expr : Expr} (translated : translate p.packet.registry.constructors p.packet.context.interpretation pat = some expr) :
    (child p clause sig).occurrence.demand.arguments i =
      (atCell p .lower clause.id i.val expr,atCell p .upper clause.id i.val expr) := by
  have pattern : clause.arguments[i.val]'(by rw [sig.1]; exact i.isLt) = pat :=
    (List.getElem?_eq_some_iff.mp entry).2
  change inputInterval (capture p.packet) (args p clause i)
    (clause.arguments[i.val]'(by rw [sig.1]; exact i.isLt)) = _
  rw [pattern]
  unfold inputInterval
  split
  · rename_i n eq
    exact False.elim (nonVar n eq)
  · unfold args
    simp only [entry,translated]

end Yulang.GeneralWhereOriginDescriptor318
