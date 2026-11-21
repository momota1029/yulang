import Yulang.GeneralWhereOriginChild318
import Yulang.GeneralDictionaryDefault214ActualShadowRegression

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
set_option maxHeartbeats 6500000
namespace Yulang.GeneralWhereOriginShadow318
open GeneralDeclarations (Clause)
open GeneralNominalCenters (Plan)
open GeneralWhereVersionCompiler317 (schema child)
open GeneralNominalVersionedPlans231 (variables childSchema)
open GeneralNominalCenteredHeadMatExpressions (Expr translate value)
open GeneralNominalCenteredHeadMatSchemas (generated_equation)
open GeneralNominalExpressionIntervals237 (reads interval)
open GeneralNominalMaterialization (Mode)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

def Span (vars : Mode → Nat → Ty) (expr : Expr) : Prop :=
  Subtype (value vars .lower expr) (value vars .actual expr) ∧
    Subtype (value vars .actual expr) (value vars .upper expr)

theorem argument_fits_of_span (p : Plan rs) (m : Assignment) (c : Clause)
    (listed : c ∈ p.packet.declaration.requirements) (sig : c.Signature rs)
    (i : Fin (rs c.role).arity) (expr : Expr)
    (compiled : translate p.packet.registry.constructors p.packet.context.interpretation
      (c.arguments[i.val]'(by rw [sig.1]; exact i.isLt)) = some expr)
    (span : Span (variables p m) expr)
    (rows : (schema p).Holds (variables p m) m)
    (actual : (childSchema p c sig).Holds (variables p m) m) :
    GeneralNominalCaptureMerges.Fits m ((child p c sig).occurrence.demand.arguments i)
      (m ((child p c sig).center i)).1 := by
  have reqs := GeneralWhereOriginChild318.endpoint_requests p c listed sig i
  have lo := generated_equation rows reqs.1 compiled
  have hi := generated_equation rows reqs.2 compiled
  have center := generated_equation actual (List.mem_ofFn.mpr ⟨i,rfl⟩) compiled
  rw [GeneralWhereVersionCompiler317.child_center p c sig i]
  exact ⟨subtype_trans lo.1 (subtype_trans span.1 center.2),
    subtype_trans center.1 (subtype_trans span.2 hi.2)⟩

theorem equivalent_span {vars : Mode → Nat → Ty} {one two : Expr}
    (equiv : ∀ mode, Equivalent (value vars mode one) (value vars mode two))
    (held : Span vars two) : Span vars one :=
  ⟨subtype_trans (equiv .lower).1 (subtype_trans held.1 (equiv .actual).2),
    subtype_trans (equiv .actual).1 (subtype_trans held.2 (equiv .upper).2)⟩

/-- A shadowed field is a real compiler read but not an interval dependency.
Only the visible payload and tail need a span. The ignored value may be
unconstrained or even vary nonmonotonically with mode. -/
theorem shadow_span (vars : Mode → Nat → Ty) (label : Nat) (live hidden tail : Expr)
    (bounded : ∀ n ∈ reads (.record label live tail),
      Subtype (vars .lower n) (vars .actual n) ∧ Subtype (vars .actual n) (vars .upper n)) :
    Span vars (.record label live (.record label hidden tail)) := by
  apply equivalent_span (two := .record label live tail)
  · intro mode
    exact GeneralNominalCommonBridge.shadow _ _ _ _
  · exact interval vars _ bounded

theorem checked_shadow_example (vars : Mode → Nat → Ty) :
    Span vars GeneralDictionaryDefault214ActualShadowRegression.expression := by
  apply shadow_span
  intro n found
  change n ∈ ([] : List Nat) at found
  cases found

theorem raw_read_not_needed :
    77 ∈ reads GeneralDictionaryDefault214ActualShadowRegression.expression ∧
      77 ∉ (GeneralDeclarationPatterns.normalize
        GeneralDictionaryDefault214ActualShadowRegression.pattern).variables := by
  exact ⟨by decide +kernel,GeneralDictionaryDefault214ActualShadowRegression.normalized_absent⟩

end Yulang.GeneralWhereOriginShadow318
