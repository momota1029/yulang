import Yulang.GeneralDeclarativeReadScope320
import Yulang.GeneralDeclarativeSubstitution320

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 13500
set_option maxHeartbeats 3500000
namespace Yulang.GeneralDeclarativeNormalized320
open CommonNominalFullCarrier (Equivalent subtype_trans)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeDemand320 (Bounds bounds_sound HeadMeaning WhereMeaning sourceValue)
open GeneralDeclarativeWhere319 (Capture variables)
open GeneralDeclarativeBounds319 (bound_sound)
open GeneralDeclarativePoint320 (FrozenReads semantic_point)
open GeneralDeclarativeSubstitution320 (EquationRead equation_read)
open GeneralDeclarativeReadScope320 (tracked_from_declared_inputs)
open GeneralNominalCenteredHeadMatExpressions (Expr translate value)
open GeneralNominalCenteredHeadMatCompilerSemantics (translate_value)
open GeneralNominalExpressionIntervals237 (interval)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans)
open GeneralDeclarationPatterns (Constructors Pattern normalize)
open GeneralNominalInspection (Interpretation)
open GeneralDeclarations (Declaration Clause DeclarationChecked)
open CommonRoleOutermostResolver (All₂)

/-- Two independently checkable routes to the actual center. The
endpoint route does not require an actual constructor equation at the center. -/
inductive Center (s : State) (capture : Nat → Capture)
    (arg : Capture) (code : Expr) : Prop where
  | direct : EquationRead s capture .actual arg.center code → Center s capture arg code
  | endpoints : Bounds s arg → FrozenReads s capture code →
      EquationRead s capture .lower arg.lower code →
      EquationRead s capture .upper arg.upper code → Center s capture arg code

theorem center_sound {s capture arg code} (center : Center s capture arg code)
    (m : Assignment) (valid : Models s m) :
    Equivalent (m arg.center).1 (value (variables capture m) .actual code) := by
  cases center with
  | direct fact => exact equation_read fact m valid
  | endpoints bounds freeze lower upper =>
    have bounded := bounds_sound bounds m valid
    have exacts := semantic_point freeze m valid
    have lo := eqv_trans (equation_read lower m valid) exacts.1
    have hi := eqv_trans (equation_read upper m valid) exacts.2
    exact ⟨subtype_trans bounded.2 hi.1,subtype_trans lo.2 bounded.1⟩

def NormalArg (s : State) (c : Constructors) (interp : Interpretation) (capture : Nat → Capture)
    (arg : Capture) (pattern : Pattern) : Prop :=
  ∃ exp, translate c interp (normalize pattern) = some exp ∧
    EquationRead s capture .lower arg.lower exp ∧ EquationRead s capture .upper arg.upper exp ∧
    Center s capture arg exp

/-- The compilation here is on the normalized source. Scope therefore
supplies the bounds for every actual polarity-sensitive read, even for
heads with eliminated shadow fields. -/
def NormalMeaning (c : Constructors) (interp : Interpretation) (capture : Nat → Capture)
    (model : Assignment) (arg : Capture) (pattern : Pattern) : Prop :=
  ∃ exp, translate c interp (normalize pattern) = some exp ∧
    Equivalent (model arg.lower).1 (value (variables capture model) .lower exp) ∧
    Equivalent (model arg.upper).1 (value (variables capture model) .upper exp) ∧
    HeadMeaning c interp capture model arg pattern

theorem normalized_where {s c interp capture decl clause arg pattern}
    (check : DeclarationChecked c roles decl)
    (belongs : clause ∈ decl.requirements) (appears : pattern ∈ clause.arguments)
    (bound : ∀ name ∈ decl.inputNames, Bounds s (capture name))
    (proof : NormalArg s c interp capture arg pattern) (m : Assignment) (valid : Models s m) :
    NormalMeaning c interp capture m arg pattern := by
  obtain ⟨exp,compiled,one,two,center⟩ := proof
  have tracked := tracked_from_declared_inputs check belongs appears compiled bound
  have ranges := interval (variables capture m) exp (fun name h =>
    ⟨bound_sound m valid.1 (tracked name h).1,bound_sound m valid.1 (tracked name h).2⟩)
  have lo := equation_read one m valid
  have hi := equation_read two m valid
  have actual := center_sound center m valid
  refine ⟨exp,compiled,lo,hi,?_,subtype_trans lo.1 (subtype_trans ranges.1 actual.2),
    subtype_trans actual.1 (subtype_trans ranges.2 hi.2)⟩
  unfold sourceValue
  rwa [← translate_value (normalize pattern) compiled]

theorem ordered_map {p q : α → β → Prop} {xs : List α} {ys : List β}
    (related : All₂ p xs ys)
    (transport : ∀ a ∈ xs, ∀ b ∈ ys, p a b → q a b) : All₂ q xs ys := by
  induction related with
  | nil => exact .nil
  | cons first rest ih =>
    exact .cons (transport _ List.mem_cons_self _ List.mem_cons_self first)
      (ih (fun a ha b hb => transport a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)))

theorem normalized_where_clause {s c interp capture decl clause args}
    (check : DeclarationChecked c roles decl)
    (belongs : clause ∈ decl.requirements) (bound : ∀ name ∈ decl.inputNames, Bounds s (capture name))
    (proof : All₂ (NormalArg s c interp capture) args clause.arguments)
    (m : Assignment) (valid : Models s m) :
    All₂ (NormalMeaning c interp capture m) args clause.arguments :=
  ordered_map proof (fun _ _ _ appears h => normalized_where check belongs appears bound h m valid)

end Yulang.GeneralDeclarativeNormalized320
