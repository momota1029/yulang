import Yulang.GeneralDictionaryDefaultExpression209
import Yulang.GeneralDictionaryDefaultRecorded208

set_option backward.isDefEq.respectTransparency false

/-! Body transport is semantic, not a claim that cached reports are unchanged.
Only actual binder values and default input centers are compared. -/
namespace Yulang.GeneralDictionaryDefaultBodyTransport209
open GeneralDeclarations GeneralNominalCenters GeneralDictionaryAssociatedProvenance
open GeneralNominalCenteredHeadMatExpressions GeneralNominalCenteredHeadMatEffects
open GeneralDictionaryDefaultExpression209
open CommonNominalFullCarrier
variable {roles : Roles.RoleDecls} {first last : Plan roles}
variable {model : GeneralNominalCommonBridge.Assignment}
variable {environment : GeneralNominalMaterialization.Mode → Nat → Ty}

mutual
 theorem actual_only (expression : Expr) :
    value (fun _ name => environment .actual name) .actual expression = value environment .actual expression := by
  cases expression with
  | «variable» => rfl
  | primitive constructor arguments => exact congrArg (primitiveValue constructor) (actuals_only arguments)
  | nominal name arguments => exact congrArg (fun xs => nominal name (xs.map Sum.inl)) (actuals_only arguments)
  | record label payload tail => simp only [value,actual_only payload,actual_only tail]
  | variant tag payload => simp only [value,actual_only payload]
  | join a b => simp only [value,actual_only a,actual_only b]
 theorem actuals_only (expressions : List Expr) :
    values (fun _ name => environment .actual name) .actual expressions = values environment .actual expressions := by
  cases expressions with
  | nil => rfl
  | cons head tail => simp only [values,actual_only head,actuals_only tail]
end

 theorem actual_equivalent (expression : Expr)
    (same : ∀ name ∈ GeneralNominalCenteredHeadMatExtension.names expression,
      Equivalent (one .actual name) (two .actual name)) :
    Equivalent (value one .actual expression) (value two .actual expression) := by
  have eqv := value_equivalent (mode := GeneralNominalMaterialization.Mode.actual)
    (first := fun _ name => one .actual name) (last := fun _ name => two .actual name)
    expression (fun _ name member => same name member)
  simpa only [actual_only] using eqv

 theorem compile_equal
    (constructors : first.packet.registry.constructors = last.packet.registry.constructors)
    (interpretation : first.packet.context.interpretation = last.packet.context.interpretation)
    (body : Body) : compileBody first body = compileBody last body := by
  cases body <;> simp only [compileBody,constructors,interpretation]

 theorem body_holds_iff
    (translated : compileBody first body = some expression)
    (translated' : compileBody last body = some expression)
    (same : ∀ name ∈ GeneralNominalCenteredHeadMatExtension.names expression,
      Equivalent (bodyVariables first model body .actual name) (bodyVariables last model body .actual name)) :
    BodyHolds first target model body ↔ BodyHolds last target model body := by
  rw [body_equation translated,body_equation translated']
  have equal := actual_equivalent expression same
  exact ⟨fun valid => equivalent_trans valid equal,
    fun valid => equivalent_trans valid ⟨equal.2,equal.1⟩⟩

 theorem actual_variables (plan : Plan roles) (model) (name) :
    variables plan model .actual name = (model (plan.binder name)).1 := by
  simp only [variables,ite_self]

 theorem semantic_body_variables
    (binders : ∀ name, Equivalent (model (first.binder name)).1 (model (last.binder name)).1)
    (centers : ∀ index : Nat, Equivalent
      (model ((List.ofFn first.input.center)[index]?.getD 0)).1
      (model ((List.ofFn last.input.center)[index]?.getD 0)).1)
    (body : Body) (name : Nat) :
    Equivalent (bodyVariables first model body .actual name) (bodyVariables last model body .actual name) := by
  cases body with
  | explicit => simpa only [bodyVariables,actual_variables] using binders name
  | default => exact centers name

/-- Reinspection may change syntax. Equal compiled environments plus equivalent
actual binders/centers suffice for every total explicit or default equation. -/
 theorem body_transport
    (constructors : first.packet.registry.constructors = last.packet.registry.constructors)
    (interpretation : first.packet.context.interpretation = last.packet.context.interpretation)
    (binders : ∀ name, Equivalent (model (first.binder name)).1 (model (last.binder name)).1)
    (centers : ∀ index : Nat, Equivalent
      (model ((List.ofFn first.input.center)[index]?.getD 0)).1
      (model ((List.ofFn last.input.center)[index]?.getD 0)).1) :
    BodyHolds first target model body ↔ BodyHolds last target model body := by
  have compile := compile_equal constructors interpretation body
  cases compiled : compileBody first body with
  | none =>
      have compiled' : compileBody last body = none := compile.symm.trans compiled
      simp [BodyHolds,bodySchema,compiled,compiled',GeneralNominalCenteredHeadMatSchemas.Schema.Holds]
  | some expression =>
      exact body_holds_iff compiled (compile.symm.trans compiled)
        (fun name _ => semantic_body_variables binders centers body name)

end Yulang.GeneralDictionaryDefaultBodyTransport209
