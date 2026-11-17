import Yulang.GeneralDictionaryReachableRest227
import Yulang.GeneralDictionaryDefault214ActualBodyFrame
import Yulang.GeneralNominalCenteredHeadMatSemanticSubstitution

/-! Historical input binders need not be kept bit-for-bit: the retained head
schema reads them back from their observed origins. Explicit bodies therefore
protect roots and output binders, not repeated-capture p0/p1 names. -/
namespace Yulang.GeneralDictionaryHistoricalBody227
open GeneralDeclarations GeneralDeclarationPatterns GeneralNominalCenters
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRecursiveInspection
open GeneralNominalCenteredHeadMatEffects
open GeneralNominalCenteredModelExtension (originSource)
open GeneralNominalCenteredFrame179 (Agree observes_iff)
open GeneralDictionaryAssociatedProvenance (Body Supplies)
open CommonNominalFullCarrier
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl eqv_symm eqv_trans)
variable {roles : Roles.RoleDecls} {plan : Plan roles} {first last : Assignment}

def headRoots (plan : Plan roles) : List Nat :=
  plan.headSchema.variables.map fun entry => originSource entry.origin

/-- Uniform semantic readback for an input binder; its own assignment entry is
not required to be equal across models. No trace or groundness premise. -/
theorem input_equivalent (plan : Plan roles)
    (finished : Finished (GeneralNominalQueryProvenance183.headInspection plan))
    (one : plan.SchemaHolds plan.headSchema first)
    (two : plan.SchemaHolds plan.headSchema last)
    (same : Agree (headRoots plan) first last)
    (name : Nat) (declared : name ∈ plan.packet.declaration.inputNames) :
    Equivalent (first (plan.binder name)).1 (last (plan.binder name)).1 := by
  obtain ⟨captured,present,equal⟩ := GeneralNominalCompleteNames183.declaration_input_capture
    plan.packet.context.state plan.packet.context.interpretation plan.packet.declaration
    plan.packet.bounds _ 0 finished name declared
  obtain ⟨origin,_,used⟩ := GeneralNominalCenteredCaptureSchema.many_capture
    plan.packet.context.state _ plan.packet.bounds _ 0 captured present
  have a : GeneralNominalOriginTerms.Same first origin (.source (plan.binder captured.name)) :=
    one.2 ⟨captured.name,origin,.actual⟩ used
  have b : GeneralNominalOriginTerms.Same last origin (.source (plan.binder captured.name)) :=
    two.2 ⟨captured.name,origin,.actual⟩ used
  have root := same (originSource origin)
    (List.mem_map.mpr ⟨⟨captured.name,origin,.actual⟩,used,rfl⟩)
  obtain ⟨value,seen⟩ := a.1
  have seen' := (observes_iff origin root value).mp seen
  have aa := a.2.2 value (first (plan.binder captured.name)).1 seen (.source _)
  have bb := b.2.2 value (last (plan.binder captured.name)).1 seen' (.source _)
  simpa only [equal] using eqv_trans (eqv_symm aa) bb

def explicitSources (plan : Plan roles) (target : Nat) : List Nat :=
  target :: (headRoots plan ++ plan.packet.declaration.outputNames.map plan.binder)

def bodySources (plan : Plan roles) (target : Nat) : Body → List Nat
  | .explicit _ => explicitSources plan target
  | body@(.default _ _ _) => GeneralDictionaryDefault214ActualBodyFrame.bodySources plan target body

/-- Normalization removes syntactically shadowed reads before scope is used.
The compiled total expression itself is not replaced or weakened. -/
theorem explicit_value_equivalent (plan : Plan roles) (equation : GeneralDeclarations.Equation)
    (present : equation ∈ plan.packet.declaration.associated)
    (finished : Finished (GeneralNominalQueryProvenance183.headInspection plan))
    (one : plan.SchemaHolds plan.headSchema first)
    (two : plan.SchemaHolds plan.headSchema last)
    (same : Agree (headRoots plan ++ plan.packet.declaration.outputNames.map plan.binder) first last)
    (compiled : compileBody plan (.explicit equation) = some expression) :
    Equivalent (GeneralNominalCenteredHeadMatExpressions.value (variables plan first) .actual expression)
      (GeneralNominalCenteredHeadMatExpressions.value (variables plan last) .actual expression) := by
  have a := GeneralNominalCenteredHeadMatCompilerSemantics.compiled_normalized
    (variables := variables plan first) compiled
  have b := GeneralNominalCenteredHeadMatCompilerSemantics.compiled_normalized
    (variables := variables plan last) compiled
  have middle : Equivalent
      (GeneralNominalCenteredHeadMatPatternSemantics.eval
        (GeneralNominalCenteredHeadMatCompilerSemantics.algebra plan.packet.registry.constructors
          plan.packet.context.interpretation) (variables plan first .actual) (normalize equation.rhs))
      (GeneralNominalCenteredHeadMatPatternSemantics.eval
        (GeneralNominalCenteredHeadMatCompilerSemantics.algebra plan.packet.registry.constructors
          plan.packet.context.interpretation) (variables plan last .actual) (normalize equation.rhs)) := by
    apply GeneralNominalCenteredHeadMatSemanticSubstitution.eval_congr
    intro name member
    rw [actual_variable,actual_variable]
    rcases plan.packet.checked.scope.2.1 equation present name member with input | output
    · exact input_equivalent plan finished one two
        (fun n h => same n (List.mem_append_left _ h)) name input
    · rw [same (plan.binder name) (List.mem_append_right _ (List.mem_map.mpr ⟨name,output,rfl⟩))]
      exact eqv_refl _
  exact eqv_trans a (eqv_trans middle (eqv_symm b))

theorem body_iff (plan : Plan roles) (target : Nat) (body : Body)
    (supplied : Supplies roles plan.packet.declaration outputName body)
    (finished : Finished (GeneralNominalQueryProvenance183.headInspection plan))
    (one : plan.SchemaHolds plan.headSchema first)
    (two : plan.SchemaHolds plan.headSchema last)
    (same : Agree (bodySources plan target body) first last) :
    BodyHolds plan target first body ↔ BodyHolds plan target last body := by
  cases supplied with
  | explicit equation present named =>
    cases compiled : compileBody plan (.explicit equation) with
    | none => simp [BodyHolds,bodySchema,compiled,GeneralNominalCenteredHeadMatSchemas.Schema.Holds]
    | some expression =>
      rw [body_equation compiled,body_equation compiled]
      have targetEq := congrArg Prod.fst (same target (List.mem_cons_self ..))
      have rhs := explicit_value_equivalent plan equation present finished one two
        (fun n h => same n (List.mem_cons_of_mem _ h)) compiled
      change Equivalent (first target).1 _ ↔ Equivalent (last target).1 _
      rw [targetEq]
      exact ⟨fun valid => eqv_trans valid rhs,fun valid => eqv_trans valid (eqv_symm rhs)⟩
  | default term absent declared =>
    exact GeneralDictionaryDefault214ActualBodyFrame.body_iff plan target _ same

open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208

/-- Actual registrations discharge Finished and both schema premises. -/
theorem registered_body_iff
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (plan : Plan roles) (registered : plan ∈ state.core.plans)
    (target : Nat) (body : Body)
    (supplied : Supplies roles plan.packet.declaration outputName body)
    (one : Models state first) (two : Models state last)
    (same : Agree (bodySources plan target body) first last) :
    BodyHolds plan target first body ↔ BodyHolds plan target last body := by
  apply body_iff plan target body supplied
    (GeneralDictionaryDefault214ActualReadback.registered_finished path plan registered)
  · exact (GeneralNominalCenteredHeadMatStepPackets.head_equations
      (one.2.2.2.2.1 plan registered)).2.2
  · exact (GeneralNominalCenteredHeadMatStepPackets.head_equations
      (two.2.2.2.2.1 plan registered)).2.2
  · exact same

end Yulang.GeneralDictionaryHistoricalBody227
