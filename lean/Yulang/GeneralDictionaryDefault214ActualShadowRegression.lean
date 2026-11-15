import Yulang.GeneralDictionaryDefault214ActualBodyFrame

/-! A hidden record field is a real raw-expression read but not a semantic
body dependency. This is a support-helper regression, not an EvidenceNode
counterexample and not a change to the stored total expression. -/
namespace Yulang.GeneralDictionaryDefault214ActualShadowRegression
open GeneralDeclarations GeneralDeclarationPatterns GeneralNominalCenters
open GeneralNominalCenteredHeadMatExpressions
open GeneralNominalCenteredHeadMatEffects
open GeneralNominalCenteredHeadMatExtension (names)
open GeneralDictionaryDefault214ActualBodyFrame

 def pattern : Pattern := .record 5 (.app 2 []) (.record 5 (.var 77) (.app 2 []))
 def expression : Expr := .record 5 (.primitive (.scalar .int) [])
   (.record 5 (.variable 77) (.primitive (.scalar .int) []))
 def equation : GeneralDeclarations.Equation := ⟨99,0,pattern⟩
 def declaration : Declaration := ⟨37,0,[.app 2 []],[],[equation],[]⟩

 theorem declaration_scoped : declaration.Scoped := by
   simp [Declaration.Scoped,declaration,equation,pattern,normalize,hide,Pattern.variables,variablesArgs,normalizeArgs]

 theorem translation : translate GeneralDeclarationExamples.constructors GeneralNominalExamples.interpretation pattern =
     some expression := rfl

 theorem raw_dependency : 77 ∈ names expression := by decide +kernel
 theorem normalized_absent : 77 ∉ (normalize pattern).variables := by decide +kernel
 theorem not_raw_scope : ¬ (∀ name ∈ names expression, name ∈ declaration.inputNames ∨ name ∈ declaration.outputNames) := by
   intro scope
   have member := scope 77 raw_dependency
   simp [declaration,Declaration.inputNames,Declaration.outputNames,normalizeArgs,normalize,variablesArgs,Pattern.variables] at member

 theorem raw_support_reads (plan : Plan roles)
     (compiled : compileBody plan (.explicit equation) = some expression) : plan.binder 77 ∈
     GeneralDictionaryDefaultModeEffects213.bodySources plan target (.explicit equation) := by
   simp only [GeneralDictionaryDefaultModeEffects213.bodySources,
     GeneralDictionaryDefaultModeSupport213.schemaSources,bodySchema,compiled,List.flatMap_cons,List.flatMap_nil,List.append_nil]
   apply List.mem_cons_of_mem
   rw [GeneralDictionaryDefaultModeSupport213.actual_reads]
   apply List.mem_map.mpr
   refine ⟨77,raw_dependency,?_⟩
   simp [GeneralDictionaryDefaultTotalFrame212.bodyResolve,GeneralDictionaryDefaultTotalFrame212.resolve]

 theorem semantic_support (plan : Plan roles) : bodySources plan target (.explicit equation) = [target] := by
   simp [bodySources,equation,pattern,normalize,hide,Pattern.variables,variablesArgs,normalizeArgs]

 theorem body_invariant (plan : Plan roles) (first last : GeneralNominalCommonBridge.Assignment)
     (same : first target = last target) :
     BodyHolds plan target first (.explicit equation) ↔ BodyHolds plan target last (.explicit equation) := by
   apply body_iff
   rw [semantic_support]
   intro name member
   cases List.mem_singleton.mp member
   exact same

 theorem shadow_value (variables mode) :
     CommonNominalFullCarrier.Equivalent (value variables mode expression)
       (value variables mode (.record 5 (.primitive (.scalar .int) []) (.primitive (.scalar .int) []))) :=
   GeneralNominalCommonBridge.shadow _ _ _ _
end Yulang.GeneralDictionaryDefault214ActualShadowRegression
