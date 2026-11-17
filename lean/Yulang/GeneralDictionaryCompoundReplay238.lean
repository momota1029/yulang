import Yulang.GeneralDictionaryCompoundObstruction238
import Yulang.GeneralNominalVersionedHeadReplay237
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryCompoundReplay238
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryCompoundSource238
open GeneralDictionaryCompoundPoint238
open GeneralDictionaryCompoundObstruction238
open GeneralNominalVersionedPlans231 GeneralNominalCenters
open GeneralNominalCommonBridge (Assignment)

 theorem head_schema : currentPlan.headSchema = oldPlan.headSchema :=
  GeneralNominalVersionedHeadReplay237.schema_eq _ _ rfl rfl rfl rfl

 theorem binder_exact : GeneralNominalVersionedFrame231.binder currentPlan 0 = GeneralDictionaryCompoundPacket238.actual := by
  rw [GeneralNominalVersionedFrame231.binder_eq]
  unfold Plan.binder
  change (if 0 ∈ declaration.outputNames then _ else if _ then _ else _) = _
  simp only [show ¬ 0 ∈ declaration.outputNames by decide, ite_false]
  have oldCapture : (GeneralNominalPacketSupport.capture currentPlan.packet).inputs 0 =
      (GeneralDictionaryCompoundPacket238.lo,GeneralDictionaryCompoundPacket238.hi) := by
    unfold GeneralNominalPacketSupport.capture
    rw [GeneralDictionaryCompoundCurrent238.bindings_exact]
    rfl
  rw [oldCapture]
  have distinct : GeneralDictionaryCompoundPacket238.lo ≠ GeneralDictionaryCompoundPacket238.hi :=
    Ne.symm (GeneralNominalCenteredAllocation.fresh_namespaces (by decide : (1:Nat) ≠ 0))
  simp only [distinct,ite_false]
  rfl

 theorem actual_head (model : Assignment) (valid : GeneralNominalVersionedJournal232.Models point model) :
    SchemaHolds currentPlan currentPlan.headSchema model := by
  have old := (valid.2.1 oldPlan original_plan_retained).2.1.2.2.2.2.1
  rw [head_schema]
  refine ⟨old.1,?_⟩
  intro entry member
  have named := GeneralNominalHeadSchemaNames186.head_input oldPlan entry member
  have zero : entry.name = 0 := by
    simpa [GeneralDeclarations.Declaration.inputNames,GeneralDeclarationPatterns.variablesArgs,
      GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
      GeneralDeclarationPatterns.Pattern.variables] using named
  have mode := GeneralNominalHeadSchemaNames186.head_actual oldPlan entry member
  have prior := old.2 entry member
  simp only [mode,ite_true,zero,binder_exact]
  simpa only [mode,ite_true,zero,GeneralNominalVersionedFrame231.binder_eq,
    GeneralDictionaryCompoundPacket238.binder_exact] using prior

 theorem child_schema (signature : child.Signature roles) :
    childSchema currentPlan child signature = childSchema oldPlan child signature := by
  rw [childSchema_eq,childSchema_eq]
  rfl

 theorem actual_variables (model : Assignment) : variables currentPlan model .actual 0 = variables oldPlan model .actual 0 := by
  unfold variables
  simp only [show ¬ 0 ∈ declaration.outputNames by decide, ite_false]
  rw [binder_exact,GeneralNominalVersionedFrame231.binder_eq,GeneralDictionaryCompoundPacket238.binder_exact]

 theorem child_actual (model : Assignment) (valid : GeneralNominalVersionedJournal232.Models point model)
    (signature : child.Signature roles) :
    (childSchema currentPlan child signature).Holds (variables currentPlan model) model := by
  have old := (valid.2.1 oldPlan original_plan_retained).2.1.2.2.2.2.2.2 child (List.mem_singleton_self _) signature |>.2
  rw [child_schema,childSchema_eq,GeneralDictionaryCompoundTotal238.child_schema] at *
  intro equation member
  have previous := old equation member
  cases List.mem_singleton.mp member
  simpa only [GeneralNominalCenteredHeadMatSchemas.Equation.Holds,GeneralNominalCenteredHeadMatExpressions.value,actual_variables] using previous

 theorem child_site (signature : child.Signature roles) :
    GeneralNominalVersionedFrame231.childSite currentPlan child signature =
      GeneralNominalVersionedFrame231.childSite oldPlan child signature := by
  unfold GeneralNominalVersionedFrame231.childSite GeneralNominalVersionedFrame231.clauseChild
    GeneralDictionaryEmissionPlans.occurrence GeneralDeclarationDemands.emit
    GeneralDeclarationDemands.childDemand GeneralNominalVersionedFrame231.frame
    GeneralNominalVersionedFrame231.emittedCenter
  dsimp only
  congr 1
  congr 1
  congr 1
  all_goals
    funext index
    have same : index = 0 := Fin.ext (by have h := index.isLt; change index.val < 1 at h; exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ h))
    subst index
    rfl

 theorem child_interval (model : Assignment) (valid : GeneralNominalVersionedJournal232.Models point model)
    (signature : child.Signature roles) :
    (GeneralNominalVersionedFrame231.childSite currentPlan child signature).Holds model := by
  rw [child_site]
  exact (valid.2.1 oldPlan original_plan_retained).2.1.2.2.2.2.2.2 child (List.mem_singleton_self _) signature |>.1

end Yulang.GeneralDictionaryCompoundReplay238
