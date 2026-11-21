import Yulang.GeneralVersionedForeignCollision314
import Yulang.GeneralNominalCenteredHeadMatCompilerSemantics

set_option backward.isDefEq.respectTransparency false
/-! Actual-mode materialized values can reuse a genuine old write from the
same numeric invocation. The operand argument uses normalized scoped
source terms and actual observations, not equality of interval bounds. -/
namespace Yulang.GeneralVersionedRevisitActual314
open GeneralDeclarations GeneralSourceDictionaries GeneralDeclarationPatterns GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedTraceSupport237 (Reachable)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralNominalVersionedPlans231 (variables SchemaHolds)
open GeneralNominalVersionedFrame231 (binder binder_eq childSite emittedCenter)
open GeneralNominalCenteredHeadMatCompilerSemantics (compiled_normalized algebra)
open GeneralNominalCenteredHeadMatExpressions (translate value)
open GeneralNominalCenteredHeadMatPatternSemantics (eval)
open GeneralFiniteTypedWrites312 (reflexive symmetric transitive)
open CommonNominalFullCarrier (Equivalent)
open GeneralVersionedCompoundRows313 (address)
open GeneralVersionedComputedRows313 (OutputCell)
open GeneralNominalCommonBridge (Assignment)

theorem actual_agree {s : State roles} {p q : Plan roles}
    (checked : (boundary roles).Checked registry) (actual : Reachable registry root s)
    (frame : Frame (Compiled registry) s.core focus key p)
    (stored : q ∈ s.plans)
    (identity : q.packet.site.occurrence.identity = p.packet.site.occurrence.identity)
    (rule : q.packet.declaration = p.packet.declaration) (m : Assignment)
    (valid : Models s m) (schema : SchemaHolds p p.headSchema m)
    (name : Nat) (named : name ∈ p.packet.declaration.inputNames ∨ name ∈ p.packet.declaration.outputNames) :
    Equivalent (variables q m .actual name) (variables p m .actual name) := by
  obtain ⟨ctx,origins⟩ := GeneralVersionedSiteOrigins312.reached actual
  have configs := GeneralVersionedSiteOrigins312.stored_current_config actual stored
  have interpretation := configs.2.2.trans (congrArg GeneralNominalCandidates.Context.interpretation frame.context_eq).symm
  have seedEq := configs.1.trans (congrArg (fun c => c.state.seed) frame.context_eq).symm
  have centers := GeneralVersionedIdentityCenters312.same_identity checked actual valid q.input p.input
    (origins.input q stored) frame.center_recorded
    ((congrArg (fun o : Occurrence roles => o.identity) q.input_exact).trans
      (identity.trans (congrArg (fun o : Occurrence roles => o.identity) p.input_exact).symm))
  have currentHead := (GeneralVersionedIdentityCenters312.head_actual_iff p m).mp schema
  have oldHead := (GeneralVersionedIdentityCenters312.head_actual_iff q m).mp
    (GeneralNominalVersionedDiagnostic232.head_equations (valid.2.1 q stored)).2.2
  rcases named with input|output
  · have same := GeneralNominalHeadSchemaSemantic186.binder_same q p rule
      (configs.2.1.trans (congrArg (fun c => c.state.constructors) frame.context_eq).symm) interpretation centers oldHead currentHead
      (GeneralVersionedSiteOrigins312.stored_finished actual stored) name (rule.symm ▸ input)
    have value := same.2.2 _ _ (.source _) (.source _)
    simpa only [variables,ite_self,binder_eq] using value
  · have oldOutput : name ∈ q.packet.declaration.outputNames := rule.symm ▸ output
    have target : binder q name = binder p name := by
      simp only [binder,oldOutput,output,ite_true]
      change GeneralNominalIdentities.source q.packet.context.state.seed
        (GeneralNominalAllocation.origin q.packet.site.occurrence.identity q.packet.declaration.id 2 name 0) =
        GeneralNominalIdentities.source p.packet.context.state.seed
        (GeneralNominalAllocation.origin p.packet.site.occurrence.identity p.packet.declaration.id 2 name 0)
      rw [seedEq,identity,rule]
    simp only [variables,ite_self,target]
    exact reflexive _

theorem same_value {s : State roles} {p q : Plan roles}
    (checked : (boundary roles).Checked registry) (actual : Reachable registry root s)
    (frame : Frame (Compiled registry) s.core focus key p)
    (stored : q ∈ s.plans)
    (identity : q.packet.site.occurrence.identity = p.packet.site.occurrence.identity)
    (rule : q.packet.declaration = p.packet.declaration) (m : Assignment)
    (valid : Models s m) (schema : SchemaHolds p p.headSchema m)
    (pat : Pattern) {expr : GeneralNominalCenteredHeadMatExpressions.Expr}
    (translation : translate p.packet.registry.constructors p.packet.context.interpretation pat = some expr)
    (bound : ∀ name ∈ (normalize pat).variables,
      name ∈ p.packet.declaration.inputNames ∨ name ∈ p.packet.declaration.outputNames) :
    Equivalent (value (variables q m) .actual expr) (value (variables p m) .actual expr) := by
  have config := GeneralVersionedSiteOrigins312.stored_current_config actual stored
  have constructorEq : q.packet.registry.constructors = p.packet.registry.constructors :=
    congrArg Registry.constructors (((GeneralNominalVersionedMixedRegistry234.reachable actual).2.1 q stored).trans frame.registry_eq.symm)
  have interp := config.2.2.trans (congrArg GeneralNominalCandidates.Context.interpretation frame.context_eq).symm
  have previous : translate q.packet.registry.constructors q.packet.context.interpretation pat = some expr := by
    rwa [constructorEq,interp]
  have earlier := compiled_normalized (variables := variables q m) previous
  rw [constructorEq,interp] at earlier
  have current := compiled_normalized (variables := variables p m) translation
  have same := GeneralNominalCenteredHeadMatSemanticSubstitution.eval_congr (algebra := algebra p.packet.registry.constructors p.packet.context.interpretation) (normalize pat)
    (fun name present => actual_agree checked actual frame stored identity rule m valid schema name (bound name present))
  exact transitive earlier (transitive same (symmetric current))

theorem output {s : State roles} {p q : Plan roles}
    (checked : (boundary roles).Checked registry) (actual : Reachable registry root s)
    (frame : Frame (Compiled registry) s.core focus key p)
    (stored : q ∈ s.plans)
    (identity : q.packet.site.occurrence.identity = p.packet.site.occurrence.identity)
    (rule : q.packet.declaration = p.packet.declaration) (m : Assignment)
    (valid : Models s m) (schema : SchemaHolds p p.headSchema m)
    (row : GeneralNominalCenteredHeadMatSchemas.Equation) (cell : OutputCell p row) :
    row.Holds (variables p m) m := by
  obtain ⟨clause,inClause,eq,inside,computed,compiled,target,mode⟩ := cell
  have config := GeneralVersionedSiteOrigins312.stored_current_config actual stored
  have seedEq := config.1.trans (congrArg (fun c => c.state.seed) frame.context_eq).symm
  have constructorEq : q.packet.registry.constructors = p.packet.registry.constructors :=
    congrArg Registry.constructors (((GeneralNominalVersionedMixedRegistry234.reachable actual).2.1 q stored).trans frame.registry_eq.symm)
  have interp := config.2.2.trans (congrArg GeneralNominalCandidates.Context.interpretation frame.context_eq).symm
  have past : OutputCell q row := by
    refine ⟨clause,rule.symm ▸ inClause,eq,inside,?_,?_,?_,mode⟩
    · rwa [rule]
    · rwa [constructorEq,interp]
    · simp only [address,seedEq,identity,rule]
      exact target
  have held := (valid.2.1 q stored).2.2 row (GeneralVersionedComputedRows313.row_present past)
  have values := same_value checked actual frame stored identity rule m valid schema eq.rhs compiled
    (fun n seen => p.packet.checked.scope.2.2 clause inClause eq inside n
      (GeneralPatternVariableProvenance.normalize_variables eq.rhs seen))
  unfold GeneralNominalCenteredHeadMatSchemas.Equation.Holds at held ⊢
  rw [mode] at held ⊢
  exact transitive held values


theorem child {s : State roles} {p q : Plan roles}
    (checked : (boundary roles).Checked registry) (actual : Reachable registry root s)
    (frame : Frame (Compiled registry) s.core focus key p)
    (stored : q ∈ s.plans)
    (identity : q.packet.site.occurrence.identity = p.packet.site.occurrence.identity)
    (rule : q.packet.declaration = p.packet.declaration) (m : Assignment)
    (valid : Models s m) (schema : SchemaHolds p p.headSchema m)
    (clause : Clause) (inClause : clause ∈ p.packet.declaration.requirements) (sig : clause.Signature roles)
    (row : GeneralNominalCenteredHeadMatSchemas.Equation)
    (listed : row ∈ (GeneralNominalVersionedPlans231.childSchema p clause sig).equations) :
    row.Holds (variables p m) m := by
  obtain ⟨request,rqMember,materialized⟩ := GeneralVersionedRootWrites312.from_request listed
  obtain ⟨index,rfl⟩ := List.mem_ofFn.mp rqMember
  let pos : Fin clause.arguments.length := ⟨index.val,by rw [sig.1]; exact index.isLt⟩
  let pat := clause.arguments[pos.val]
  obtain ⟨compiled,target,mode⟩ := GeneralVersionedCompoundRows313.materializes materialized
  change translate p.packet.registry.constructors p.packet.context.interpretation pat = _ at compiled
  change row.target = emittedCenter p clause.id index.val pat at target
  change row.mode = .actual at mode
  by_cases simple : ∃ name, normalize pat = .var name
  · obtain ⟨name,atVar⟩ := simple
    have typed := compiled_normalized (variables := variables p m) compiled
    rw [atVar] at typed
    unfold emittedCenter at target
    rw [atVar] at target
    unfold GeneralNominalCenteredHeadMatSchemas.Equation.Holds
    rw [mode,target]
    have atActual : variables p m .actual name = (m (binder p name)).1 := by simp only [variables,ite_self]
    change Equivalent _ (variables p m .actual name) at typed
    rw [atActual] at typed
    exact symmetric typed
  · have settings := GeneralVersionedSiteOrigins312.stored_current_config actual stored
    have sameSeed := settings.1.trans (congrArg (fun c => c.state.seed) frame.context_eq).symm
    have constructorEq : q.packet.registry.constructors = p.packet.registry.constructors :=
      congrArg Registry.constructors (((GeneralNominalVersionedMixedRegistry234.reachable actual).2.1 q stored).trans frame.registry_eq.symm)
    have interp := settings.2.2.trans (congrArg GeneralNominalCandidates.Context.interpretation frame.context_eq).symm
    have oldTranslation : translate q.packet.registry.constructors q.packet.context.interpretation pat = some row.expression := by
      rwa [constructorEq,interp]
    let oldTarget := (childSite q clause sig).center index
    have sameTarget : oldTarget = row.target := by
      change emittedCenter q clause.id index.val pat = _
      rw [target]
      cases normalized : normalize pat with
      | var n => exact False.elim (simple ⟨n,normalized⟩)
      | app | record | variant | join =>
        all_goals
          unfold emittedCenter
          rw [normalized,sameSeed,identity,rule]
    let oldRequest : GeneralNominalMaterialization.Request := ⟨pat,oldTarget,.actual⟩
    have oldMember : oldRequest ∈ GeneralNominalVersionedPlans231.childRequests q clause sig :=
      List.mem_ofFn.mpr ⟨index,rfl⟩
    have earlier := (valid.2.1 q stored).2.1.2.2.2.2.2.2 clause (rule.symm ▸ inClause) sig
    have wrote := GeneralNominalCenteredHeadMatSchemas.generated_equation earlier.2 oldMember oldTranslation
    have normalized : normalize pat ∈ normalizeArgs clause.arguments := by
      rw [GeneralNominalChildAssembly.normalize_map]
      exact List.mem_map.mpr ⟨pat,List.getElem_mem ..,rfl⟩
    have same := same_value checked actual frame stored identity rule m valid schema pat compiled
      (fun name use => .inl (p.packet.checked.scope.1 clause inClause name
        (GeneralDictionaryActualSchemaScope.variables_args_member _ _ normalized name use)))
    unfold GeneralNominalCenteredHeadMatSchemas.Equation.Holds
    change Equivalent (m oldTarget).1 (value (variables q m) .actual row.expression) at wrote
    rw [sameTarget] at wrote
    rw [mode]
    exact transitive wrote same

end Yulang.GeneralVersionedRevisitActual314
