import Yulang.GeneralVersionedNormalizedVariable313
import Yulang.GeneralVersionedFirstFootprint313
import Yulang.GeneralVersionedForwardedWrites312

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000
/-! Rows for compound where inputs retain their actual clause and position.
Each endpoint or center of such a clause gets a distinct allocation.
No equation is approximated by its endpoint or actual sibling. -/
namespace Yulang.GeneralVersionedCompoundRows313
open GeneralDeclarations GeneralDeclarationPatterns GeneralNominalCenters
open GeneralNominalVersionedFrame231 (capture frame childSite binder)
open GeneralNominalVersionedPlans231 (variables childSchema)
open GeneralNominalMaterialization (Mode Request)
open GeneralNominalCenteredHeadMatSchemas (Equation generated materialize)
open GeneralNominalCenteredHeadMatExpressions (translate)
open GeneralNominalCommonBridge (Assignment)
open GeneralVersionedRootWrites312 (inner whereRequests from_request)
open GeneralVersionedForwardedWrites312 (variable_request)

def address (p : Plan roles) (kind clause pos : Nat) : Nat :=
  fresh p.packet.context.state.seed p.packet.site.occurrence.identity p.packet.declaration.id kind clause pos

def mode (kind : Nat) : Mode :=
  if kind = 3 then .lower else if kind = 4 then .upper else .actual

def Taut (p : Plan roles) (eq : GeneralNominalCenteredHeadMatSchemas.Equation) : Prop :=
  ∀ m : Assignment, eq.Holds (variables p m) m

def Cell (p : Plan roles) (eq : GeneralNominalCenteredHeadMatSchemas.Equation) : Prop :=
  ∃ clause ∈ p.packet.declaration.requirements, ∃ pos kind pat,
    (kind = 3 ∨ kind = 4 ∨ kind = 9) ∧ clause.arguments[pos]? = some pat ∧
    translate p.packet.registry.constructors p.packet.context.interpretation pat = some eq.expression ∧
    eq.target = address p kind clause.id pos ∧ eq.mode = mode kind

def ForwardedResult (d : Declaration) : Prop :=
  ∀ clause ∈ d.requirements, ∀ eq ∈ clause.outputs,
    ∃ n, eq.rhs = .var n ∧ n ∈ d.outputNames

theorem materializes {catalogue interp rq eq} (h : eq ∈ (materialize catalogue interp rq).equations) :
    translate catalogue interp rq.pattern = some eq.expression ∧ eq.target = rq.target ∧ eq.mode = rq.mode := by
  unfold materialize at h
  split at h
  · cases List.mem_singleton.mp h
    exact ⟨by assumption,rfl,rfl⟩
  · cases h

theorem key_unique (f : α → Nat) (xs : List α)
    (unique : (xs.map f).Nodup) (a b : α) (one : a ∈ xs) (two : b ∈ xs) (same : f a = f b) : a = b := by
  induction xs with
  | nil => cases one
  | cons top rest ih =>
    have unique := List.nodup_cons.mp unique
    rcases List.mem_cons.mp one with ea|ha
    · subst top
      rcases List.mem_cons.mp two with eb|hb
      · exact eb.symm
      · exact False.elim (unique.1 (List.mem_map.mpr ⟨b,hb,same.symm⟩))
    · rcases List.mem_cons.mp two with eb|hb
      · subst top
        exact False.elim (unique.1 (List.mem_map.mpr ⟨a,ha,same⟩))
      · exact ih unique.2 ha hb

theorem coherent_address {p : Plan roles} {a b : GeneralNominalCenteredHeadMatSchemas.Equation}
    (one : Cell p a) (two : Cell p b) (same : a.target = b.target) : a = b := by
  obtain ⟨c,hc,i,k,pat,hk,pi,pc,atA,modeA⟩ := one
  obtain ⟨d,hd,j,l,other,hl,pj,pd,atB,modeB⟩ := two
  have equal := atA.symm.trans (same.trans atB)
  have coords := (GeneralNominalIdentities.source_identity p.packet.context.state.seed _ _).mp equal
  have kinds := congrArg (fun o : GeneralNominalIdentities.Origin => o.2.2.1) coords
  have clauses := congrArg (fun o : GeneralNominalIdentities.Origin => o.2.2.2.1) coords
  have positions := congrArg (fun o : GeneralNominalIdentities.Origin => o.2.2.2.2) coords
  change k = l at kinds
  change c.id = d.id at clauses
  change i = j at positions
  have sameClause := key_unique Clause.id _ p.packet.checked.identified.1 c d hc hd clauses
  subst d; subst j; subst l
  have samePat := Option.some.inj (pi.symm.trans pj)
  subst other
  have expression := Option.some.inj (pc.symm.trans pd)
  cases a; cases b; simp_all

theorem clause_arg (p : Plan roles) (clause : Clause) (inClause : clause ∈ p.packet.declaration.requirements)
    (pos : Fin clause.arguments.length) (n : Nat) (named : normalize clause.arguments[pos.val] = .var n) :
    n ∉ p.packet.declaration.outputNames := by
  intro no
  apply p.packet.checked.outputOnly.2 clause inClause n no
  apply GeneralDictionaryActualSchemaScope.variables_args_member _ clause.arguments[pos.val] (List.getElem_mem ..)
  apply GeneralPatternVariableProvenance.normalize_variables
  simp [named,Pattern.variables]

theorem lower_or_upper (p : Plan roles)
    (clause : Clause) (inClause : clause ∈ p.packet.declaration.requirements) (sig : clause.Signature roles)
    (i : Fin (roles clause.role).arity) (kind : Nat) (which : kind = 3 ∨ kind = 4)
    (eq : GeneralNominalCenteredHeadMatSchemas.Equation)
    (found : eq ∈ (materialize p.packet.registry.constructors p.packet.context.interpretation
      (let pat := clause.arguments[i.val]'(by rw [sig.1]; exact i.isLt)
       let pair := GeneralDeclarationDemands.inputInterval (capture p.packet)
         (((frame p.packet).allocation p.packet.declaration.id clause).arguments i) pat
       ⟨pat, if kind = 3 then pair.1 else pair.2, mode kind⟩)).equations) :
    Taut p eq ∨ Cell p eq := by
  let pos : Fin clause.arguments.length := ⟨i.val,by rw [sig.1]; exact i.isLt⟩
  let pat := clause.arguments[pos.val]
  obtain ⟨translated,target,modeEq⟩ := materializes found
  change translate p.packet.registry.constructors p.packet.context.interpretation pat = _ at translated
  let boundPair := GeneralDeclarationDemands.inputInterval (capture p.packet)
    (((frame p.packet).allocation p.packet.declaration.id clause).arguments i) pat
  change eq.target = (if kind = 3 then boundPair.1 else boundPair.2) at target
  change eq.mode = mode kind at modeEq
  have patEq : clause.arguments[i.val]? = some pat := List.getElem?_eq_some_iff.mpr ⟨pos.isLt,rfl⟩
  cases normalForm : normalize pat with
  | var n =>
    have notOutput := clause_arg p clause inClause pos n normalForm
    have pairEq : boundPair = (capture p.packet).inputs n := by
      simp [boundPair,GeneralDeclarationDemands.inputInterval,normalForm]
    rw [pairEq] at target
    left
    intro m
    have equivalence := GeneralVersionedNormalizedVariable313.normalized_value pat normalForm translated (variables p m) (mode kind)
    unfold GeneralNominalCenteredHeadMatSchemas.Equation.Holds
    rw [target,modeEq]
    rcases which with rfl|rfl <;>
      simpa only [mode,variables,notOutput,ite_false,↓reduceIte,show (4:Nat) ≠ 3 from by decide] using GeneralFiniteTypedWrites312.symmetric equivalence
  | app | record | variant | join =>
    all_goals
      have pairEq : boundPair = (address p 3 clause.id i.val,address p 4 clause.id i.val) := by
        simp only [boundPair,GeneralDeclarationDemands.inputInterval,normalForm]
        rfl
      rw [pairEq] at target
      right
      refine ⟨clause,inClause,i.val,kind,pat,which.elim Or.inl (fun h => .inr (.inl h)),patEq,translated,?_,modeEq⟩
      rcases which with rfl|rfl <;> exact target

theorem center (p : Plan roles) (clause : Clause) (inClause : clause ∈ p.packet.declaration.requirements)
    (sig : clause.Signature roles) (eq : GeneralNominalCenteredHeadMatSchemas.Equation)
    (found : eq ∈ (childSchema p clause sig).equations) : Taut p eq ∨ Cell p eq := by
  obtain ⟨request,req,compiled⟩ := from_request found
  obtain ⟨index,rfl⟩ := List.mem_ofFn.mp req
  let pat := clause.arguments[index.val]'(by rw [sig.1]; exact index.isLt)
  obtain ⟨atExpr,atTarget,atMode⟩ := materializes compiled
  change translate p.packet.registry.constructors p.packet.context.interpretation pat = _ at atExpr
  change eq.target = GeneralNominalVersionedFrame231.emittedCenter p clause.id index.val pat at atTarget
  change eq.mode = .actual at atMode
  cases norm : normalize pat with
  | var n =>
    left
    intro m
    have typeEq := GeneralNominalCenteredHeadMatCompilerSemantics.compiled_normalized (variables := variables p m) atExpr
    rw [norm] at typeEq
    unfold GeneralNominalVersionedFrame231.emittedCenter at atTarget
    rw [norm] at atTarget
    unfold GeneralNominalCenteredHeadMatSchemas.Equation.Holds
    rw [atTarget,atMode]
    have variableEq : variables p m .actual n = (m (binder p n)).1 := by unfold variables; split <;> rfl
    change CommonNominalFullCarrier.Equivalent _ (variables p m .actual n) at typeEq
    rw [variableEq] at typeEq
    exact GeneralFiniteTypedWrites312.symmetric typeEq
  | app | record | variant | join =>
    all_goals
      right
      refine ⟨clause,inClause,index.val,9,pat,.inr (.inr rfl),List.getElem?_eq_some_iff.mpr ⟨_,rfl⟩,
        atExpr,?_,atMode⟩
      unfold GeneralNominalVersionedFrame231.emittedCenter at atTarget
      rw [norm] at atTarget
      exact atTarget


theorem emitted (p : Plan roles)
    (forwarded : ForwardedResult p.packet.declaration)
    (eq : GeneralNominalCenteredHeadMatSchemas.Equation)
    (found : eq ∈ (generated p.packet.registry.constructors p.packet.context.interpretation
      (whereRequests p)).equations) : Taut p eq ∨ Cell p eq := by
  obtain ⟨rq,seen,materialized⟩ := from_request found
  obtain ⟨emit,emitted,inside⟩ := List.mem_flatMap.mp seen
  have posted := (GeneralCanonicalChildOrder.canonicalEmit_perm p.packet.site.occurrence.identity p.packet.declaration
    p.packet.checked (capture p.packet) ((frame p.packet).allocation p.packet.declaration.id)).mem_iff.mpr emitted
  unfold GeneralDeclarationDemands.emitAll at posted
  obtain ⟨item,_,rfl⟩ := List.mem_map.mp posted
  let clause := item.val
  have requirement := p.packet.checked.signature.2.2.2 clause item.property
  unfold GeneralNominalCenteredHeadMatSchemas.emissionRequests at inside
  rcases List.mem_append.mp inside with input|output
  · obtain ⟨arg,args,byArg⟩ := List.mem_flatMap.mp input
    obtain ⟨index,rfl⟩ := List.mem_ofFn.mp args
    rcases List.mem_cons.mp byArg with rfl|next
    · exact lower_or_upper p clause item.property requirement index 3 (.inl rfl) eq materialized
    · cases List.mem_singleton.mp next
      exact lower_or_upper p clause item.property requirement index 4 (.inr rfl) eq materialized
  · obtain ⟨request,requestMember,rfl⟩ := List.mem_map.mp output
    obtain ⟨rule,ruleMember,rfl⟩ := List.mem_map.mp requestMember
    obtain ⟨name,bare,named⟩ := forwarded clause item.property rule ruleMember
    change eq ∈ (materialize p.packet.registry.constructors p.packet.context.interpretation
      ⟨rule.rhs,GeneralDeclarationDemands.outputTarget p.packet.declaration (capture p.packet)
        ((frame p.packet).allocation p.packet.declaration.id clause).outputs rule,.actual⟩).equations at materialized
    have target := GeneralDeclarationDemands.generated_output_target p.packet.declaration (capture p.packet)
      ((frame p.packet).allocation p.packet.declaration.id clause).outputs rule name named bare
    rw [target,bare] at materialized
    left
    intro m
    exact variable_request p m name .actual _ (by simp [variables,binder,named]) eq materialized

theorem classifies (p : Plan roles)
    (forwarded : ForwardedResult p.packet.declaration)
    (eq : GeneralNominalCenteredHeadMatSchemas.Equation) (found : eq ∈ inner p) :
    Taut p eq ∨ Cell p eq := by
  rcases List.mem_append.mp found with whereEq|childEq
  · exact emitted p forwarded eq whereEq
  · obtain ⟨clause,_,here⟩ := List.mem_flatMap.mp childEq
    exact center p clause.val clause.property _ eq here

end Yulang.GeneralVersionedCompoundRows313
