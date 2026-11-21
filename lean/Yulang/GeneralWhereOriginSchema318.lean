import Yulang.GeneralWhereOriginReady318
import Yulang.GeneralWhereOriginDescriptor318

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 24000
set_option maxHeartbeats 15000000
namespace Yulang.GeneralWhereOriginSchema318
open GeneralDeclarations (Clause)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralNominalCenters (Plan)
open GeneralNominalVersionedFrame231 (capture)
open GeneralWhereVersionCompiler317 (args allocation emit emissions schema)
open GeneralWhereOriginDelta318 (Cell)
open GeneralVersionedCompoundRows313 (Taut clause_arg materializes)
open GeneralNominalCenteredHeadMatSchemas (Equation generated materialize emissionRequests inputRequests)
open GeneralNominalMaterialization (Request rootRequests)
open GeneralNominalCenteredHeadMatExpressions (translate)
open GeneralVersionedEndpointAddress315 (Side atCell)
open GeneralNominalVersionedPlans231 (variables)
open GeneralVersionedRootWrites312 (from_request)

def pick (side : Side) (pair : GeneralSourceState.Interval) : Nat :=
  match side with | .lower => pair.1 | .upper => pair.2

def input (p : Plan rs) (c : Clause) (sig : c.Signature rs)
    (i : Fin (rs c.role).arity) (side : Side) : Request :=
  let pat := c.arguments[i.val]'(by rw [sig.1]; exact i.isLt)
  let interval := GeneralDeclarationDemands.inputInterval (capture p.packet) (args p c i) pat
  ⟨pat,pick side interval,side.mode⟩

theorem row_ext (a b : Equation) (target : a.target = b.target)
    (mode : a.mode = b.mode) (expression : a.expression = b.expression) : a = b := by
  cases a; cases b
  simp_all

theorem from_input {p : Plan rs} (c : Clause) (listed : c ∈ p.packet.declaration.requirements)
    (sig : c.Signature rs) (i : Fin (rs c.role).arity) (side : Side) (row : Equation)
    (found : row ∈ (materialize p.packet.registry.constructors p.packet.context.interpretation
      (input p c sig i side)).equations) : Taut p row ∨ ∃ cell : Cell p, row = cell.row := by
  obtain ⟨code,target,polarity⟩ := materializes found
  let pos : Fin c.arguments.length := ⟨i.val,by rw [sig.1]; exact i.isLt⟩
  let pat := c.arguments[pos.val]
  let pair := GeneralDeclarationDemands.inputInterval (capture p.packet) (args p c i) pat
  change translate p.packet.registry.constructors p.packet.context.interpretation pat = some row.expression at code
  change row.target = pick side pair at target
  change row.mode = side.mode at polarity
  have located : c.arguments[i.val]? = some pat := List.getElem?_eq_some_iff.mpr ⟨pos.isLt,rfl⟩
  cases h : normalize pat with
  | var name =>
    have notOut := clause_arg p c listed pos name h
    have equality : pair = (capture p.packet).inputs name := by
      simp [pair,GeneralDeclarationDemands.inputInterval,h]
    rw [equality] at target
    left
    intro m
    have named := GeneralVersionedNormalizedVariable313.normalized_value pat h code (variables p m) side.mode
    unfold Equation.Holds
    rw [target,polarity]
    cases side <;> simpa only [pick,Side.mode,variables,notOut,ite_false] using
      GeneralFiniteTypedWrites312.symmetric named
  | app | record | variant | join =>
    all_goals
      have good : ∀ n, normalize pat ≠ .var n := by
        intro n equal
        rw [h] at equal
        cases equal
      have bounds : pair = (atCell p .lower c.id i.val row.expression,
          atCell p .upper c.id i.val row.expression) := by
        unfold pair
        simp only [GeneralDeclarationDemands.inputInterval,h]
        unfold args
        simp only [located,code]
      rw [bounds] at target
      right
      let cell : Cell p := ⟨c,i.val,side,pat,row.expression,listed,located,good,code⟩
      refine ⟨cell,?_⟩
      apply row_ext row cell.row
      · cases side <;> exact target
      · exact polarity
      · rfl

/-- No fabricated endpoint rows: every non-tautological polarized row of the
corrected compiler is the row of a checked compound source cell. Materialized
actual/associated outputs are kept on their separate proof path. -/
theorem exact_schema {p : Plan rs} (row : Equation) (seen : row ∈ (schema p).equations) :
    row.mode = .actual ∨ Taut p row ∨ ∃ cell : Cell p, row = cell.row := by
  unfold schema at seen
  obtain ⟨request,generated,localRow⟩ := from_request seen
  rcases List.mem_append.mp generated with atRoot|fromChild
  · unfold rootRequests at atRoot
    obtain ⟨out,_,atOut⟩ := List.mem_flatMap.mp atRoot
    obtain ⟨eq,_,rfl⟩ := List.mem_map.mp atOut
    exact .inl (materializes localRow).2.2
  · obtain ⟨e,written,required⟩ := List.mem_flatMap.mp fromChild
    have member := (GeneralCanonicalChildOrder.canonicalEmit_perm p.packet.site.occurrence.identity
      p.packet.declaration p.packet.checked (capture p.packet) (allocation p)).mem_iff.mpr written
    obtain ⟨clause,_,rfl⟩ := List.mem_map.mp member
    let sig := p.packet.checked.signature.2.2.2 clause.val clause.property
    unfold emissionRequests at required
    rcases List.mem_append.mp required with byInput|byOutput
    · obtain ⟨argument,occurred,stored⟩ := List.mem_flatMap.mp byInput
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp occurred
      unfold inputRequests at stored
      rcases List.mem_cons.mp stored with rfl|next
      · exact .inr (from_input clause.val clause.property sig i .lower row localRow)
      · cases List.mem_singleton.mp next
        exact .inr (from_input clause.val clause.property sig i .upper row localRow)
    · obtain ⟨out,_,rfl⟩ := List.mem_map.mp byOutput
      exact .inl (materializes localRow).2.2

end Yulang.GeneralWhereOriginSchema318
