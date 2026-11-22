import Yulang.GeneralDeclarativeEndpointResidual336

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeEndpointResidualSemantics336
open GeneralDeclarativeEndpointRecord336 (interp)
open GeneralDeclarativeEndpointResidual336 (endpoint_mask)
open GeneralDeclarativeRecordResidual323 (withTail)
open CommonRoleCanonicalRows (Row normalize residual)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open CommonNominalFullCarrier (Equivalent Subtype Ty Row observeTy mask)
open CommonNominalFullDemand (MaskedProbeStep MaskedProbeAt ProbeAt ProbeStep Observation)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans eqv_symm)

abbrev opened : Expr := .primitive .emptyRecord []
abbrev closed : Expr := .primitive .exactEmpty []

private theorem hidden_absent (m) (d : Nat) (key : Nat) (rs : List (Nat × Expr))
    (missing : key ∉ rs.map Prod.fst) (hidden : List Nat) (env) (cmp)
    (obs : Observation CommonNominalFullCarrier.Row) :
    ¬ MaskedProbeStep Common.rowLe env cmp hidden (observeTy d (interp m (withTail rs opened))) (.field key obs) ∧
    (MaskedProbeStep Common.rowLe env cmp hidden (observeTy d (interp m (withTail rs opened)))
      (.optional key obs) ↔ obs = .trivial) := by
  induction rs with
  | nil =>
    change (¬ MaskedProbeStep Common.rowLe env cmp hidden .emptyRecord (.field key obs)) ∧
      (MaskedProbeStep Common.rowLe env cmp hidden .emptyRecord (.optional key obs) ↔ obs = .trivial)
    simp [MaskedProbeStep]
  | cons first rest ih =>
    obtain ⟨label,item⟩ := first
    have different : key ≠ label := fun e => missing (e ▸ List.mem_cons_self)
    have suffix : key ∉ rest.map Prod.fst := fun e => missing (List.mem_cons_of_mem _ e)
    have old := ih suffix
    let t := observeTy d (interp m (withTail rest opened))
    let f := CommonNominalSyntax.observe (CommonNominalSyntax.graph CommonNominalFullCarrier.Row) d
      (.node (interp m item))
    change (¬MaskedProbeStep Common.rowLe env cmp hidden (.record label f t) (.field key obs)) ∧
      (MaskedProbeStep Common.rowLe env cmp hidden (.record label f t) (.optional key obs) ↔ obs = .trivial)
    change (¬MaskedProbeStep Common.rowLe env cmp hidden t (.field key obs)) ∧
      (MaskedProbeStep Common.rowLe env cmp hidden t (.optional key obs) ↔ obs = .trivial) at old
    simp only [MaskedProbeStep,different,false_and,ite_false,old.1,old.2,not_false_eq_true,true_and,or_self]

/-- If the original tail is width-open and every captured label is
already absent from the residual spine, the internal mask has no
effect on the standalone residual. This is not true for exact-closed
residuals at consumed labels. -/
theorem open_disjoint (m) (keys : List Nat) (rs : List (Nat × Expr))
    (missing : ∀ k ∈ keys, k ∉ rs.map Prod.fst) :
    Equivalent (mask keys (interp m (withTail rs opened))) (interp m (withTail rs opened)) := by
  have all (depth : Nat) :
      CommonNominalFullDemand.ProducerEq Common.rowLe
        (observeTy depth (mask keys (interp m (withTail rs opened)))) (observeTy depth (interp m (withTail rs opened))) := by
    apply (CommonNominalFullDemand.producerEq_iff_probe _ _).mpr
    intro rank env obs
    let t := observeTy depth (interp m (withTail rs opened))
    change ProbeAt Common.rowLe rank env (.mask keys t) obs ↔ ProbeAt Common.rowLe rank env t obs
    rw [CommonNominalFullDemand.probeAt_mask,← CommonNominalFullDemand.maskedProbeAt_nil]
    have rest {o : Observation CommonNominalFullCarrier.Row} (notField : ¬o.isOuterField) :
        MaskedProbeAt Common.rowLe rank env keys t o ↔ MaskedProbeAt Common.rowLe rank env [] t o := by
      cases rank <;> exact CommonNominalFullDemand.maskedProbeStep_other t keys [] o notField
    have fields (label : Nat) (inner : Observation CommonNominalFullCarrier.Row) :
        (MaskedProbeAt Common.rowLe rank env keys t (.field label inner) ↔
         MaskedProbeAt Common.rowLe rank env [] t (.field label inner)) ∧
        (MaskedProbeAt Common.rowLe rank env keys t (.optional label inner) ↔
         MaskedProbeAt Common.rowLe rank env [] t (.optional label inner)) := by
      by_cases seen : label ∈ keys
      · cases rank
        · have h := hidden_absent m depth label rs (missing label seen) keys env (fun _ _ => True) inner
          have u := hidden_absent m depth label rs (missing label seen) [] env (fun _ _ => True) inner
          exact ⟨⟨fun a => False.elim (h.1 a),fun b => False.elim (u.1 b)⟩,h.2.trans u.2.symm⟩
        · rename_i rank
          let cmp := fun expected input => ∀ next test, ProbeAt Common.rowLe rank next input test →
            ProbeAt Common.rowLe rank next expected test
          have h := hidden_absent m depth label rs (missing label seen) keys env cmp inner
          have u := hidden_absent m depth label rs (missing label seen) [] env cmp inner
          exact ⟨⟨fun a => False.elim (h.1 a),fun b => False.elim (u.1 b)⟩,h.2.trans u.2.symm⟩
      · have same : label ∈ keys ↔ label ∈ ([] : List Nat) := by simp [seen]
        cases rank <;> exact CommonNominalFullDemand.maskedProbeStep_query_congr t label inner keys [] same
    cases obs
    case field k x => exact (fields k x).1
    case optional k x => exact (fields k x).2
    all_goals exact rest (by simp [CommonNominalFullDemand.Observation.isOuterField])
  exact ⟨fun d => (all d).1,fun d => (all d).2⟩

theorem open_exact (m) (keys : List Nat) (raw : List (Nat × Expr)) :
    Equivalent (mask keys (interp m (withTail raw opened)))
      (interp m (withTail (residual keys (normalize raw)) opened)) := by
  refine eqv_trans (endpoint_mask raw keys .width m) (open_disjoint m keys _ ?_)
  intro k selected inLeft
  obtain ⟨e,listed,this⟩ := List.mem_map.mp inLeft
  exact (CommonRoleCanonicalRows.mem_residual keys _ _ |>.mp listed).2 (this ▸ selected)


open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativeWhere319 (InInterval)

theorem open_interval {s : State} {p : Supported s done}
    (r : GeneralDeclarativeEndpointRecord336.Read p arg keys lower upper first last opened opened)
    (m) (fit : Models s m) :
    InInterval (interp m (withTail (residual keys (normalize lower)) opened))
      (interp m (withTail (residual keys (normalize upper)) opened)) (mask keys (m arg.center).1) := by
  have sem := GeneralDeclarativeEndpointRecord336.residual_interval r m fit
  have lo := open_exact m keys lower
  have hi := open_exact m keys upper
  exact ⟨CommonNominalFullCarrier.subtype_trans lo.2 sem.1,CommonNominalFullCarrier.subtype_trans sem.2 hi.1⟩

/-- The exact cut is at the consumed label, not at unrelated labels.
An unmasked exact-empty record knows that label absent, whereas a
producer mask deliberately forgets its optional observation. -/
theorem closed_distinct (keys : List Nat) (label : Nat) (hidden : label ∈ keys) :
    ¬ Subtype (mask keys CommonNominalFullCarrier.exactEmpty) CommonNominalFullCarrier.exactEmpty := by
  intro below
  let env : CommonNominalFullDemand.Environment CommonNominalFullCarrier.Row :=
    ⟨fun _ => .bottom,fun _ => []⟩
  have expected : ProbeAt Common.rowLe 0 env .exactEmpty (.optional label (.base .int)) := by
    simp [ProbeAt,ProbeStep,MaskedProbeStep]
  have impossible := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (below 0) 0 env _ expected
  change ProbeAt Common.rowLe 0 env (.mask keys .exactEmpty) (.optional label (.base .int)) at impossible
  simp [ProbeAt,ProbeStep,MaskedProbeStep,hidden] at impossible

end Yulang.GeneralDeclarativeEndpointResidualSemantics336
