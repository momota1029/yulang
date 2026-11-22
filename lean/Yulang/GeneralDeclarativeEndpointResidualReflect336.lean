import Yulang.GeneralDeclarativeEndpointResidualSemantics336
import Yulang.GeneralDeclarativeNewNames321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeEndpointResidualReflect336
open GeneralDeclarativeEndpointRecord336 (interp mask_below)
open GeneralDeclarativeEndpointResidual336 (endpoint_mask)
open GeneralDeclarativeRecordResidual323 (withTail)
open GeneralDeclarativeRecordSpine330 (Terminal)
open GeneralDeclarativeNewNames321 (after before_after)
open CommonRoleCanonicalRows (Row normalize residual)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open CommonNominalFullCarrier (Equivalent Subtype Ty observeTy mask subtype_trans)
open CommonNominalFullDemand (MaskedProbeStep MaskedProbeAt ProbeAt ProbeStep Observation)

def Exact (e : Expr) : Prop := e = .primitive .exactEmpty []

/-- All labels outside a finite rigid residual spine expose the
same exact/width policy, unless a producer mask hides that label. -/
private theorem absent (m) (d : Nat) (key : Nat) (rs : Row Expr) (terminal : Terminal endCode)
    (missing : key ∉ rs.map Prod.fst) (hidden : List Nat) (env) (cmp)
    (obs : Observation CommonNominalFullCarrier.Row) :
    ¬ MaskedProbeStep Common.rowLe env cmp hidden (observeTy d (interp m (withTail rs endCode))) (.field key obs) ∧
    (MaskedProbeStep Common.rowLe env cmp hidden (observeTy d (interp m (withTail rs endCode)))
      (.optional key obs) ↔ (Exact endCode ∧ key ∉ hidden) ∨ obs = .trivial) := by
  induction rs with
  | nil =>
    cases terminal with
    | width =>
      change (¬ MaskedProbeStep Common.rowLe env cmp hidden .emptyRecord (.field key obs)) ∧
        (MaskedProbeStep Common.rowLe env cmp hidden .emptyRecord (.optional key obs) ↔
          (Exact (.primitive .emptyRecord []) ∧ key ∉ hidden) ∨ obs = .trivial)
      simp [MaskedProbeStep,Exact]
    | exactEnd =>
      change (¬ MaskedProbeStep Common.rowLe env cmp hidden .exactEmpty (.field key obs)) ∧
        (MaskedProbeStep Common.rowLe env cmp hidden .exactEmpty (.optional key obs) ↔
          (Exact (.primitive .exactEmpty []) ∧ key ∉ hidden) ∨ obs = .trivial)
      simp [MaskedProbeStep,Exact]
  | cons row rest ih =>
    obtain ⟨label,payload⟩ := row
    have diff : key ≠ label := fun h => missing (h ▸ List.mem_cons_self)
    have clear : key ∉ rest.map Prod.fst := fun h => missing (List.mem_cons_of_mem _ h)
    have old := ih clear
    let t := observeTy d (interp m (withTail rest endCode))
    let f := CommonNominalSyntax.observe (CommonNominalSyntax.graph CommonNominalFullCarrier.Row) d
      (.node (interp m payload))
    change (¬MaskedProbeStep Common.rowLe env cmp hidden (.record label f t) (.field key obs)) ∧
      (MaskedProbeStep Common.rowLe env cmp hidden (.record label f t) (.optional key obs) ↔ _)
    change (¬MaskedProbeStep Common.rowLe env cmp hidden t (.field key obs)) ∧
      (MaskedProbeStep Common.rowLe env cmp hidden t (.optional key obs) ↔ _) at old
    simp only [MaskedProbeStep,diff,false_and,ite_false,old.1,old.2,not_false_eq_true,true_and]
    constructor
    · rintro ((found|seen)|found)
      · exact .inl found
      · exact .inr seen
      · exact .inr found
    · exact Or.inl

/-- Upper/lower comparisons of known syntax residuals can be
unmasked. This is reflection of their *order*, not equivalence of
one arbitrary masked residual to its standalone closed spelling. -/
theorem reflect (m) (keys : List Nat) (ls us : Row Expr) (lo : Terminal le) (hi : Terminal ue)
    (leftClear : ∀ k ∈ keys, k ∉ ls.map Prod.fst)
    (rightClear : ∀ k ∈ keys, k ∉ us.map Prod.fst)
    (masked : Subtype (mask keys (interp m (withTail ls le))) (mask keys (interp m (withTail us ue)))) :
    Subtype (interp m (withTail ls le)) (interp m (withTail us ue)) := by
  let inventory := keys ++ ls.map Prod.fst ++ us.map Prod.fst
  let fresh := after inventory
  have absentFresh : fresh ∉ inventory := fun h => Nat.lt_irrefl _ (before_after h)
  have avoidKeys : fresh ∉ keys := fun h => absentFresh (List.mem_append_left _
    (List.mem_append_left _ h))
  have avoidLow : fresh ∉ ls.map Prod.fst := fun h => absentFresh (List.mem_append_left _
    (List.mem_append_right _ h))
  have avoidHigh : fresh ∉ us.map Prod.fst := fun h => absentFresh (List.mem_append_right _ h)
  intro depth
  apply (CommonNominalFullDemand.producerLe_iff_probe _ _).mpr
  intro rank env obs
  let L := observeTy depth (interp m (withTail ls le))
  let U := observeTy depth (interp m (withTail us ue))
  have preserved := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (masked depth) rank env
  change ∀ obs, ProbeAt Common.rowLe rank env (.mask keys U) obs →
    ProbeAt Common.rowLe rank env (.mask keys L) obs at preserved
  have pushes (o : Observation CommonNominalFullCarrier.Row) :
      MaskedProbeAt Common.rowLe rank env keys U o → MaskedProbeAt Common.rowLe rank env keys L o := by
    rw [← CommonNominalFullDemand.probeAt_mask,← CommonNominalFullDemand.probeAt_mask]
    exact preserved o
  change ProbeAt Common.rowLe rank env U obs → ProbeAt Common.rowLe rank env L obs
  rw [← CommonNominalFullDemand.maskedProbeAt_nil,← CommonNominalFullDemand.maskedProbeAt_nil]
  have other (o : Observation CommonNominalFullCarrier.Row) (h : ¬o.isOuterField) :
      MaskedProbeAt Common.rowLe rank env [] U o → MaskedProbeAt Common.rowLe rank env [] L o := by
    have law (x : CommonNominalFullDemand.Ty CommonNominalFullCarrier.Row) :
      MaskedProbeAt Common.rowLe rank env keys x o ↔ MaskedProbeAt Common.rowLe rank env [] x o := by
      cases rank <;> exact CommonNominalFullDemand.maskedProbeStep_other x keys [] o h
    exact fun found => (law L).mp (pushes o ((law U).mpr found))
  have fields (k : Nat) (test : Observation CommonNominalFullCarrier.Row) :
      (MaskedProbeAt Common.rowLe rank env [] U (.field k test) →
        MaskedProbeAt Common.rowLe rank env [] L (.field k test)) ∧
      (MaskedProbeAt Common.rowLe rank env [] U (.optional k test) →
        MaskedProbeAt Common.rowLe rank env [] L (.optional k test)) := by
    by_cases keyIn : k ∈ keys
    · let cmp : CommonNominalFullDemand.Ty CommonNominalFullCarrier.Row →
        CommonNominalFullDemand.Ty CommonNominalFullCarrier.Row → Prop :=
        match rank with
        | 0 => fun _ _ => True
        | q+1 => fun expected input => ∀ next probe, ProbeAt Common.rowLe q next input probe →
          ProbeAt Common.rowLe q next expected probe
      have reduced (h : List Nat) (x : CommonNominalFullDemand.Ty CommonNominalFullCarrier.Row) (o) :
          MaskedProbeAt Common.rowLe rank env h x o = MaskedProbeStep Common.rowLe env cmp h x o := by
        cases rank <;> rfl
      have qlow := absent m depth fresh ls lo avoidLow keys env cmp test
      have qhigh := absent m depth fresh us hi avoidHigh keys env cmp test
      have klow := absent m depth k ls lo (leftClear k keyIn) [] env cmp test
      have khigh := absent m depth k us hi (rightClear k keyIn) [] env cmp test
      have sinceHigh : MaskedProbeAt Common.rowLe rank env [] U (.optional k test) ↔
          MaskedProbeAt Common.rowLe rank env keys U (.optional fresh test) := by
        rw [reduced,reduced]
        exact khigh.2.trans (by simpa only [avoidKeys,List.not_mem_nil,and_true] using qhigh.2.symm)
      have sinceLow : MaskedProbeAt Common.rowLe rank env keys L (.optional fresh test) ↔
          MaskedProbeAt Common.rowLe rank env [] L (.optional k test) := by
        rw [reduced,reduced]
        exact qlow.2.trans (by simpa only [avoidKeys,List.not_mem_nil,and_true] using klow.2.symm)
      exact ⟨fun no => False.elim (khigh.1 ((reduced _ _ _) ▸ no)),
        fun yes => sinceLow.mp (pushes _ (sinceHigh.mp yes))⟩
    · have same : k ∈ keys ↔ k ∈ ([] : List Nat) := by simp [keyIn]
      have law (x : CommonNominalFullDemand.Ty CommonNominalFullCarrier.Row) :
          (MaskedProbeAt Common.rowLe rank env keys x (.field k test) ↔
            MaskedProbeAt Common.rowLe rank env [] x (.field k test)) ∧
          (MaskedProbeAt Common.rowLe rank env keys x (.optional k test) ↔
            MaskedProbeAt Common.rowLe rank env [] x (.optional k test)) := by
        cases rank <;> exact CommonNominalFullDemand.maskedProbeStep_query_congr x k test keys [] same
      exact ⟨fun one => (law L).1.mp (pushes _ ((law U).1.mpr one)),
        fun two => (law L).2.mp (pushes _ ((law U).2.mpr two))⟩
  cases obs
  case field k test => exact (fields k test).1
  case optional k test => exact (fields k test).2
  all_goals exact other _ (by simp [CommonNominalFullDemand.Observation.isOuterField])

end Yulang.GeneralDeclarativeEndpointResidualReflect336
