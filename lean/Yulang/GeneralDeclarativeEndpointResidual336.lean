import Yulang.GeneralDeclarativeEndpointRecord336

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeEndpointResidual336
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativeEndpointRecord336 (Read interp mask_equiv mask_below)
open GeneralDeclarativeRecordResidual323 (withTail)
open GeneralDeclarativeRecordSpine330 (Terminal Spine ends)
open GeneralDeclarativeVisibleRecord326 (visible_spine)
open GeneralDeclarativeWhere319 (InInterval)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans eqv_symm)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open CommonRoleCanonicalRows (Row normalize residual)
open CommonNominalFullCarrier (Ty Equivalent Subtype mask observeTy record)
open CommonNominalFullDemand (MaskedProbeStep MaskedProbeAt Observation ProbeAt)
open CommonNominalSyntax (Layer)

private theorem known_record {r : Row Expr} {e : Expr} (terminal : Terminal e)
    (m) (d : Nat) :
    (observeTy d (interp m (withTail r e)) = .emptyRecord) ∨
    (observeTy d (interp m (withTail r e)) = .exactEmpty) ∨
    (∃ k f rest, observeTy d (interp m (withTail r e)) = .record k f rest) := by
  cases r with
  | nil =>
    cases terminal with
    | width => exact .inl rfl
    | exactEnd => exact .inr (.inl rfl)
  | cons a fields =>
    cases a with
    | mk k v => exact .inr (.inr ⟨k,_,_,rfl⟩)

private theorem peel_finite {hidden : List Nat} {key : Nat} (inside : key ∈ hidden)
    {tail : CommonNominalFullDemand.Ty CommonNominalFullCarrier.Row}
    (known : tail = .emptyRecord ∨ tail = .exactEmpty ∨ ∃ k f rest, tail = .record k f rest)
    (value) (env) (cmp) (obs : Observation CommonNominalFullCarrier.Row) :
    MaskedProbeStep Common.rowLe env cmp hidden (.record key value tail) obs ↔
    MaskedProbeStep Common.rowLe env cmp hidden tail obs := by
  rcases known with h|h|⟨k,f,rest,h⟩ <;> subst tail <;> cases obs <;>
    simp [MaskedProbeStep,inside]
  rename_i label obs
  by_cases found : label = k ∧ k ∉ hidden
  · simp [found]
    intro trivialObs
    subst obs
    exact CommonNominalFullDemand.maskedProbeStep_trivial [] f
  · simp [found]; exact Or.inr

theorem peel {key : Nat} {hidden : List Nat} (removed : key ∈ hidden)
    (fields : Row Expr) (endCode : Expr) (terminal : Terminal endCode) (f : Expr) (m) :
    Equivalent (mask hidden (interp m (withTail ((key,f)::fields) endCode)))
      (mask hidden (interp m (withTail fields endCode))) := by
  have all (depth : Nat) : CommonNominalFullDemand.ProducerEq Common.rowLe
    (observeTy depth (mask hidden (interp m (withTail ((key,f)::fields) endCode))))
    (observeTy depth (mask hidden (interp m (withTail fields endCode)))) := by
    apply (CommonNominalFullDemand.producerEq_iff_probe _ _).mpr
    intro rank env obs
    change ProbeAt Common.rowLe rank env (.mask hidden
      (.record key _ (observeTy depth (interp m (withTail fields endCode))))) obs ↔
      ProbeAt Common.rowLe rank env (.mask hidden (observeTy depth (interp m (withTail fields endCode)))) obs
    rw [CommonNominalFullDemand.probeAt_mask,CommonNominalFullDemand.probeAt_mask]
    cases rank <;> exact peel_finite removed (known_record terminal m depth) _ env _ obs
  exact ⟨fun d => (all d).1,fun d => (all d).2⟩

theorem prefix_mask (removed : ∀ f ∈ front, f.1 ∈ hidden)
    (terminal : Terminal endCode) (m) :
    Equivalent (mask hidden (interp m (withTail (front ++ suffix) endCode)))
      (mask hidden (interp m (withTail suffix endCode))) := by
  induction front with
  | nil => exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
  | cons first more ih =>
    obtain ⟨key,f⟩ := first
    exact eqv_trans (peel (removed _ List.mem_cons_self) _ _ terminal _ m)
      (ih (fun e there => removed e (List.mem_cons_of_mem _ there)))

/-- Retain the endpoint's own width/exact terminal. A consumer looking
at a removed field must still respect the same outer mask. This does
not replace an exact-closed residual by a width-open one. -/
theorem endpoint_mask (raw : Row Expr) (keys : List Nat) (terminal : Terminal endCode) (m) :
    Equivalent (mask keys (interp m (withTail raw endCode)))
      (mask keys (interp m (withTail (residual keys (normalize raw)) endCode))) := by
  have normalized := visible_spine m raw endCode
  have cut := GeneralDeclarativeRecordResidual323.reconstruct_with_terminal m (normalize raw) keys endCode
    (CommonRoleCanonicalRows.normalize_unique raw)
  rw [GeneralDeclarativeRecordResidual323.withTail_append] at cut
  have marked {e : Nat × Expr} (part : e ∈ CommonRoleCanonicalRows.selected keys (normalize raw)) :
      e.1 ∈ keys := by
    simpa using (List.mem_filter.mp part).2
  exact eqv_trans (mask_equiv keys (eqv_trans normalized cut))
    (prefix_mask (fun e h => marked h) terminal m)

theorem exact_residuals {s : State} {p : Supported s done} (r : Read p arg keys ls us first last le ue)
    (m) (fit : Models s m) :
    InInterval (mask keys (interp m (withTail (residual keys (normalize ls)) le)))
      (mask keys (interp m (withTail (residual keys (normalize us)) ue)))
      (mask keys (m arg.center).1) := by
  have cut := GeneralDeclarativeEndpointRecord336.residual_interval r m fit
  have low := endpoint_mask ls keys (ends r.lo) m
  have high := endpoint_mask us keys (ends r.hi) m
  exact ⟨CommonNominalFullCarrier.subtype_trans low.2 cut.1,
    CommonNominalFullCarrier.subtype_trans cut.2 high.1⟩

end Yulang.GeneralDeclarativeEndpointResidual336
