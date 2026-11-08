import Yulang.CommonRoleMaterializedDomain
import Yulang.CommonRoleCaptureOrigin

/-! Source-preserving child templates for the int-only materialization adapter.
This bridge preserves source slots through actual unary captures. It does not
establish general interval adequacy or stability of candidate selection. -/
namespace Yulang.CommonRoleChildTemplates
open CommonRoleSettledSyntax CommonRoleOpenProducer CommonRoleCaptureOrigin
open CommonRoleMaterializedDomain
open CommonRoleSettledConstraints (State)

/-- Structural extraction preserves a slot, never identifies it by its value. -/
def extract : Nat → Endpoint n → Option (Endpoint n)
  | 0, e => some e
  | k + 1, .fixed t => (atDepth (k + 1) t).map Endpoint.fixed
  | _ + 1, .slot _ => none
  | k + 1, .wrap _ e => extract k e

/-- Extraction commutes with every state, not merely the creation state. -/
theorem extract_eval (k : Nat) (e : Endpoint n) (s : State n) :
    (extract k e).map (Endpoint.eval s) = atDepth k (e.eval s) := by
  induction k generalizing e with
  | zero => rfl
  | succ k ih =>
    cases e with
    | fixed t =>
      cases h : atDepth (k + 1) t <;> simp [extract, Endpoint.eval, h]
    | slot i =>
      simp only [extract, Option.map_none, Endpoint.eval]
      split <;> rfl
    | wrap c e => exact ih e

/-- A successful materialized capture always has a source template witness. -/
theorem extract_exists (k : Nat) (e : Endpoint n) (s : State n) (payload : Ty)
    (captured : atDepth k (e.eval s) = some payload) :
    ∃ source, extract k e = some source ∧ source.eval s = payload := by
  rw [← extract_eval] at captured
  exact Option.map_eq_some_iff.mp captured

/-- Substitute a source endpoint rather than its current materialized value. -/
def plug : Template → Endpoint n → Endpoint n
  | .var _, e => e
  | .atom a, _ => .fixed (.atom a)
  | .wrap c t, e => .wrap c (plug t e)

theorem plug_eval (t : Template) (e : Endpoint n) (s : State n) :
    (plug t e).eval s = t.instantiate (e.eval s) := by
  induction t <;> simp_all [plug, Endpoint.eval, Template.instantiate]

def childTemplate (r : Nat × Template) (lo hi : Endpoint n) : SourceRequest n :=
  ⟨r.1, plug r.2 lo, plug r.2 hi⟩

theorem child_eval (r : Nat × Template) (lo hi : Endpoint n) (s : State n) :
    (childTemplate r lo hi).eval s =
      ⟨r.1, r.2.instantiate (lo.eval s), r.2.instantiate (hi.eval s)⟩ := by
  simp [childTemplate, SourceRequest.eval, plug_eval]

/-- Actual captures lift to source templates; their provenance continues to hold
at every future state, without assuming the declaration will remain selected. -/
theorem production_lifts (visible : List Declaration) (source : SourceRequest n)
    (s : State n) (d : Declaration) (lp hp : Ty) (depth : Nat)
    (produced : production visible (source.eval s) = some (d, lp, hp))
    (located : captureDepth d.head = some depth) :
    ∃ lo hi : Endpoint n,
      extract depth source.lower = some lo ∧ extract depth source.upper = some hi ∧
      lo.eval s = lp ∧ hi.eval s = hp ∧
      (∀ future : State n,
        atDepth depth (source.lower.eval future) = some (lo.eval future) ∧
        atDepth depth (source.upper.eval future) = some (hi.eval future)) ∧
      (d.requirements.map (fun r => (childTemplate r lo hi).eval s)) =
        children (source.eval s) d lp hp := by
  obtain ⟨lower, upper⟩ := production_origin visible (source.eval s) d lp hp depth produced located
  obtain ⟨lo, loFound, loValue⟩ := extract_exists depth source.lower s lp lower
  obtain ⟨hi, hiFound, hiValue⟩ := extract_exists depth source.upper s hp upper
  refine ⟨lo, hi, loFound, hiFound, loValue, hiValue, ?_, ?_⟩
  · intro future
    constructor
    · rw [← extract_eval, loFound]; rfl
    · rw [← extract_eval, hiFound]; rfl
  · simp only [child_eval, loValue, hiValue, children]

/-- Every actual where child has a source template retaining the parent slots.
The source witness is obtained from production, not supplied as an adequacy assumption. -/
theorem every_child_lifts (visible : List Declaration) (source : SourceRequest n)
    (s : State n) (d : Declaration) (lp hp : Ty) (depth : Nat) (child : Request)
    (produced : production visible (source.eval s) = some (d, lp, hp))
    (located : captureDepth d.head = some depth)
    (generated : child ∈ children (source.eval s) d lp hp) :
    ∃ lo hi : Endpoint n, ∃ r ∈ d.requirements,
      extract depth source.lower = some lo ∧ extract depth source.upper = some hi ∧
      (childTemplate r lo hi).eval s = child ∧
      ∀ future : State n,
        atDepth depth (source.lower.eval future) = some (lo.eval future) ∧
        atDepth depth (source.upper.eval future) = some (hi.eval future) := by
  obtain ⟨lo, hi, lf, hf, _, _, stable, all⟩ :=
    production_lifts visible source s d lp hp depth produced located
  rw [← all] at generated
  obtain ⟨r, required, equal⟩ := List.mem_map.mp generated
  exact ⟨lo, hi, r, required, lf, hf, equal, stable⟩

/-- When the same first-hit candidate is produced later, replay uses the stored
source templates. This is conditional on the observed later production, not a
proof that candidate selection is stable. `production` alone is not selection. -/
theorem replay_children (source : SourceRequest n) (d : Declaration)
    (lo hi : Endpoint n) (depth : Nat)
    (lf : extract depth source.lower = some lo)
    (hf : extract depth source.upper = some hi)
    (located : captureDepth d.head = some depth)
    (future : State n) (visible : List Declaration) (lp hp : Ty)
    (produced : production visible (source.eval future) = some (d, lp, hp)) :
    d.requirements.map (fun r => (childTemplate r lo hi).eval future) =
      children (source.eval future) d lp hp := by
  obtain ⟨lower, upper⟩ := production_origin visible (source.eval future) d lp hp depth produced located
  have l : lo.eval future = lp := by
    have h := extract_eval depth source.lower future
    rw [lf] at h
    exact Option.some.inj (h.trans lower)
  have u : hi.eval future = hp := by
    have h := extract_eval depth source.upper future
    rw [hf] at h
    exact Option.some.inj (h.trans upper)
  simp only [child_eval, l, u, children]

/-- Shape ignores int-only slot materialization, but preserves fixed subtrees. -/
def shape : Endpoint n → Ty
  | .fixed t => t
  | .slot _ => .unknown
  | .wrap c e => .wrap c (shape e)

theorem eval_form (e : Endpoint n) (s : State n) :
    (e.eval s).form = (shape e).form := by
  induction e with
  | fixed t => rfl
  | slot i =>
    simp only [Endpoint.eval]
    split <;> rfl
  | wrap c e ih => simpa [Endpoint.eval, shape, Ty.form] using congrArg CommonRoleCaptureNormalization.Form.tick ih

def sourceWeight (source : SourceRequest n) : Nat :=
  (shape source.lower).weight + (shape source.upper).weight

theorem eval_weight (source : SourceRequest n) (s : State n) :
    CommonRoleOpenDescent.weight (source.eval s) = sourceWeight source := by
  simp [CommonRoleOpenDescent.weight, SourceRequest.eval, sourceWeight,
    Ty.weight, eval_form]

/-- State-independent source-child relation. Each edge carries an actual
production in some state; the state may differ independently at every edge.
The domain is the int-only adapter, not arbitrary interval source graphs. -/
inductive Generated (registry : Registry) : SourceRequest n → SourceRequest n → Prop where
  | step (parent : SourceRequest n) (s : State n) (d : Declaration)
      (lp hp : Ty) (depth : Nat) (lo hi : Endpoint n) (r : Nat × Template)
      (produced : production registry.declarations (parent.eval s) = some (d, lp, hp))
      (located : captureDepth d.head = some depth)
      (lf : extract depth parent.lower = some lo)
      (hf : extract depth parent.upper = some hi)
      (required : r ∈ d.requirements) :
      Generated registry (childTemplate r lo hi) parent

/-- Derived Paterson descent remains valid even if every edge rematerializes
its source in an unrelated ordinary state. It is not same-parent revisit descent. -/
theorem generated_decreases (registry : Registry) (child parent : SourceRequest n)
    (edge : Generated registry child parent) : sourceWeight child < sourceWeight parent := by
  cases edge with
  | step parent s d lp hp depth lo hi r produced located lf hf required =>
    have hit : (d, lp, hp) ∈ hits (scan parent.role
        (parent.lower.eval s) (parent.upper.eval s) registry.declarations) := by
      unfold production at produced
      cases hs : hits (scan (parent.eval s).role (parent.eval s).lower
          (parent.eval s).upper registry.declarations) with
      | nil => simp [hs] at produced
      | cons first rest =>
        have equal : first = (d, lp, hp) := by simpa [hs] using produced
        simp only [SourceRequest.eval] at hs
        rw [hs, equal]
        exact List.mem_cons_self
    obtain ⟨member, _, lower, upper⟩ := CommonRoleOpenProducerAccess.scan_hit_origin
      _ _ _ _ d lp hp ((CommonRoleOpenProducerAccess.mem_hits ..).mp hit)
    have desc := CommonRoleOpenDescent.checked_child_decreases d (registry.checked d member)
      r required _ _ lp hp lower upper
    obtain ⟨l, u⟩ := production_origin registry.declarations (parent.eval s) d lp hp depth produced located
    have lv : lo.eval s = lp := by
      have h := extract_eval depth parent.lower s
      rw [lf] at h
      exact Option.some.inj (h.trans l)
    have uv : hi.eval s = hp := by
      have h := extract_eval depth parent.upper s
      rw [hf] at h
      exact Option.some.inj (h.trans u)
    rw [← eval_weight (childTemplate r lo hi) s, ← eval_weight parent s]
    simpa [CommonRoleOpenDescent.weight, childTemplate, plug_eval, lv, uv, SourceRequest.eval] using desc

/-- Accessibility is derived, with no supplied Acc/fuel/closure premise.
Only child creation is covered, not a saturation loop revisiting the same parent. -/
theorem generated_accessible (registry : Registry) (parent : SourceRequest n) :
    Acc (Generated registry) parent := by
  have all : ∀ measure, ∀ p : SourceRequest n, sourceWeight p = measure →
      Acc (Generated registry) p := by
    intro measure
    induction measure using Nat.strongRecOn with
    | ind measure ih =>
      intro p equal
      constructor
      intro child edge
      exact ih (sourceWeight child) (by rw [← equal]; exact generated_decreases registry child p edge)
        child rfl
  exact all (sourceWeight parent) parent rfl

/-- Every actual child of a capture-bearing production is represented by an
edge in the source-template relation, so the derived accessibility applies. -/
theorem every_child_generated (registry : Registry) (source : SourceRequest n)
    (s : State n) (d : Declaration) (lp hp : Ty) (depth : Nat) (child : Request)
    (produced : production registry.declarations (source.eval s) = some (d, lp, hp))
    (located : captureDepth d.head = some depth)
    (generated : child ∈ children (source.eval s) d lp hp) :
    ∃ childSource : SourceRequest n,
      childSource.eval s = child ∧ Generated registry childSource source ∧
      Acc (Generated registry) childSource := by
  obtain ⟨lo, hi, r, required, lf, hf, equal, _⟩ :=
    every_child_lifts registry.declarations source s d lp hp depth child produced located generated
  exact ⟨childTemplate r lo hi, equal,
    .step source s d lp hp depth lo hi r produced located lf hf required,
    generated_accessible registry _⟩

end Yulang.CommonRoleChildTemplates
