import Yulang.GeneralDeclarativeI65LiteralTypedBody368
import Yulang.GeneralDeclarativeI65PostselectionTies368

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65
open GeneralDeclarativeWitnessCovariantOrigin353 (Problem Row)
open GeneralDeclarativeWitnessTypedOutput354 (Batch Item Write ordinary)
open GeneralDeclarativeWitnessTypedPacket354 (At)
open GeneralDeclarativeWitnessCompiler350 (Context initial portNames placed)
open GeneralDeclarativeWitnessDeclaredState357 (Joined Value pointSpans)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeStableAssemble329 (firsts tieState prepare_grows)
open GeneralDeclarativeStableTies329 (Present pairOf present_entails from_use)
open GeneralDeclarativeEntailment320 (Holds appendFacts)
open GeneralDeclarativeGrowth327 (Extends restrict facts)
open GeneralDeclarativeCurrentReceipt330 (relays_models)
open GeneralDeclarations (Declaration)
open CommonNominalFullCarrier (Equivalent)

theorem typed_at_literal_position {p : Problem} {ctx : Context} {input : Nat → Capture}
    {outs : List GeneralSourceState.Output} (batch : Batch p ctx input outs) {i : Nat} {exactRow : Row}
    (seen : batch.trace[i]? = some (.typed exactRow)) :
    ∃ source : At p ctx input outs i, source.typed.row = exactRow := by
  induction batch generalizing i with
  | nil => simp [Batch.trace] at seen
  | cons item tail ih =>
    cases i with
    | zero =>
      cases item with
      | ordinary e ready target => simp [Batch.trace,Item.write] at seen
      | nominal sourced =>
        have exactId : sourced.row = exactRow := by simpa [Batch.trace,Item.write] using seen
        exact ⟨⟨_,rfl,sourced⟩,exactId⟩
    | succ i =>
      obtain ⟨source,found⟩ := ih (by simpa [Batch.trace] using seen)
      exact ⟨⟨source.demand,source.indexed,source.typed⟩,found⟩

/-- The typed batch's same actual source name and ordinal are retained,
not inferred from type values or from a downstream release. -/
theorem current_typed_write_exact {s : State} {q : Request} {decl : Declaration}
    {ctx : Context} {p : Problem} {kids : List Request}
    (body : TypedWritten (s := s) (q := q) (decl := decl) ctx p kids)
    {i : Nat} {row : Row} (seen : body.outputs.trace[i]? = some (.typed row)) :
    ∃ source : At p ctx (portNames ctx body.ports).input p.demand.outputs i,
      source.typed.row = row ∧ q.demand.outputs[i]? = some source.demand ∧
        row.root = source.demand.target := by
  obtain ⟨source,eq⟩ := typed_at_literal_position body.outputs seen
  exact ⟨source,eq,body.nativeDemand ▸ source.indexed,by rw [←eq]; rfl⟩

theorem typed_run_preserves_repeated_centers {s : State} {q : Request} {decl : Declaration}
    {ctx : Context} {p : Problem} {kids : List Request}
    (body : TypedWritten (s := s) (q := q) (decl := decl) ctx p kids) (m : Model) (fit : Fits s m) :
    ∀ use ∈ ctx.spans, Equivalent (m.assignment use.2.center).1
      (m.assignment ((firsts ctx.spans ctx.fallback use.1).center)).1 := by
  have start : Extends (initial ctx).state body.stateAfterPrep := prepare_grows body.prep
  have finish := relays_models body.receipt m.assignment fit.1.1
  have initFit := restrict start m.assignment (restrict (facts _ _) m.assignment
    (restrict (facts _ _) m.assignment finish))
  have eqs : (initial ctx).state.equations = (tieState ctx.named ctx.spans ctx.fallback).equations :=
    build_keeps_selected_equations ctx.keep (ctx.spans.map Prod.fst) ctx.spans ctx.fallback
      (tieState ctx.named ctx.spans ctx.fallback)
  have remaining : Present (initial ctx).state (firsts ctx.spans ctx.fallback) (ctx.spans.map pairOf) := by
    intro row listed
    rw [eqs]
    exact List.mem_append_right _ listed
  intro use atSource
  exact from_use (present_entails remaining) (List.mem_map.mpr ⟨use,atSource,rfl⟩) m.assignment initFit

/-- The actual compiler spans refer to the exact chosen head,
independently from body success. Repeated use equality is proved
afterward, not required as a shape-matching test. -/
inductive TypedSelectedLayout {s : State} {q : Request} {decl : Declaration}
    (spans : List (Nat × Capture)) : SourceHead s q decl → Prop where
  | ordered {capture h} :
      (∀ n ∈ decl.inputNames, Bounds s.current.ordinary (capture n)) →
      (∀ n ∈ decl.inputNames, ((spans.find? fun item => item.1 == n).map Prod.snd) = some (capture n)) →
      TypedSelectedLayout spans (.ordered capture h)
  | joined {h : Joined s.current q.demand decl} :
      spans = pointSpans h.firstBinder h.lastBinder h.actualValue →
      TypedSelectedLayout spans (.joined h)

structure TypedLocalMeaning {s : State} {q : Request} {decl : Declaration}
    {ctx : Context} {p : Problem} {kids : List Request}
    (pick : AuthoredCandidate s q decl)
    (body : TypedWritten (s := s) (q := q) (decl := decl) ctx p kids) (m : Model) : Prop where
  head : HeadModel s m q decl pick.head
  exactSpans : TypedSelectedLayout ctx.spans pick.head
  exactKids : kids = children q (GeneralDeclarativeEmissionForest322.children ctx.decl
    (portNames ctx body.ports) (placed ctx body.ports))
  fixedTargets : body.outputs.trace.map Write.target = q.demand.outputs.map GeneralSourceState.Output.target
  ordinaryRows : ∀ e ∈ ordinary body.outputs.trace, Holds m.assignment e
  typedRows : ∀ t, .typed t ∈ body.outputs.trace →
      ∃ v : Value, m.authoredValues t.root = some v ∧ v.tag = t.tag ∧ v.name = t.box ∧
        v.arguments = [.inl (m.assignment t.valueName).1]
  repeated : ∀ use ∈ ctx.spans, Equivalent (m.assignment use.2.center).1
      (m.assignment ((firsts ctx.spans ctx.fallback use.1).center)).1

theorem chosen_typed_literal_body_sound {s : State} {q : Request} {decl : Declaration}
    {ctx : Context} {p : Problem} {kids : List Request}
    (pick : AuthoredCandidate s q decl)
    (body : TypedWritten (s := s) (q := q) (decl := decl) ctx p kids)
    (layout : TypedSelectedLayout ctx.spans pick.head) (m : Model) (fit : Fits s m) :
    TypedLocalMeaning pick body m := by
  obtain ⟨targets,writes,typed⟩ := typed_written_all_models body m fit
  exact ⟨source_head_sound pick.head m fit,layout,body.ordered,targets,writes,typed,
    typed_run_preserves_repeated_centers body m fit⟩

end Yulang.GeneralDeclarativeI65
