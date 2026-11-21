import Yulang.GeneralDeclarativeStableInputs329
import Yulang.GeneralDeclarativeTraceExpand323

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeStableTrace329
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarationPatterns (Pattern Constructors normalize)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCenteredHeadMatExpressions (translate)
open GeneralDeclarativeTrace321 (Occurrence Trace)
open GeneralDeclarativeTraceNames321 (trace_keys_modes)
open GeneralDeclarativeTraceExpand323 (convert expands)
open GeneralDeclarativeTraceTransfer325 (ordinary)
open GeneralDeclarativeOpaqueNested328 (occurrences)
open GeneralDeclarativeStableReads329 (One Heads)
open GeneralDeclarativeOrigins321 (Supported restriction)
open CommonRoleOutermostResolver (All₂)

def Located (s : State) (o : Occurrence) (p : Nat × Capture) : Prop :=
  o.binder = p.1 ∧ o.argument = p.2.center ∧ Bounds s p.2

theorem names {s : State} (located : All₂ (Located s) seen spans)
    (actual : ∀ o ∈ seen, o.mode = .actual) :
    seen.map convert = occurrences spans ∧ ∀ a ∈ spans, Bounds s a.2 := by
  induction located with
  | nil => exact ⟨rfl,fun _ h => False.elim (List.not_mem_nil h)⟩
  | @cons o a os as first _ ih =>
    obtain ⟨rest,bounds⟩ := ih (fun o seen => actual o (List.mem_cons_of_mem _ seen))
    have here := actual o List.mem_cons_self
    refine ⟨?_,?_⟩
    · change convert o :: List.map convert os =
        ⟨a.1,.actual,.variable a.2.center⟩ :: occurrences as
      rw [rest]
      simp only [convert,here,first.1,first.2.1]
    · intro found which
      rcases List.mem_cons.mp which with rfl|last
      · exact first.2.2
      · exact bounds found last

/-- A genuine supported actual trace supplies head readback in the
*same* state for every constructor expressible by Trace. The spans
retain the exact centers from the observed occurrences; source or
output authority is not invented by ordinary equality. -/
theorem from_trace {s : State} {p : Supported s done}
    (argBounds : Bounds s arg)
    (printed : translate c i (normalize pat) = some code)
    (real : Trace (restriction p) .actual arg.center code seen)
    (located : All₂ (Located s) seen spans) :
    One s c i arg pat spans ∧ ∀ a ∈ spans, Bounds s a.2 := by
  have a : ∀ o ∈ seen, o.mode = .actual :=
    fun o seenHere => ((trace_keys_modes real).2 o seenHere).elim id id
  obtain ⟨same,known⟩ := names located a
  obtain ⟨form,shown,w⟩ := expands (ordinary p real)
  exact ⟨⟨argBounds,code,form,printed,shown,same ▸ w⟩,known⟩

structure Actual (s : State) (c : Constructors) (i : Interpretation)
    {done : Nat → Prop} (p : Supported s done) (arg : Capture) (pat : Pattern)
    (spans : List (Nat × Capture)) : Prop where
  args : Bounds s arg
  reads : ∃ code seen, translate c i (normalize pat) = some code ∧
    Trace (restriction p) .actual arg.center code seen ∧ All₂ (Located s) seen spans

inductive Aligned (s : State) (c : Constructors) (i : Interpretation)
    {done : Nat → Prop} (p : Supported s done) :
    List Capture → List Pattern → List (Nat × Capture) → Prop where
  | nil : Aligned s c i p [] [] []
  | cons : Actual s c i p a pat first → Aligned s c i p args pats rest →
      Aligned s c i p (a::args) (pat::pats) (first++rest)

theorem ready {s : State} {p : Supported s done} (observed : Aligned s c i p args pats spans) :
    Heads s c i args pats spans ∧ ∀ a ∈ spans, Bounds s a.2 := by
  induction observed with
  | nil => exact ⟨.nil,fun _ h => False.elim (List.not_mem_nil h)⟩
  | cons here _ rest =>
    obtain ⟨_,_,print,traced,tied⟩ := here.reads
    obtain ⟨new,ranges⟩ := from_trace here.args print traced tied
    exact ⟨.cons new rest.1,fun a h => (List.mem_append.mp h).elim (ranges a) (rest.2 a)⟩

end Yulang.GeneralDeclarativeStableTrace329
