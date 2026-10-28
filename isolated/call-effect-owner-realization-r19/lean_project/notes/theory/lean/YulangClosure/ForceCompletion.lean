import YulangClosure.ForceAdmin

/-!
Candidate r11 completion theorem for the frozen r7 abstract machine.
All payloads and fixed `H`, `beta`, `inst` are arbitrary. Traces and ordered
wrapper lists are literal. No source encoding, concrete instantiation law,
Force applicability, termination, O-NORM, O-RESULT, foreign continuation,
Call theorem, source/native correspondence or parent closure is asserted.
-/
namespace YulangClosure.ForceAdmin

universe u

variable {P : Type u} {H : Nat → Option (V P)}
  {beta : P → P → V P} {inst : P → P → P}

/-- Execute a source-only stack result by recursion on the pending stack.
The saved outer wrappers precede the instantiated current wrappers, which
precede the newly observed body's wrappers at every consumed frame. -/
private theorem stack_result_run
    {K : List (AppFrame P)} {h : Head P} {W : List P}
    {tr : List (Event P)} {out : Head P} {Ws : List P}
    (result : StackResult H beta inst K h W tr out Ws) :
    CountedRun H beta inst tr
      ⟨headValue h, K, W⟩ ⟨headValue out, [], Ws⟩ := by
  induction K generalizing h W tr with
  | nil =>
      rcases result with ⟨rfl, rfl, rfl⟩
      exact .refl _
  | cons frame K ih =>
      rcases frame with ⟨A, W₀⟩
      cases h with
      | node k => exact False.elim result
      | abs b =>
          rcases result with ⟨tb, hb, Wb, rest, obs, stack, rfl⟩
          have body := observe_run obs K (W₀ ++ W.map (inst A))
          have finish := ih (h := hb)
            (W := (W₀ ++ W.map (inst A)) ++ Wb) (tr := rest) stack
          exact .counted .typeBeta (body.trans finish)

/-- Arbitrary-focus finite completion, with the exact trace and literal
ordered endpoint wrappers. `FocusResult` remains the independent source-only
definition from ForceAdmin; no machine run is added to its premises. -/
theorem abstract_focus_counted_run_iff
    (H : Nat → Option (V P)) (beta : P → P → V P) (inst : P → P → P)
    (s : Focus P) (tr : List (Event P)) (out : Head P) (Ws : List P) :
    FocusResult H beta inst s tr out Ws ↔
      CountedRun H beta inst tr s ⟨headValue out, [], Ws⟩ := by
  constructor
  · intro result
    rcases result with ⟨t, h, W, rest, obs, stack, trace⟩
    have observedRun := observe_run obs s.pending s.wrappers
    have suffix := stack_result_run stack
    rw [trace]
    exact observedRun.trans suffix
  · intro run
    have terminal :
        FocusResult H beta inst ⟨headValue out, [], Ws⟩ [] out Ws := by
      exact ⟨[], out, [], [], .head out,
        ⟨rfl, rfl, (List.append_nil Ws).symm⟩, rfl⟩
    have result := run_backward run [] out Ws terminal
    simpa only [List.append_nil] using result

#print abstract_focus_counted_run_iff
#print axioms abstract_focus_counted_run_iff

end YulangClosure.ForceAdmin
