import Init

/-!
Abstract finite-success observation only (r7). `inst` is an arbitrary fixed
whole-packet action: no concrete source instantiation law is proved here.
No source encoding, raw error completeness, termination, O-NORM, O-RESULT,
Force realization, Call theorem or parent soundness follows from this module.
-/
namespace YulangClosure.ForceAdmin

universe u

inductive V (P : Type u) where
  | ref : Nat → V P
  | app : V P → P → V P
  | abs : P → V P
  | view : P → V P → V P
  | node : P → V P

inductive Head (P : Type u) where
  | abs : P → Head P
  | node : P → Head P

def headValue {P : Type u} : Head P → V P
  | .abs b => .abs b
  | .node k => .node k

inductive Event (P : Type u) where
  | ref : Nat → V P → Event P
  | typeBeta : P → P → V P → Event P
  | peel : P → Event P
  | inApp : P → Event P → Event P

/-- Defined directly from syntax and lookup, independently of the machine. -/
inductive SourceObserve {P : Type u} (H : Nat → Option (V P))
    (beta : P → P → V P) (inst : P → P → P) :
    V P → List (Event P) → Head P → List P → Prop where
  | head (h) : SourceObserve H beta inst (headValue h) [] h []
  | reference {r v tr h W} : H r = some v →
      SourceObserve H beta inst v tr h W →
      SourceObserve H beta inst (.ref r) (.ref r v :: tr) h W
  | view {chi v tr h W} : SourceObserve H beta inst v tr h W →
      SourceObserve H beta inst (.view chi v) (.peel chi :: tr) h (chi :: W)
  | application {f A b tr₁ tr₂ h W₁ W₂} :
      SourceObserve H beta inst f tr₁ (.abs b) W₁ →
      SourceObserve H beta inst (beta b A) tr₂ h W₂ →
      SourceObserve H beta inst (.app f A)
        (tr₁.map (.inApp A) ++ [.typeBeta b A (beta b A)] ++ tr₂)
        h (W₁.map (inst A) ++ W₂)

structure AppFrame (P : Type u) where
  argument : P
  savedOuterWrappers : List P

structure Focus (P : Type u) where
  current : V P
  pending : List (AppFrame P)
  wrappers : List P

def lift {P : Type u} : List (AppFrame P) → Event P → Event P
  | [], e => e
  | frame :: K, e => lift K (.inApp frame.argument e)

/-- Only `focus` is silent. All three administrative operations emit events. -/
inductive AdminMicro {P : Type u} (H : Nat → Option (V P))
    (beta : P → P → V P) (inst : P → P → P) :
    Option (Event P) → Focus P → Focus P → Prop where
  | focus {f A K W} : AdminMicro H beta inst none
      ⟨.app f A, K, W⟩ ⟨f, ⟨A, W⟩ :: K, []⟩
  | reference {r v K W} : H r = some v →
      AdminMicro H beta inst (some (lift K (.ref r v)))
        ⟨.ref r, K, W⟩ ⟨v, K, W⟩
  | peel {chi v K W} :
      AdminMicro H beta inst (some (lift K (.peel chi)))
        ⟨.view chi v, K, W⟩ ⟨v, K, W ++ [chi]⟩
  | typeBeta {b A W₀ K W} :
      AdminMicro H beta inst (some (lift K (.typeBeta b A (beta b A))))
        ⟨.abs b, ⟨A, W₀⟩ :: K, W⟩
        ⟨beta b A, K, W₀ ++ W.map (inst A)⟩

/-- Independent finite machine runs, with silent edges contributing no event. -/
inductive CountedRun {P : Type u} (H : Nat → Option (V P))
    (beta : P → P → V P) (inst : P → P → P) :
    List (Event P) → Focus P → Focus P → Prop where
  | refl (s) : CountedRun H beta inst [] s s
  | silent {a b c tr} : AdminMicro H beta inst none a b →
      CountedRun H beta inst tr b c → CountedRun H beta inst tr a c
  | counted {a b c tr e} : AdminMicro H beta inst (some e) a b →
      CountedRun H beta inst tr b c → CountedRun H beta inst (e :: tr) a c

variable {P : Type u} {H : Nat → Option (V P)}
  {beta : P → P → V P} {inst : P → P → P}

theorem CountedRun.trans {a b c : Focus P} {xs ys : List (Event P)}
    (p : CountedRun H beta inst xs a b) (q : CountedRun H beta inst ys b c) :
    CountedRun H beta inst (xs ++ ys) a c := by
  revert q
  induction p with
  | refl => intro q; exact q
  | silent e _ ih => intro q; exact .silent e (ih q)
  | counted e _ ih => intro q; exact .counted e (ih q)

/-- Local segment: it preserves K; it makes no claim about a foreign suffix. -/
theorem observe_run {v tr h W} (p : SourceObserve H beta inst v tr h W) :
    ∀ (K : List (AppFrame P)) (W₀ : List P),
      CountedRun H beta inst (tr.map (lift K))
        ⟨v, K, W₀⟩ ⟨headValue h, K, W₀ ++ W⟩ := by
  induction p with
  | head h =>
      intro K W₀
      simpa using (CountedRun.refl (H := H) (beta := beta) (inst := inst)
        (⟨headValue h, K, W₀⟩ : Focus P))
  | reference eq _ ih =>
      intro K W₀
      exact .counted (.reference eq) (ih K W₀)
  | @view chi v tr h W _ ih =>
      intro K W₀
      simpa [List.append_assoc] using
        (CountedRun.counted (AdminMicro.peel (H := H) (beta := beta) (inst := inst)
          (chi := chi) (v := v) (K := K) (W := W₀))
          (ih K (W₀ ++ [chi])))
  | @application f A b tr₁ tr₂ h W₁ W₂ _ _ ih₁ ih₂ =>
      intro K W₀
      have first : CountedRun H beta inst (tr₁.map (lift (⟨A, W₀⟩ :: K)))
          ⟨f, ⟨A, W₀⟩ :: K, []⟩ ⟨.abs b, ⟨A, W₀⟩ :: K, W₁⟩ := by
        simpa [headValue] using ih₁ (⟨A, W₀⟩ :: K) []
      have second := CountedRun.counted
        (AdminMicro.typeBeta (H := H) (beta := beta) (inst := inst)
          (b := b) (A := A) (W₀ := W₀) (K := K) (W := W₁))
        (ih₂ K (W₀ ++ W₁.map (inst A)))
      have whole := CountedRun.silent
        (AdminMicro.focus (H := H) (beta := beta) (inst := inst))
        (first.trans second)
      simpa [List.map_append, List.map_map, Function.comp_def, lift,
        List.append_assoc] using whole

/- The following invariant describes completion using ONLY SourceObserve and
   a structural recursion on the pending stack, never CountedRun/AdminMicro. -/
def StackResult (H : Nat → Option (V P)) (beta : P → P → V P)
    (inst : P → P → P) : List (AppFrame P) → Head P → List P →
    List (Event P) → Head P → List P → Prop
  | [], h, W, tr, out, Ws => tr = [] ∧ out = h ∧ Ws = W
  | frame :: K, .node _, _, _, _, _ => False
  | frame :: K, .abs b, W, tr, out, Ws =>
      ∃ tb hb Wb rest,
        SourceObserve H beta inst (beta b frame.argument) tb hb Wb ∧
        StackResult H beta inst K hb
          ((frame.savedOuterWrappers ++ W.map (inst frame.argument)) ++ Wb)
          rest out Ws ∧
        tr = lift K (.typeBeta b frame.argument (beta b frame.argument)) ::
          (tb.map (lift K) ++ rest)

def FocusResult (H : Nat → Option (V P)) (beta : P → P → V P)
    (inst : P → P → P) (s : Focus P) (tr : List (Event P))
    (out : Head P) (Ws : List P) : Prop :=
  ∃ t h W rest,
    SourceObserve H beta inst s.current t h W ∧
    StackResult H beta inst s.pending h (s.wrappers ++ W) rest out Ws ∧
    tr = t.map (lift s.pending) ++ rest

def emitted {P : Type u} : Option (Event P) → List (Event P)
  | none => []
  | some e => [e]

/-- Backward preservation of a source-only completion invariant. -/
theorem micro_backward {tag a b tr out Ws}
    (step : AdminMicro H beta inst tag a b)
    (p : FocusResult H beta inst b tr out Ws) :
    FocusResult H beta inst a (emitted tag ++ tr) out Ws := by
  cases step with
  | @reference r v K W eq =>
      rcases p with ⟨t, h, Wr, rest, obs, stack, trace⟩
      refine ⟨.ref r v :: t, h, Wr, rest, .reference eq obs, stack, ?_⟩
      simpa [emitted, List.map_cons, trace]
  | @peel chi v K W =>
      rcases p with ⟨t, h, Wr, rest, obs, stack, trace⟩
      refine ⟨.peel chi :: t, h, chi :: Wr, rest, .view obs, ?_, ?_⟩
      · simpa [List.append_assoc] using stack
      · simpa [emitted, List.map_cons, trace]
  | @typeBeta b A W₀ K W =>
      rcases p with ⟨t, h, Wr, rest, obs, stack, trace⟩
      refine ⟨[], .abs b, [],
        lift K (.typeBeta b A (beta b A)) :: (t.map (lift K) ++ rest),
        .head (.abs b), ?_, ?_⟩
      · simp only [Focus.pending, Focus.wrappers, List.append_nil, StackResult]
        exact ⟨t, h, Wr, rest, obs, stack, rfl⟩
      · simpa [emitted, trace]
  | @focus f A K W =>
      rcases p with ⟨t, h, Wr, rest, obs, stack, trace⟩
      cases h with
      | node k => exact False.elim stack
      | abs b =>
          rcases stack with ⟨tb, hb, Wb, restb, ob, sb, erest⟩
          refine ⟨t.map (.inApp A) ++ [.typeBeta b A (beta b A)] ++ tb,
            hb, Wr.map (inst A) ++ Wb, restb, .application obs ob, ?_, ?_⟩
          · simpa [List.append_assoc] using sb
          · simp only [Focus.pending] at trace
            simp [emitted, trace, erest, List.map_append, List.map_map,
              Function.comp_def, lift, List.append_assoc]

private theorem terminal_result (h : Head P) (W : List P) :
    FocusResult H beta inst ⟨headValue h, [], W⟩ [] h W := by
  exact ⟨[], h, [], [], .head h, ⟨rfl, rfl, (List.append_nil W).symm⟩, rfl⟩

theorem run_backward {a b tr} (run : CountedRun H beta inst tr a b) :
    ∀ tail out Ws, FocusResult H beta inst b tail out Ws →
      FocusResult H beta inst a (tr ++ tail) out Ws := by
  induction run with
  | refl => intro tail out Ws p; exact p
  | silent step _ ih =>
      intro tail out Ws p
      simpa [emitted] using micro_backward step (ih tail out Ws p)
  | counted step _ ih =>
      intro tail out Ws p
      simpa [emitted] using micro_backward step (ih tail out Ws p)

/-- Arbitrary fixed `inst`; finite successful traces and literal wrappers only. -/
theorem abstract_observe_counted_run_iff
    (H : Nat → Option (V P)) (beta : P → P → V P) (inst : P → P → P)
    (v : V P) (tr : List (Event P)) (h : Head P) (W : List P) :
    SourceObserve H beta inst v tr h W ↔
      CountedRun H beta inst tr ⟨v, [], []⟩ ⟨headValue h, [], W⟩ := by
  constructor
  · intro obs
    simpa [lift] using observe_run obs [] []
  · intro run
    have result := run_backward run [] h W (terminal_result h W)
    rcases result with ⟨t, hh, Wr, rest, obs, stack, trace⟩
    simp only [Focus.pending, Focus.wrappers, List.nil_append, StackResult] at stack
    rcases stack with ⟨rfl, rfl, rfl⟩
    have eq : tr = t := by simpa [lift] using trace
    cases eq
    exact obs

/-- Literal wrapper nesting: no commutation, cancellation or union. -/
def wrap (W : List P) (v : V P) : V P :=
  match W with
  | [] => v
  | chi :: rest => .view chi (wrap rest v)

theorem wrap_append (W₁ W₂ : List P) (v : V P) :
    wrap (W₁ ++ W₂) v = wrap W₁ (wrap W₂ v) := by
  induction W₁ with
  | nil => rfl
  | cons chi rest ih => exact congrArg (V.view chi) ih

#print abstract_observe_counted_run_iff
#print axioms abstract_observe_counted_run_iff
#print axioms wrap_append

end YulangClosure.ForceAdmin
