import Yulang.GeneralDeclarativeRepresentatives321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeTraceNames321
open GeneralDeclarativeHead320 (State byMode)
open GeneralDeclarativeTrace321 (Occurrence Links Trace TraceArgs)
open GeneralDeclarativeRepresentatives321 (choose used_mode)
open GeneralDeclarativeLowerKnown321 (Alias)
open GeneralDeclarativeWhere319 (Capture)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalMaterialization (Mode)

mutual
 def names : Expr → List Nat
  | .variable b => [b]
  | .primitive _ es | .nominal _ es => namesMany es
  | .record _ a b | .join a b => names a ++ names b
  | .variant _ x => names x
 def namesMany : List Expr → List Nat
  | [] => []
  | e :: rest => names e ++ namesMany rest
end

def Keys (seen : List Occurrence) (expected : List Nat) : Prop := seen.map Occurrence.binder = expected

def Modes (seen : List Occurrence) (mode : Mode) : Prop :=
  ∀ o ∈ seen, o.mode = mode ∨ o.mode = .actual

theorem Modes.append {first last : List Occurrence} {mode : Mode}
    (one : Modes first mode) (two : Modes last mode) : Modes (first ++ last) mode :=
  fun o seen => (List.mem_append.mp seen).elim (one o) (two o)

theorem Keys.append {first last : List Occurrence} (one : Keys first a) (two : Keys last b) :
    Keys (first ++ last) (a ++ b) := by
  unfold Keys at *
  rw [List.map_append,one,two]

theorem trace_keys_modes (walk : Trace s mode root expr seen) :
    Keys seen (names expr) ∧ Modes seen mode := by
  exact Trace.rec
    (motive_1 := fun md _ code uses _ => Keys uses (names code) ∧ Modes uses md)
    (motive_2 := fun md _ codes uses _ => Keys uses (namesMany codes) ∧ Modes uses md)
    (by
      intro md a v
      refine ⟨rfl,?_⟩
      intro o here
      cases List.mem_singleton.mp here
      exact .inl rfl)
    (by intros; assumption)
    (by
      intro n src tag args targets uses md _ _ _ ih
      exact ⟨ih.1,fun o h => .inr ((ih.2 o h).elim id id)⟩)
    (by
      intro n src field a b md x xs y ys _ _ _ _ hx hy
      exact ⟨hx.1.append hy.1,hx.2.append hy.2⟩)
    (by intros; assumption)
    (by
      intro n src a b md x xs y ys _ _ _ _ hx hy
      exact ⟨hx.1.append hy.1,hx.2.append hy.2⟩)
    (by exact ⟨rfl,fun _ h => by cases h⟩)
    (by
      intro md a v first args rest tail _ _ hx hy
      exact ⟨hx.1.append hy.1,hx.2.append hy.2⟩)
    walk

def actualCapture (seen : List Occurrence) (base : Nat → Mode → Nat)
    (lo hi : Nat → Nat) (binder : Nat) : Capture :=
  ⟨lo binder,choose seen base binder .actual,hi binder⟩

theorem actual_links {s : State} {seen : List Occurrence}
    (allActual : Modes used .actual) (subset : used ⊆ seen)
    (shared : ∀ first ∈ seen, ∀ second ∈ seen, first.binder = second.binder →
      first.mode = .actual → second.mode = .actual → Alias s first.argument second.argument) :
    Links s (actualCapture seen base lo hi) used := by
  intro o present
  have mode : o.mode = .actual := ((allActual o present).elim id id)
  have representative := used_mode (fallback := base) (subset present)
  have same := shared o (subset present) _ representative rfl mode mode
  simp only [mode,byMode,actualCapture] at same ⊢
  exact same

theorem trace_actual_chosen {s : State} {seen : List Occurrence}
    (trace : Trace s .actual root expr used) (subset : used ⊆ seen)
    (shared : ∀ first ∈ seen, ∀ second ∈ seen, first.binder = second.binder →
      first.mode = .actual → second.mode = .actual → Alias s first.argument second.argument) :
    GeneralDeclarativeEntailment320.Entails s
      ⟨root,GeneralDeclarativeSubstitution320.logical (actualCapture seen base lo hi) .actual expr⟩ :=
  GeneralDeclarativeTrace321.trace_equation trace (actual_links (trace_keys_modes trace).2 subset shared)

end Yulang.GeneralDeclarativeTraceNames321
