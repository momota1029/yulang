import Yulang.Effects

/-!
# Local positive checks and negative permissions

Current spec/05-effects.md §5.5 and traps.md T3 check the concrete effects visible
at an annotation, while allowing an opaque tail. This module characterizes that
local check. A later refinement does not trigger a new check (spec T3, 2026-11-05).

The final impossibility theorem explains why a purely extensional checker cannot
simultaneously accept every unknown row, reject a forbidden concrete effect, and
be invariant under arbitrary substitution. A source implementation must retain
the observation boundary: spec T3 (decided 2026-11-05) checks only what is
visible at the annotation, and later concretization of a generalized row
variable is substitution into a scheme, not a recheck.
-/

namespace Yulang.Annotations

open Yulang.Effects

/-- What is concrete and visible at this one annotation boundary. -/
structure Snapshot (Variable : Type) (Key : Type) where
  concrete : Row Key
  tails : List Variable

/-- Positive annotations do not demand that any allowed effect actually occur. -/
def Admissible (permission : Permission Key) (snapshot : Snapshot Variable Key) : Prop :=
  ∀ occurrence ∈ snapshot.concrete,
    occurrence.barriers = [] → permission occurrence.key = true

def check (permission : Permission Key) (snapshot : Snapshot Variable Key) : Bool :=
  snapshot.concrete.all (fun occurrence =>
    !occurrence.barriers.isEmpty || permission occurrence.key)

theorem check_iff (permission : Permission Key) (snapshot : Snapshot Variable Key) :
    check permission snapshot = true ↔ Admissible permission snapshot := by
  unfold check Admissible
  simp only [List.all_eq_true]
  constructor
  · intro h occurrence hin hempty
    have result := h occurrence hin
    simpa [hempty] using result
  · intro h occurrence hin
    cases hb : occurrence.barriers with
    | nil => simpa using h occurrence hin hb
    | cons barrier rest => simp

/-- Unknown tails are allowed locally, without equating the tail with the whitelist. -/
theorem opaque_tail_allowed (permission : Permission Key) (variables : List Variable) :
    check permission (⟨[], variables⟩ : Snapshot Variable Key) = true := rfl

/-- Changing an opaque tail alone cannot alter this observation snapshot's result. -/
theorem opaque_tail_irrelevant (permission : Permission Key) (row : Row Key)
    (first second : List Variable) :
    check permission (⟨row, first⟩ : Snapshot Variable Key) =
      check permission (⟨row, second⟩ : Snapshot Variable Key) := rfl

theorem visible_forbidden_rejected (permission : Permission Key) (key : Key)
    (denied : permission key = false) (variables : List Variable) :
    check permission (⟨[{key := key}], variables⟩ : Snapshot Variable Key) = false := by
  simp [check, denied]

theorem protected_concrete_allowed (permission : Permission Key) (scope : Nat)
    (row : Row Key) (variables : List Variable) :
    check permission (⟨protect scope allowNone row, variables⟩ : Snapshot Variable Key) = true := by
  apply (check_iff _ _).mpr
  intro occurrence hin empty
  obtain ⟨original, _, rfl⟩ := List.mem_map.mp hin
  simp [protectOccurrence, allowNone] at empty

/-- The negative permission operation preserves family identities and does not
insert an allowed effect into a computation that never had it. -/
theorem negative_permission_does_not_inject (scope : Nat) (permission : Permission Key)
    (row : Row Key) :
    (protect scope permission row).map Occurrence.key = row.map Occurrence.key := by
  simp [protect, List.map_map, Function.comp_def]

/-- These three requirements cannot hold for a checker on row expressions alone.
The quantifiers are unrestricted: substitution may fill an unknown with a
forbidden visible head. No later-refinement policy is assumed here. -/
theorem no_substitution_invariant_extensional_check
    (accepts : RowExpr Nat Key → Prop) (forbidden : Key)
    (unknown : accepts (.var 0))
    (rejects : ¬ accepts (.head forbidden))
    (stable : ∀ (row : RowExpr Nat Key) (substitution : Nat → RowExpr Nat Key),
      accepts row → accepts (row.subst substitution)) : False := by
  exact rejects (stable (.var 0) (fun _ => .head forbidden) unknown)

example : check (fun key : Nat => key == 0)
    (⟨[], [0]⟩ : Snapshot Nat Nat) = true := by decide

example : check (fun key : Nat => key == 0)
    (⟨[{key := 1}], []⟩ : Snapshot Nat Nat) = false := by decide

end Yulang.Annotations
