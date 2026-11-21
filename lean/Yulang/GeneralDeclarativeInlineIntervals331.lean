import Yulang.GeneralDeclarativeInlineMaterial331

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeInlineIntervals331
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeOpaqueNominal328 (point point_bounded)
open GeneralDeclarativeTermWalk322 (Occurrence)
open GeneralDeclarativeInlineAllocation331 (captures)
open GeneralDeclarativeInlineMaterial331 (read seed ordinary)
open GeneralDeclarativeInlineTrace331 (Read)
open GeneralDeclarativeStableReads329 (One)
open GeneralDeclarativeGrowth327 (Extends fits)
open GeneralDeclarativeOpaqueConserve328 (Retains)
open GeneralDeclarativeOpaqueNested328 (occurrences)
open GeneralDeclarativeRecordPoints330 (fieldName stepName)
open GeneralDeclarationPatterns (normalize)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)

def choose (existing : Nat → Capture) (raw : Expr) (fresh : Nat) : Capture :=
  match raw with
  | .variable n => existing n
  | _ => point fresh

def captureWith (existing : Nat → Capture) (start : Nat) : List Occurrence → List (Nat × Capture)
  | [] => []
  | o::os => (o.binder,choose existing o.term start) :: captureWith existing (stepName o.term start) os

def Existing (s : State) (located : Nat → Capture) (uses : List Occurrence) : Prop :=
  ∀ atSite ∈ uses, ∀ n, atSite.term = .variable n →
    (located n).center = n ∧ Bounds s (located n)

theorem carries_ranges {s t : State} (grown : Extends s t) (old : Existing s existing uses) :
    Existing t existing uses := by
  intro atSite used n isName
  obtain ⟨center,bounds⟩ := old atSite used n isName
  exact ⟨center,fits grown bounds⟩

theorem fixed_centers {s : State} {existing : Nat → Capture} {uses : List Occurrence}
    (preserved : Existing s existing uses) (start : Nat) :
    occurrences (captureWith existing start uses) = occurrences (captures start uses) := by
  induction uses generalizing start with
  | nil => rfl
  | cons u us ih =>
    have before : (choose existing u.term start).center = fieldName u.term start := by
      cases eq : u.term <;> try rfl
      case «variable» n => exact (preserved u List.mem_cons_self n eq).1
    have tail : Existing s existing us :=
      fun _ member n eq => preserved _ (List.mem_cons_of_mem _ member) n eq
    change (⟨u.binder,.actual,.variable (choose existing u.term start).center⟩ : Occurrence) ::
      occurrences (captureWith existing (stepName u.term start) us) =
      ⟨u.binder,.actual,.variable (fieldName u.term start)⟩ ::
      occurrences (captures (stepName u.term start) us)
    rw [before,ih tail]

theorem kept_ranges {s t : State} (grown : Extends s t) {existing : Nat → Capture}
    {uses : List Occurrence} (preserved : Existing s existing uses) (start : Nat) :
    ∀ span ∈ captureWith existing start uses, Bounds t span.2 := by
  induction uses generalizing start with
  | nil => intro _ impossible; cases impossible
  | cons u us ih =>
    intro span h
    rcases List.mem_cons.mp h with rfl|member
    · cases eq : u.term <;> try exact point_bounded _ _
      case «variable» n => exact fits grown (preserved u List.mem_cons_self n eq).2
    · exact ih (fun _ later n eq => preserved _ (List.mem_cons_of_mem _ later) n eq)
        _ _ member

/-- Inline composite variables are only allocated where necessary.
For a real old occurrence whose interval is already known, the
entire existing lower/centre/upper triple survives, not a new
point or an endpoint used as its actual centre. -/
theorem read_with_ranges {s : State} {p : Supported s done}
    (box : Bounds s a) (printed : translate c i (normalize pat) = some code)
    (actual : Read (restriction p) .actual (.variable a.center) code uses)
    (known : Existing s existing uses) (targets : List Nat) :
    ∃ t, Retains s t targets ∧
      One t c i a pat (captureWith existing (seed s a targets uses) uses) ∧
      (ordinary s a targets uses) ⊆ t.equations ∧
      ∀ span ∈ captureWith existing (seed s a targets uses) uses, Bounds t span.2 := by
  obtain ⟨t,retains,one,rows,_⟩ := read box printed actual targets
  obtain ⟨box,spelling,expanded,decoded,derives,walk⟩ := one
  rw [← fixed_centers known] at walk
  exact ⟨t,retains,⟨box,spelling,expanded,decoded,derives,walk⟩,rows,kept_ranges retains.grows known _⟩

end Yulang.GeneralDeclarativeInlineIntervals331
