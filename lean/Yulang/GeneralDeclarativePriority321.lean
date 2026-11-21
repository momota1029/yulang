import Yulang.GeneralDeclarativeInspect321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativePriority321
open GeneralDeclarations (Declaration Registry)
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativeLowerKnown321 (Ready Delayed ready_iff_not_delayed)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeGraphRows321 (observed)
open GeneralDeclarativeInspect321 (PatternK2)
open GeneralNominalCenteredHeadMatExpressions (translate)
open GeneralNominalInspection (Interpretation)
open CommonRoleOutermostResolver (Frontier All₂)

def Visible (r : Registry) (d : Demand) (impl : Declaration) : Prop :=
  impl ∈ r.declarations ∧ impl.role = d.role

/-- Two independent judgments still have to come from actual source
interval propagation, not from an implementation selection function. -/
structure Candidates where
  viable : Demand → Declaration → Prop
  unresolved : Demand → Declaration → Prop

def Survives (r : Registry) (tests : Candidates) (d : Demand) (impl : Declaration) : Prop :=
  Visible r d impl ∧ tests.viable d impl

def Blocked (r : Registry) (tests : Candidates) (d : Demand) : Prop :=
  ∃ impl, Visible r d impl ∧ tests.unresolved d impl

def RootRecurs (s : State) (d : Demand) : Prop :=
  ∃ arg ∈ d.arguments, AliasCycle s (observed s) arg.lower

def CandidateRecurs (s : State) (r : Registry) (interp : Interpretation)
    (tests : Candidates) (d : Demand) : Prop :=
  ∃ impl, Survives r tests d impl ∧ ∃ (i : Nat) (arg : GeneralDeclarativeWhere319.Capture) (pat : GeneralDeclarationPatterns.Pattern) (code : GeneralNominalCenteredHeadMatExpressions.Expr),
    d.arguments[i]? = some arg ∧ impl.head[i]? = some pat ∧
    translate r.constructors interp (GeneralDeclarationPatterns.normalize pat) = some code ∧ PatternK2 s arg.lower code

def Recurs (s : State) (r : Registry) (interp : Interpretation) (tests : Candidates)
    (d : Demand) : Prop :=
  RootRecurs s d ∨ CandidateRecurs s r interp tests d

/-- This is only priority over independently supplied propagation and
child-generation judgments on the supported normalized view fragment. To
instantiate source-wide classification the lower, structural and candidate
views must first be proved exact; a missing fragment witness is not a
new language rejection or delay. Neither argument may call the compiler or
decide which dictionary the recursive classifier produced. -/
inductive Local (s : State) (r : Registry) (interp : Interpretation)
    (p : Supported s completed) (tests : Candidates)
    (generates : Demand → Declaration → List Demand → Prop) : Demand → Frontier Demand → Prop where
  | unsupported : Delayed p d → ¬Recurs s r interp tests d → Local s r interp p tests generates d .pending
  | recursive : Ready p d → Recurs s r interp tests d → Local s r interp p tests generates d .rejected
  | unresolved : Ready p d → ¬Recurs s r interp tests d → Blocked r tests d →
      Local s r interp p tests generates d .pending
  | noCandidate : Ready p d → ¬Recurs s r interp tests d → ¬Blocked r tests d →
      (∀ impl, ¬Survives r tests d impl) → Local s r interp p tests generates d .rejected
  | ambiguous : Ready p d → ¬Recurs s r interp tests d → ¬Blocked r tests d →
      Survives r tests d first → Survives r tests d second → first.id ≠ second.id →
      Local s r interp p tests generates d .ambiguous
  | selected : Ready p d → ¬Recurs s r interp tests d → ¬Blocked r tests d →
      Survives r tests d impl → (∀ other, Survives r tests d other → other.id = impl.id) →
      generates d impl children → Local s r interp p tests generates d (.selected impl.id children)

variable {s : State} {r : Registry} {interp : Interpretation} {completed : Nat → Prop}
    {p : Supported s completed} {tests : Candidates} {generates : Demand → Declaration → List Demand → Prop}

theorem delayed_pending_only (delayed : Delayed p d) (outcome : Local s r interp p tests generates d result) :
    result = .pending := by
  have notReady : ¬Ready p d := fun ready => (ready_iff_not_delayed p d).mp ready delayed
  cases outcome with
  | unsupported => rfl
  | recursive ready _ => exact False.elim (notReady ready)
  | unresolved => rfl
  | noCandidate ready _ _ _ => exact False.elim (notReady ready)
  | ambiguous ready _ _ _ _ _ => exact False.elim (notReady ready)
  | selected ready _ _ _ _ _ => exact False.elim (notReady ready)

theorem recursive_over_viable (ready : Ready p d) (recursive : Recurs s r interp tests d)
    (outcome : Local s r interp p tests generates d result) :
    result = .rejected := by
  cases outcome with
  | unsupported delayed _ => exact False.elim ((ready_iff_not_delayed p d).mp ready delayed)
  | recursive => rfl
  | unresolved _ safe _ => exact False.elim (safe recursive)
  | noCandidate => rfl
  | ambiguous _ safe _ _ _ _ => exact False.elim (safe recursive)
  | selected _ safe _ _ _ _ => exact False.elim (safe recursive)

/-- Do not use the fragment to decide the diagnostic priority if ordinary
recurrence is known at the same time expansion lacks authorized support. -/
theorem overlap_outside_fragment (delayed : Delayed p d) (recursive : Recurs s r interp tests d) :
    ¬Local s r interp p tests generates d result := by
  intro outcome
  have notReady : ¬Ready p d := fun ready => (ready_iff_not_delayed p d).mp ready delayed
  cases outcome with
  | unsupported _ safe => exact safe recursive
  | recursive ready _ => exact notReady ready
  | unresolved ready _ _ => exact notReady ready
  | noCandidate ready _ _ _ => exact notReady ready
  | ambiguous ready _ _ _ _ _ => exact notReady ready
  | selected ready _ _ _ _ _ => exact notReady ready

theorem selected_generated (outcome : Local s r interp p tests generates d (.selected key kids)) :
    ∃ impl, impl.id = key ∧ Survives r tests d impl ∧ generates d impl kids := by
  cases outcome with
  | selected _ _ _ surviving _ built => exact ⟨_,rfl,surviving,built⟩

end Yulang.GeneralDeclarativePriority321
