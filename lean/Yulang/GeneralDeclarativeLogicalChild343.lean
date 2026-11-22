import Yulang.GeneralDeclarativeInitialRoot343

set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 16000
set_option maxHeartbeats 600000
namespace Yulang.GeneralDeclarativeLogicalChild343
open GeneralDeclarationPatterns (normalize)
open GeneralNominalCenteredHeadMatExpressions (Expr translateMany)
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeVersionedRootGuard342 (observedRoot actualDemand original_targets)
open GeneralDeclarativeVersionedRootShape342 (spans typePoint)
open GeneralDeclarativeVersionedReceipt342 (ownerOutput)
open GeneralDeclarativeVersionedChildView342 (code)
open GeneralDictionaryJournalRefinement228Source (interpretation)
open GeneralWhereOriginSingleSource318 (declaration sourceRegistry)
open GeneralLiveCompoundRegistry316 (otherChild)
open GeneralWhereOriginSupport318 (journalSources)
open GeneralWherePhysicalCommit319 (final)
open GeneralDeclarativeStableAssemble329 (merged)
open GeneralDeclarativeClauseBatch327 (prepare)
open GeneralDeclarativeFreshInputs325 (prepared)
open GeneralDeclarativeNestedBody332 (compileBody)
open GeneralDeclarativeFootprint321 (stateNames)
open GeneralDeclarativeFreshWhere325 (seed)
open GeneralDeclarativeEntailment320 (appendFacts)

abbrev value : Expr := .variant 0 (.variable 0)
abbrev fallback (_ : Nat) : Capture := typePoint
abbrev targets (_ : GeneralDeclarations.Clause) (_ : Nat) : Nat := 4
def stage (keep : List Nat) := (merged observedRoot keep spans fallback).state
def capture (keep : List Nat) := (merged observedRoot keep spans fallback).captures
def protect (keep : List Nat) := stateNames (stage keep) ++ keep
abbrev jobs := GeneralDeclarativeSparseWhere325.plan otherChild.arguments [value]
def fresh (keep : List Nat) := seed (stage keep) (protect keep) (capture keep) jobs
def arg (keep : List Nat) : Capture := ⟨fresh keep,fresh keep + 1,fresh keep + 2⟩
def child (keep : List Nat) : Demand := ⟨1,[arg keep],[]⟩
def built (keep : List Nat) := prepared (stage keep) (protect keep) (capture keep) jobs
def output (keep : List Nat) := appendFacts (built keep) [ownerOutput]

theorem center (keep : List Nat) : (capture keep 0).center = 2 ∧ (capture keep 1).center = 2 := ⟨rfl,rfl⟩

theorem translated : translateMany sourceRegistry.constructors interpretation
    (otherChild.arguments.map normalize) = some [value] := rfl

theorem jobs_eq : jobs = [some value] := rfl

def port (keep : List Nat) : GeneralDeclarativeClauseBatch327.Port :=
  GeneralDeclarativeClauseBatch327.make (stage keep) (protect keep) (capture keep) otherChild [value]

private theorem at_first (start : Nat) (js : List (Option Expr)) (h : js = [some value]) :
    GeneralDeclarativeSparseWhere325.atPosition start js 0 = ⟨start,start+1,start+2⟩ := by
  subst js
  rfl

theorem port_zero (keep : List Nat) : (port keep).input 0 = arg keep := by
  unfold port arg
  exact at_first (fresh keep) jobs jobs_eq

private theorem singleton_batch (c : GeneralDeclarationPatterns.Constructors)
    (i : GeneralNominalInspection.Interpretation) (p : List Nat) (cap : Nat → Capture)
    (s : State) (q : GeneralDeclarations.Clause) (codes : List Expr)
    (printed : translateMany c i (q.arguments.map normalize) = some codes) :
    prepare c i p cap s [q] =
      some (prepared s p cap (GeneralDeclarativeSparseWhere325.plan q.arguments codes),
        [GeneralDeclarativeClauseBatch327.make s p cap q codes]) := by
  simp only [prepare,printed]
  rfl

theorem batch (keep : List Nat) :
    prepare sourceRegistry.constructors interpretation (protect keep) (capture keep) (stage keep)
      declaration.requirements = some (built keep,[port keep]) := by
  rw [show declaration.requirements = [otherChild] from rfl]
  unfold built port
  exact singleton_batch sourceRegistry.constructors interpretation (protect keep) (capture keep) (stage keep)
    otherChild [value] translated

end Yulang.GeneralDeclarativeLogicalChild343
