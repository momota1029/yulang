import Yulang.GeneralDepthTwoOnlyFirst300
import Yulang.GeneralDepthTwoOnlySecond300
import Yulang.GeneralDepthTwoCertifiedRead300

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 35000
set_option maxHeartbeats 15000000
namespace Yulang.GeneralDepthTwoMachine300
open GeneralGeneratedNestedSource299 (initial root)
open GeneralDepthTwoFirstInstall300 (after)
open GeneralDepthTwoSecondInstall300 (final)
open GeneralDepthTwoFinalHalt300 (source_halted)
open GeneralNominalExamples (registry)
open GeneralDeclarationExamples (roles)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedJournal232 (State)
open B4Target (Steps)

inductive Phase where | source | middle | done
  deriving DecidableEq, Repr

def raw : Phase → State roles
  | .source => initial
  | .middle => after
  | .done => final

def next : Phase → Option Phase
  | .source => some .middle
  | .middle => some .done
  | .done => none

def remaining : Phase → Nat
  | .source => 2
  | .middle => 1
  | .done => 0

theorem distinct (a b : Phase) (same : raw a = raw b) : a = b := by
  obtain ⟨first,second,whole⟩ := GeneralDepthTwoPhaseCut300.different_phases
  cases a <;> cases b <;> first
    | rfl
    | exact False.elim (first same)
    | exact False.elim (second same)
    | exact False.elim (whole same)
    | exact False.elim (first same.symm)
    | exact False.elim (second same.symm)
    | exact False.elim (whole same.symm)

theorem exact_step (a b : Phase) :
    (boundary roles).Step registry root (raw a) (raw b) ↔ next a = some b := by
  cases a
  · constructor
    · intro h
      have eq := (GeneralDepthTwoOnlyFirst300.exact_first (raw b)).mp h
      have pair : b = .middle := distinct b .middle eq
      cases pair
      rfl
    · intro h
      have eq : Phase.middle = b := Option.some.inj h
      cases eq
      exact GeneralDepthTwoFirstInstall300.actual
  · constructor
    · intro h
      have eq := (GeneralDepthTwoOnlySecond300.exact_second (raw b)).mp h
      have pair : b = .done := distinct b .done eq
      cases pair
      rfl
    · intro h
      have eq : Phase.done = b := Option.some.inj h
      cases eq
      exact GeneralDepthTwoSecondInstall300.actual
  · constructor
    · intro h
      exact False.elim (source_halted _ h)
    · intro h
      cases h

theorem generate_next (a : Phase) (s : State roles)
    (step : (boundary roles).Step registry root (raw a) s) :
    ∃ b, next a = some b ∧ raw b = s := by
  cases a
  · exact ⟨.middle,rfl,((GeneralDepthTwoOnlyFirst300.exact_first s).mp step).symm⟩
  · exact ⟨.done,rfl,((GeneralDepthTwoOnlySecond300.exact_second s).mp step).symm⟩
  · exact False.elim (source_halted _ step)

theorem phases_complete (s : State roles) (path : Steps ((boundary roles).Step registry root) initial s) :
    ∃ p, raw p = s := by
  induction path with
  | refl => exact ⟨.source,rfl⟩
  | tail _ step ih =>
    obtain ⟨a,e⟩ := ih
    obtain ⟨b,_,e'⟩ := generate_next a _ (e.symm ▸ step)
    exact ⟨b,e'⟩

theorem remaining_decreases (a b : Phase) (step : (boundary roles).Step registry root (raw a) (raw b)) :
    remaining b < remaining a := by
  have next' := (exact_step a b).mp step
  cases a <;> cases b <;> first | decide | cases next'

theorem source_accessible :
    Acc (fun next prev => (boundary roles).Step registry root prev next) initial := by
  constructor
  intro s step
  cases (GeneralDepthTwoOnlyFirst300.exact_first _).mp step
  constructor
  intro s done
  cases (GeneralDepthTwoOnlySecond300.exact_second _).mp done
  exact Acc.intro _ (fun x forbidden => False.elim (source_halted x forbidden))

end Yulang.GeneralDepthTwoMachine300
