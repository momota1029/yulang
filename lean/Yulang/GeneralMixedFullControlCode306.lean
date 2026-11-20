import Yulang.GeneralMixedControlTrace306
import Yulang.GeneralRebaseDepthSchedule286

namespace Yulang.GeneralMixedFullControlCode306
open GeneralDictionaryOutputDepth252 (roles initial registry root)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralRebaseDepthPathRank285 (ActualPath)
open GeneralRebaseDepthPhase286 (Post Pre Hop InstallHop)
open GeneralMixedControlMask306 (Mask project)
open GeneralMixedControlBisim306 (Observe)

@[ext] structure Code where
  installed : Bool
  scalars : Mask
  deriving DecidableEq, Repr

def code (s : State roles) : Code := ⟨!s.core.erased.current.packets.isEmpty,project s⟩

inductive Event where
  | install
  | scalar (which : Fin 2)
  deriving DecidableEq, Repr

def fire : Event → Code → Code → Bool
  | .install, x, y => !x.installed && y.installed && decide (x.scalars = y.scalars)
  | .scalar q, x, y => decide (x.installed = y.installed) && GeneralMixedControlMask306.fire q x.scalars y.scalars

def moves (x y : Code) : Bool := fire .install x y || GeneralMixedControlMask306.moves x.scalars y.scalars &&
  decide (x.installed = y.installed)

theorem refresh_phase (s : State roles) (c : GeneralNominalCandidates.Context) :
    (code (refresh s c)).installed = (code s).installed := rfl

theorem phase_installs {s t : State roles} (hit : InstallHop s t) : (code t).installed = true := by
  cases hit
  rfl

theorem marker {s : State roles} {n : Nat} (path : ActualPath initial s n) :
    ((code s).installed = true ↔ Post s) ∧ ((code s).installed = false ↔ Pre s) := by
  induction path with
  | empty =>
    have before := GeneralRebaseDepthPhase286.start
    have impossible : ¬ Post initial := GeneralRebaseDepthPhase286.exclusive before
    exact ⟨⟨(fun no => by cases no),fun post => (impossible post).elim⟩,⟨fun _ => before,fun _ => rfl⟩⟩
  | @more s t _ path step ih =>
    have stages := GeneralRebaseDepthPhase286.path_covered (.inl GeneralRebaseDepthPhase286.start) path
    rcases stages with prior|post
    · rcases GeneralRebaseDepthPhase286.pre_partition prior step with hop|hit
      · have stays := GeneralRebaseDepthPhase286.pre_refresh prior hop
        have bit : (code t).installed = false := by cases hop; exact ih.2.mpr prior
        exact ⟨⟨(fun yes => by rw [bit] at yes; cases yes),
          fun post => (GeneralRebaseDepthPhase286.exclusive stays post).elim⟩,⟨fun _ => stays,fun _ => bit⟩⟩
      · have next := GeneralRebaseDepthPhase286.cross prior hit
        have yes := phase_installs hit
        exact ⟨⟨fun _ => next,fun _ => yes⟩,⟨(fun no => by rw [yes] at no; cases no),
          fun pre => (GeneralRebaseDepthPhase286.exclusive pre next).elim⟩⟩
    · have hop := GeneralRebaseDepthPhase286.post_step post step
      have next := GeneralRebaseDepthPhase286.post_refresh post hop
      have yes : (code t).installed = true := by cases hop; exact ih.1.mpr post
      exact ⟨⟨fun _ => next,fun _ => yes⟩,⟨(fun no => by rw [yes] at no; cases no),
        fun pre => (GeneralRebaseDepthPhase286.exclusive pre next).elim⟩⟩

inductive Action : Event → State roles → State roles → Prop
  | install : InstallHop s t → Action .install s t
  | scalar : Observe q s t → Action (.scalar q) s t

theorem action_step {event : Event} {s t : State roles} (taken : Action event s t) : Step registry root s t := by
  cases taken with
  | install h => exact GeneralRebaseDepthPhase286.as_step h
  | scalar h =>
    cases h with
    | refresh ctx cert present before after =>
      exact ⟨root,.root,.refresh root ctx cert _ present before after⟩

end Yulang.GeneralMixedFullControlCode306
