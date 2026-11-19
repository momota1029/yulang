import Yulang.GeneralRebaseSourceProjection264
import Yulang.GeneralRebaseCheckedWrite259

namespace Yulang.GeneralRebaseCheckedProjection266
open GeneralRebaseStep258
open GeneralRebaseCheckedWrite259 (commit)
open GeneralRebaseLiveProjection264 (SourceState project liveFacts)
open GeneralSourceState (Output)

theorem checked_square {basis : List Fact} (before after : State basis) (proposal : Proposal)
 (square : after = write before proposal) (closed : proposal ⊆ basis) :
 commit before proposal = .ok (if after.remaining = before.remaining then none else some after) := by
 rw [GeneralRebaseCheckedWrite259.supported _ _ closed]
 unfold tryWrite
 rw [←square]

theorem checked_projection (owners : List Nat) (pool : List Output)
 {registry : GeneralDeclarations.Registry} {root : GeneralSourceDictionaries.Occurrence roles}
 {before after : SourceState roles}
 (step : GeneralNominalVersionedMixedKernel234.Step registry root before after)
 (closed : liveFacts after ⊆ GeneralRebaseUniversalBasis263.basis owners pool) :
 commit (project owners pool before) (liveFacts after) =
   .ok (if (project owners pool after).remaining = (project owners pool before).remaining then
     none else some (project owners pool after))  :=
 checked_square _ _ _
   (GeneralRebaseSourceProjection264.step_square owners pool step) closed

/-- A single fixed source-derived basis suffices for all actual reachable
one-step rescans, including the ones that return no finite state change. -/
theorem checked_source (registry : GeneralDeclarations.Registry)
 (root : GeneralSourceDictionaries.Occurrence roles) (start : SourceState roles)
 (initial : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Initial registry root start) :
 ∃ owners : List Nat, ∃ pool : List Output, ∀ before after,
  B4Target.Steps ((GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Step registry root) start before →
  (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Step registry root before after →
  commit (project owners pool before) (liveFacts after) =
   .ok (if (project owners pool after).remaining = (project owners pool before).remaining then
     none else some (project owners pool after)) := by
 obtain ⟨owners,pool,coverage⟩ := GeneralRebaseLiveProjection264.source_covered registry root start initial
 refine ⟨owners,pool,fun before after path step => ?_⟩
 exact checked_projection owners pool step (coverage after (.tail path step))

theorem no_write_iff (owners : List Nat) (pool : List Output)
 {registry : GeneralDeclarations.Registry} {root : GeneralSourceDictionaries.Occurrence roles}
 {before after : SourceState roles}
 (step : GeneralNominalVersionedMixedKernel234.Step registry root before after)
 (closed : liveFacts after ⊆ GeneralRebaseUniversalBasis263.basis owners pool) :
 commit (project owners pool before) (liveFacts after) = .ok none ↔
 project owners pool after = project owners pool before := by
 rw [checked_projection owners pool step closed]
 by_cases equal : (project owners pool after).remaining = (project owners pool before).remaining
 · simp [state_ext _ _ equal]
 · have different : project owners pool after ≠ project owners pool before :=
     fun same => equal (congrArg State.remaining same)
   simp [equal,different]

end Yulang.GeneralRebaseCheckedProjection266
