import Yulang.GeneralRebaseCertifiedSteps266
import Yulang.GeneralRebaseCertifiedPathCount266
import Yulang.GeneralRebaseEdgeRules266

namespace Yulang.GeneralRebasePathRules266
open GeneralRebaseStep258
open GeneralRebaseCertifiedObserver266 (Edge)
open GeneralRebaseCertifiedPath266 (Path edges)
open GeneralRebaseCertifiedSteps266 (edge_suffix final_write)
open GeneralRebaseLiveProjection264 (SourceState project)
open GeneralRebasePositiveMeaning266 (Saturated)
open GeneralRebaseEdgeRules266 (rules)
open GeneralSourceState (Output)
variable {registry : GeneralDeclarations.Registry} {root : GeneralSourceDictionaries.Occurrence roles}

theorem final_saturated (owners : List Nat) (pool : List Output) (path : Path registry root first last) :
 Saturated (rules owners pool (edges path)) (project owners pool last) := by
 intro rule listed _ _
 obtain ⟨edge,member,fact,produced,rfl⟩ :=
   (GeneralRebaseEdgeRules266.member owners pool (edges path) rule).mp listed
 rw [GeneralRebaseSourceProjection264.steps_square owners pool (edge_suffix path edge member)]
 exact (GeneralRebaseFactSemantics259.present_write _ _ fact).mpr (Or.inl produced)

/-- A supplied spine and a saturation certificate for its final projection
suffice for terminal exactness even if the table contains additional edges. -/
theorem settles_covered (owners : List Nat) (pool : List Output)
 (table : List (Edge registry root)) (path : Path registry root first last)
 (listed : edges path ⊆ table)
 (closedAtTarget : Saturated (rules owners pool table) (project owners pool last)) :
 GeneralRebaseSettle259.settle
  (GeneralRebasePositiveRules266.observe (rules owners pool table)) (project owners pool first) =
 .ok (project owners pool last) := by
 let before := project owners pool first
 let after := project owners pool last
 let program := rules owners pool table
 obtain ⟨endState,success,refined,saturated,least⟩ :=
   GeneralRebasePositiveMeaning266.least_saturated program before
 have exactWrite : write before (present after) = after := final_write owners pool path
 have afterRefines : GeneralRebasePersistentObserver266.Refines before after := by
   change after.remaining.Sublist before.remaining
   rw [←exactWrite]
   exact List.filter_sublist ..
 have lower := least after afterRefines closedAtTarget
 have native := GeneralRebaseCertifiedPathCount266.exact_run owners pool table path listed
 have afterKnown : present after ⊆ present endState :=
   GeneralRebaseEdgeRules266.run_covered owners pool table native endState saturated
     (GeneralRebasePositiveRules266.known_monotone refined)
 have filterEq : endState.remaining.filter (fun fact => !(present after).contains fact) = endState.remaining := by
   apply List.filter_eq_self.mpr
   intro fact pending
   have missing : fact ∉ present after := fun known =>
     ((GeneralRebaseFactSemantics259.present_iff endState fact).mp (afterKnown known)).2 pending
   simpa using missing
 have upper := refined.filter (fun fact => !(present after).contains fact)
 rw [filterEq] at upper
 change endState.remaining.Sublist (write before (present after)).remaining at upper
 rw [exactWrite] at upper
 have same := state_ext endState after (upper.eq_of_length_le lower.length_le)
 exact success.trans (congrArg Except.ok same)

/-- One composable certified spine is terminally exact. This does not
preserve the individual proposals or successful-Step count. -/
theorem settles (owners : List Nat) (pool : List Output) (path : Path registry root first last) :
 GeneralRebaseSettle259.settle
  (GeneralRebasePositiveRules266.observe (rules owners pool (edges path))) (project owners pool first) =
 .ok (project owners pool last) :=
 settles_covered owners pool (edges path) path (fun _ h => h) (final_saturated owners pool path)

theorem same_settlement (owners : List Nat) (pool : List Output) (path : Path registry root first last) :
 GeneralRebaseSettle259.settle
  (GeneralRebasePositiveRules266.observe (rules owners pool (edges path))) (project owners pool first) =
 GeneralRebaseSettle259.settle (GeneralRebaseCertifiedObserver266.observe owners pool (edges path))
   (project owners pool first) :=
 (settles owners pool path).trans (GeneralRebaseCertifiedPathSettle266.settles owners pool path).symm

end Yulang.GeneralRebasePathRules266
