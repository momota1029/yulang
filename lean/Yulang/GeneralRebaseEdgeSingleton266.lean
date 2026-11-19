import Yulang.GeneralRebaseEdgeRules266
import Yulang.GeneralRebaseCertifiedFixture266

namespace Yulang.GeneralRebaseEdgeSingleton266
open GeneralRebaseStep258
open GeneralRebaseCompression266 (Basis)
open GeneralRebaseCertifiedObserver266 (Edge)
open GeneralRebaseLiveProjection264 (project)
open GeneralRebasePositiveMeaning266 (Saturated)
open GeneralSourceState (Output)

variable {registry : GeneralDeclarations.Registry} {root : GeneralSourceDictionaries.Occurrence roles}

/-- On a singleton the Horn envelope settles to exactly the projected
destination, although one original write may become multiple rule writes.
No singleton completeness beyond the supplied source edge is asserted. -/
theorem exact_singleton (owners : List Nat) (pool : List Output) (edge : Edge registry root) :
 GeneralRebaseSettle259.settle
  (GeneralRebasePositiveRules266.observe (GeneralRebaseEdgeRules266.rules owners pool [edge]))
  (project owners pool edge.before) = .ok (project owners pool edge.after) := by
 let first := project owners pool edge.before
 let last := project owners pool edge.after
 let rules := GeneralRebaseEdgeRules266.rules owners pool [edge]
 obtain ⟨final,success,refined,saturated,least⟩ :=
   GeneralRebasePositiveMeaning266.least_saturated rules first
 have exactWrite : write first (present last) = last :=
   GeneralRebaseProjectionObserver266.witness_write owners pool
     (⟨edge.before,edge.after,edge.actual,rfl,rfl⟩ :
      GeneralRebaseProjectionObserver266.Witness owners pool registry root first last)
 have lastRefines : GeneralRebasePersistentObserver266.Refines first last := by
   change last.remaining.Sublist first.remaining
   rw [←exactWrite]
   exact List.filter_sublist ..
 have lastSaturated : Saturated rules last := by
   intro rule inRules _ _
   obtain ⟨candidate,listed,fact,located,rfl⟩ :=
     (GeneralRebaseEdgeRules266.member owners pool [edge] rule).mp inRules
   cases List.mem_singleton.mp listed
   exact located
 have lower := least last lastRefines lastSaturated
 have lastKnown : present last ⊆ present final :=
   GeneralRebaseEdgeRules266.follows owners pool [edge] final saturated edge
     (List.mem_singleton_self _) (fun f knows =>
       GeneralRebasePositiveRules266.known_monotone refined f knows)
 have filterEq : final.remaining.filter (fun fact => !(present last).contains fact) = final.remaining := by
   apply List.filter_eq_self.mpr
   intro fact pending
   have missing : fact ∉ present last := by
     intro known
     exact ((GeneralRebaseFactSemantics259.present_iff final fact).mp (lastKnown known)).2 pending
   simpa using missing
 have upper := refined.filter (fun fact => !(present last).contains fact)
 rw [filterEq] at upper
 change final.remaining.Sublist (write first (present last)).remaining at upper
 rw [exactWrite] at upper
 have equal := state_ext final last (upper.eq_of_length_le lower.length_le)
 exact success.trans (congrArg Except.ok equal)

theorem actual_compound :
 GeneralRebaseSettle259.settle
  (GeneralRebasePositiveRules266.observe
    (GeneralRebaseEdgeRules266.rules GeneralRebaseSourceStrictFixture265.owners
      GeneralRebaseSourceStrictFixture265.pool [GeneralRebaseCertifiedFixture266.realEdge]))
  GeneralRebaseSourceStrictFixture265.first = .ok GeneralRebaseSourceStrictFixture265.last :=
 exact_singleton _ _ _

end Yulang.GeneralRebaseEdgeSingleton266
