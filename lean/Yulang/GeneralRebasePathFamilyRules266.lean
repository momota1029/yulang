import Yulang.GeneralRebasePathFamily266

namespace Yulang.GeneralRebasePathFamilyRules266
open GeneralRebaseStep258
open GeneralRebaseCertifiedPath266 (Path edges)
open GeneralRebaseLiveProjection264 (project)
open GeneralRebasePathFamily266 (table from_path edge_path)
open GeneralRebaseEdgeRules266 (rules)
open GeneralRebasePositiveMeaning266 (Saturated)
open GeneralSourceState (Output)
variable {registry : GeneralDeclarations.Registry} {root : GeneralSourceDictionaries.Occurrence roles}

theorem final_saturated (owners : List Nat) (pool : List Output)
 (paths : List (Path registry root first last)) :
 Saturated (rules owners pool (table paths)) (project owners pool last) := by
 intro rule listed _ _
 obtain ⟨edge,member,fact,produced,rfl⟩ :=
   (GeneralRebaseEdgeRules266.member owners pool (table paths) rule).mp listed
 obtain ⟨path,_,onPath⟩ := edge_path paths edge member
 rw [GeneralRebaseSourceProjection264.steps_square owners pool
      (GeneralRebaseCertifiedSteps266.edge_suffix path edge onPath)]
 exact (GeneralRebaseFactSemantics259.present_write _ _ fact).mpr (Or.inl produced)

theorem settles (owners : List Nat) (pool : List Output)
 (paths : List (Path registry root first last)) (nonempty : ∃ path, path ∈ paths) :
 GeneralRebaseSettle259.settle (GeneralRebasePositiveRules266.observe (rules owners pool (table paths)))
   (project owners pool first) = .ok (project owners pool last) := by
 obtain ⟨path,listed⟩ := nonempty
 exact GeneralRebasePathRules266.settles_covered owners pool (table paths) path
   (from_path paths path listed) (final_saturated owners pool paths)

theorem same_settlement (owners : List Nat) (pool : List Output)
 (paths : List (Path registry root first last)) (nonempty : ∃ path, path ∈ paths) :
 GeneralRebaseSettle259.settle (GeneralRebasePositiveRules266.observe (rules owners pool (table paths)))
   (project owners pool first) =
 GeneralRebaseSettle259.settle (GeneralRebaseCertifiedObserver266.observe owners pool (table paths))
   (project owners pool first) :=
 (settles owners pool paths nonempty).trans (GeneralRebasePathFamily266.settles owners pool paths nonempty).symm

end Yulang.GeneralRebasePathFamilyRules266
