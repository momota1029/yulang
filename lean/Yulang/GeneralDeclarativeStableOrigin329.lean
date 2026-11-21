import Yulang.GeneralDeclarativeStableTies329
import Yulang.GeneralDeclarativeOutputOrigins323
import Yulang.GeneralDeclarativeOpaqueAuthority328

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeStableOrigin329
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeStableTies329 (Use rows row)
open GeneralDeclarativeEntailment320 (appendFacts)
open GeneralDeclarativeOrigins321 (Supported Backed restriction backed_iff)
open GeneralDeclarativeLowerKnown321 (Ready)
open GeneralDeclarativeGraphRows321 (observed shapeOf)
open GeneralDeclarativeK2Graph321 (Shape)
open GeneralDeclarativeEndpointProbe321 (HeadMatches)

/-- Reusing independent provenance is exact: this operation adds
ordinary ties, not an assertion that any output just completed or a
new origin for its defining equation. A separately proved source
origin can be carried by a separately supplied support view. -/
def retain {s : State} (p : Supported s done) (extra : List Equation) :
    Supported (appendFacts s extra) done :=
  ⟨p.derivesFrom,fun h => List.mem_append_left _ (p.ordinary h)⟩

theorem support_same {s : State} (p : Supported s done) (extra : List Equation) (written : Equation) :
    written ∈ (restriction (retain p extra)).equations ↔ written ∈ (restriction p).equations := by
  rw [backed_iff,backed_iff]
  rfl

theorem readiness {s : State} (p : Supported s done) (extra : List Equation) :
    Ready (retain p extra) d ↔ Ready p d := by
  have port {a b : State} (normal : a.normal = b.normal) (rows : a.equations ⊆ b.equations) :
      (∀ arg ∈ d.arguments, ∃ label, GeneralDeclarativeLowerKnown321.Knows a arg.lower label) →
      ∀ arg ∈ d.arguments, ∃ label, GeneralDeclarativeLowerKnown321.Knows b arg.lower label := by
    intro holds arg h
    obtain ⟨w,v⟩ := holds arg h
    exact ⟨w,GeneralDeclarativeLowerKnown321.knows_mono normal rows v⟩
  exact ⟨port rfl (fun e h => (support_same p extra e).mp h),
    port rfl (fun e h => (support_same p extra e).mpr h)⟩

theorem candidate {s : State} (p : Supported s done) (extra : List Equation) :
    HeadMatches (restriction (retain p extra)) c i d impl ↔ HeadMatches (restriction p) c i d impl :=
  ⟨GeneralDeclarativeOutputOrigins323.head_mono rfl (fun {e} h => (support_same p extra e).mp h),
    GeneralDeclarativeOutputOrigins323.head_mono rfl (fun {e} h => (support_same p extra e).mpr h)⟩

theorem rows_are_aliases (selected : Nat → GeneralDeclarativeWhere319.Capture) (uses : List Use)
    {e : Equation} (appears : e ∈ rows selected uses) : ∃ r, e.right = .variable r := by
  obtain ⟨u,_,rfl⟩ := List.mem_map.mp appears
  exact ⟨_,rfl⟩

theorem same_direct_heads {s : State} (selected : Nat → GeneralDeclarativeWhere319.Capture) (uses : List Use)
    (n : Nat) (shape : Shape) :
    observed (appendFacts s (rows selected uses)) n shape ↔ observed s n shape := by
  constructor
  · rintro ⟨e,stored,shape⟩
    rcases List.mem_append.mp stored with source|new
    · exact ⟨e,source,shape⟩
    · obtain ⟨j,same⟩ := rows_are_aliases selected uses new
      change e = .variable j at same
      rw [same] at shape
      cases shape
  · rintro ⟨e,found,shape⟩
    exact ⟨e,List.mem_append_left _ found,shape⟩

end Yulang.GeneralDeclarativeStableOrigin329
