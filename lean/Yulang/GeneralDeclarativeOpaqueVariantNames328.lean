import Yulang.GeneralDeclarativeOpaqueVariant328
import Yulang.GeneralDeclarativeOpaqueTrace328

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeOpaqueVariantNames328
open GeneralDeclarativeHead320 (State Equation Models environment)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Bounds bounds_sound)
open GeneralDeclarativeOpaqueNames328 (kept first extend unchanged unchanged_root left_value)
open GeneralDeclarativeEntailment320 (Entails Holds literal appendFacts model_append)
open GeneralDeclarativeCaptureClosure320 (atoms withOrdinary ordinary_models)
open GeneralDeclarativeFootprint321 (stateNames preserves_models)
open GeneralDeclarativeEqualities322 (Derives semantic entails)
open GeneralDeclarativeOpaqueTrace328 (ordinary_over_support)
open GeneralDeclarativeTrace321 (Trace)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeEndpointProbe321 (Matches)
open GeneralDeclarativeCompileLists321 (Result)
open GeneralDeclarativeNFHead324 (fact)
open GeneralDeclarativeSubstitution320 (logical)
open GeneralDeclarativeTermWalk322 (Walk)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralDeclarationPatterns (normalize)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Ty Equivalent Subtype subtype_trans common_variant_iff)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans eqv_symm)

def names (s : State) (root low high : Nat) (extra : List Nat) : Capture :=
  ⟨low,first s root (low :: high :: extra),high⟩

def row (s : State) (tag root low high : Nat) (extra : List Nat) : Equation :=
  ⟨root,.variant tag (.variable (names s root low high extra).center)⟩

def visible (s : State) (tag root low high : Nat) (extra : List Nat) : State :=
  appendFacts s [row s tag root low high extra]

def ready (s : State) (tag root low high : Nat) (extra : List Nat) : State :=
  withOrdinary (visible s tag root low high extra) (atoms (names s root low high extra))

theorem known_bounds (s : State) (tag root low high : Nat) (extra : List Nat) :
    Bounds (ready s tag root low high extra) (names s root low high extra) :=
  ⟨.constraint (List.mem_append_right _ List.mem_cons_self),
   .constraint (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))⟩

theorem reads_center (s : State) (tag root low high : Nat) (extra : List Nat) :
    Derives (ready s tag root low high extra) (.variable root)
      (.variant tag (.variable (names s root low high extra).center)) :=
  .row (List.mem_append_right _ List.mem_cons_self)

theorem conserve_visible {s : State} (bounds : Bounds s arg)
    (low : Entails s ⟨arg.lower,.variant tag (.variable lo)⟩)
    (high : Entails s ⟨arg.upper,.variant tag (.variable hi)⟩) (extra : List Nat) (m : Assignment) :
    Models s m ↔ ∃ next, Models (visible s tag arg.center lo hi extra) next ∧
      ∀ n ∈ kept s arg.center (lo :: hi :: extra), next n = m n := by
  constructor
  · intro fit
    have l := low m fit
    have h := high m fit
    have r := bounds_sound bounds m fit
    obtain ⟨a,_,actual,_,_⟩ := GeneralDeclarativeOpaqueVariant328.reconstruction tag _ _ _
      (subtype_trans l.2 r.1) (subtype_trans r.2 h.1)
    let next := extend s arg.center (lo :: hi :: extra) m a .top
    have agree : ∀ n ∈ kept s arg.center (lo :: hi :: extra), next n = m n :=
      fun _ known => unchanged m a .top known
    refine ⟨_,(model_append next).mpr ⟨(preserves_models s (fun n read =>
      agree n (List.mem_append_left _ read))).mpr fit,?_⟩,agree⟩
    intro e used
    cases List.mem_singleton.mp used
    change Equivalent (next arg.center).1
      (CommonNominalFullCarrier.variant tag (next (first s arg.center (lo::hi::extra))).1)
    dsimp only [next]
    rw [unchanged_root,left_value]
    exact actual
  · rintro ⟨next,fit,agree⟩
    exact (preserves_models s (fun n known => agree n (List.mem_append_left _ known))).mp
      ((model_append next).mp fit).1

theorem unchanged_models {s : State} (bounds : Bounds s arg)
    (low : Entails s ⟨arg.lower,.variant tag (.variable lo)⟩)
    (high : Entails s ⟨arg.upper,.variant tag (.variable hi)⟩) (extra : List Nat) (m : Assignment) :
    Models (ready s tag arg.center lo hi extra) m ↔ Models (visible s tag arg.center lo hi extra) m := by
  rw [ready,ordinary_models]
  constructor
  · exact And.left
  · intro paired
    have pre := ((model_append m).mp paired).1
    have loBound := low m pre
    have hiBound := high m pre
    have actual := paired.2 _ (List.mem_append_right _ List.mem_cons_self)
    have given := bounds_sound bounds m pre
    have sideL := (common_variant_iff ..).mp (subtype_trans loBound.2 (subtype_trans given.1 actual.1))
    have sideR := (common_variant_iff ..).mp (subtype_trans actual.2 (subtype_trans given.2 hiBound.1))
    refine ⟨paired,?_⟩
    intro atom correct
    change atom ∈ atoms (names s arg.center lo hi extra) at correct
    rcases List.mem_cons.mp correct with same|more
    · cases same; exact sideL
    · cases List.mem_singleton.mp more; exact sideR

theorem conservative {s : State} (bounds : Bounds s arg)
    (low : Entails s ⟨arg.lower,.variant tag (.variable lo)⟩)
    (high : Entails s ⟨arg.upper,.variant tag (.variable hi)⟩) (extra : List Nat) (m : Assignment) :
    Models s m ↔ ∃ next, Models (ready s tag arg.center lo hi extra) next ∧
      ∀ n ∈ kept s arg.center (lo :: hi :: extra), next n = m n :=
  (conserve_visible bounds low high extra m).trans
    (exists_congr fun next => and_congr_left' (unchanged_models bounds low high extra next).symm)

theorem variant_trace {s : State} {p : Supported s done}
    (read : Trace (restriction p) mode n (.variant tag code) used) :
    ∃ e, Derives s (.variable n) (.variant tag (.variable e)) ∧ Trace (restriction p) mode e code used := by
  cases read with
  | variant aliases one nested =>
    exact ⟨_,GeneralDeclarativeOrdinaryIncrease325.derives (ordinary_over_support p)
      (.trans (.congruent (.variable aliases)) (.row one)),nested⟩

theorem from_variant_match {s : State} {p : Supported s done}
    (printed : translate c i (normalize pat) = some (.variant tag code))
    (matched : Matches (restriction p) c i arg pat) (extra : List Nat) :
    ∃ lo hi lowerUses upperUses,
      Trace (restriction p) .lower lo code lowerUses ∧ Trace (restriction p) .upper hi code upperUses ∧
      Bounds (ready s tag arg.center lo hi extra) (names s arg.center lo hi extra) ∧
      Derives (ready s tag arg.center lo hi extra) (.variable arg.center)
        (.variant tag (.variable (names s arg.center lo hi extra).center)) ∧
      (∀ m, Models s m ↔ ∃ next, Models (ready s tag arg.center lo hi extra) next ∧
        ∀ n ∈ kept s arg.center (lo :: hi :: extra), next n = m n) := by
  obtain ⟨span,decoded,thoseLo,thoseHi,written,low,high⟩ := matched
  cases Option.some.inj (written.symm.trans printed)
  obtain ⟨l,atLo,usesLo⟩ := variant_trace low
  obtain ⟨h,atHi,usesHi⟩ := variant_trace high
  exact ⟨l,h,_,_,usesLo,usesHi,known_bounds s tag arg.center l h extra,
    reads_center s tag arg.center l h extra,
    conservative (s := s) span (entails atLo) (entails atHi) extra⟩

end Yulang.GeneralDeclarativeOpaqueVariantNames328
