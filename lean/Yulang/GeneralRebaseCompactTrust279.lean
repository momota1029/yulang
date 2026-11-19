import Yulang.GeneralRebaseCompactLocal279

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27000
set_option maxHeartbeats 9800000
namespace Yulang.GeneralRebaseCompactTrust279
open GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State)
open GeneralRebaseCompactEdgeInstall279 (replaceEdges aliases_exact)
open GeneralRebaseInstallNovelty279 (Edge)
open GeneralNominalVersionedMixedObservations233 (Justified CacheSound)

variable {roles : Roles.RoleDecls} {state : State roles} {new : List (Edge roles)}

theorem replace_twice (state : State roles) (first last : List (Edge roles)) :
    replaceEdges (replaceEdges state first) last = replaceEdges state last := rfl

theorem replace_self (state : State roles) : replaceEdges state state.core.erased.current.edges = state := by
  cases state with
  | mk legacy plans effects =>
    cases legacy with
    | mk core historical =>
      cases core with
      | mk tracked sites plans sourceSites sourceRecorded =>
        cases tracked with
        | mk src current facts =>
          cases current <;> rfl

theorem legacy_discharged {focus : Occurrence roles}
    (given : GeneralNominalSupport.Discharged state.core.erased.current focus) :
    GeneralNominalSupport.Discharged (replaceEdges state new).core.erased.current focus := by
  induction given with
  | packet p mem _ ih => exact .packet p mem ih
  | alias first last a b linked _ ih => exact .alias first last a b ((aliases_exact state new _ _).mpr linked) ih

theorem versioned_discharged {focus : Occurrence roles}
    (given : GeneralNominalVersionedSupport233.Discharged state focus) :
    GeneralNominalVersionedSupport233.Discharged (replaceEdges state new) focus := by
  induction given with
  | packet p mem _ ih => exact .packet p mem ih
  | alias first last a b linked _ ih => exact .alias first last a b ((aliases_exact state new _ _).mpr linked) ih

theorem legacy_trusted {facts} (given : GeneralNominalCenteredHeadMatStepSupport.Trusted state.legacy facts) :
    GeneralNominalCenteredHeadMatStepSupport.Trusted (replaceEdges state new).legacy facts := by
  induction given with
  | source => exact .source
  | input p _ recorded read ih => exact .input p ih recorded read
  | output e _ recorded recordedPlan input classRead settled ih =>
    exact .output e ih recorded recordedPlan input classRead
      ⟨settled.1,fun child member => legacy_discharged (settled.2 child member)⟩
  | merge first last _ a b linked atoms fits same ih =>
    exact .merge first last ih a b ((aliases_exact state new _ _).mpr linked) atoms fits same

theorem versioned_trusted {facts} (given : GeneralNominalVersionedSupport233.Trusted state facts) :
    GeneralNominalVersionedSupport233.Trusted (replaceEdges state new) facts := by
  induction given with
  | source => exact .source
  | input p _ recorded read ih => exact .input p ih recorded read
  | output e _ recorded recordedPlan input classRead settled ih =>
    exact .output e ih recorded recordedPlan input classRead
      ⟨settled.1,fun child member => versioned_discharged (settled.2 child member)⟩
  | merge first last _ a b linked atoms fits same ih =>
    exact .merge first last ih a b ((aliases_exact state new _ _).mpr linked) atoms fits same

theorem justified_forward {obs : GeneralCanonicalObservations.Observation} (given : Justified state obs) :
    Justified (replaceEdges state new) obs := by
  obtain ⟨old,fresh,lt,vt,meaning⟩ := given
  exact ⟨old,fresh,legacy_trusted lt,versioned_trusted vt,meaning⟩

theorem justified_iff (obs : GeneralCanonicalObservations.Observation) :
    Justified (replaceEdges state new) obs ↔ Justified state obs := by
  constructor
  · intro given
    have back := justified_forward (new := state.core.erased.current.edges) given
    rwa [replace_twice,replace_self] at back
  · exact justified_forward

theorem cache_iff (snapshot : GeneralNominalState.State) :
    CacheSound (replaceEdges state new) snapshot ↔ CacheSound state snapshot := by
  simp only [CacheSound,justified_iff]

end Yulang.GeneralRebaseCompactTrust279
