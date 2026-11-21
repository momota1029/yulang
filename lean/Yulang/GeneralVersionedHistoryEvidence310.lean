import Yulang.GeneralNominalVersionedMixedReplay237
import Yulang.GeneralCommittedReadEvidence309

set_option backward.isDefEq.respectTransparency false
/-! Recorded semantic effects plus a genuine current frame suffice for
recursive dictionaries. History by itself is not a frame. Ordinary
context extension is allowed in the explicit replay branch. -/
namespace Yulang.GeneralVersionedHistoryEvidence310
open GeneralDeclarations GeneralNominalCenters GeneralSourceDictionaries
open GeneralNominalVersionedEvidence231 (Frame Certificate Evidence)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedTransport231 (extendedPlan)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (All₂)

variable {roles : Roles.RoleDecls} {registry : Registry} {state : State roles}
  {root focus : Occurrence roles} {key : Nat} {children : List (Occurrence roles)}
  {m : Assignment}

abbrev Compiled (r : Registry) := GeneralNominalCenteredHeadAllocEncoding.registry r

/-- Frame revalidation is required explicitly; no recipe based on a model
projection alone certifies the currently registered demand. -/
theorem recorded (checked : (boundary roles).Checked registry)
    (path : B4TargetV8.Reachable (boundary roles) registry root state)
    {plan : Plan roles} (stored : plan ∈ state.plans)
    (frame : Frame (Compiled registry) state.core focus key plan)
    (ordered : children = GeneralNominalVersionedFrame231.children plan.packet)
    (valid : Models state m) :
    Certificate (Compiled registry) state.core m focus key children plan := by
  have committed := GeneralNominalVersionedMixedPlanLedger235.reachable_plan_committed path stored
  have holds := committed.1 m valid
  exact GeneralNominalVersionedEvidence231.certificate_of_semantics frame ordered holds.1
    (GeneralNominalVersionedMixedReady235.ready checked path frame) (frame.occurrence_eq ▸ holds.2)

theorem recorded_extension (checked : (boundary roles).Checked registry)
    (path : B4TargetV8.Reachable (boundary roles) registry root state)
    {old : Plan roles} (stored : old ∈ state.plans) (reserved : List Nat)
    (atoms : List (PresenceNormalForm.Atom Nat)) (allocated : List GeneralNominalIdentities.Origin)
    (frame : Frame (Compiled registry) state.core focus key (extendedPlan reserved atoms allocated old))
    (ordered : children = GeneralNominalVersionedFrame231.children (extendedPlan reserved atoms allocated old).packet)
    (valid : Models state m) :
    Certificate (Compiled registry) state.core m focus key children (extendedPlan reserved atoms allocated old) := by
  have committed := GeneralNominalVersionedMixedReplay237.recorded_committed reserved atoms allocated path stored frame.context_eq
  have holds := committed.1 m valid
  exact GeneralNominalVersionedEvidence231.certificate_of_semantics frame ordered holds.1
    (GeneralNominalVersionedMixedReady235.ready checked path frame) (frame.occurrence_eq ▸ holds.2)

/-- Actual source history, not independent witnesses, supplies parent
    semantics and a generated edge for every ordered child. -/
theorem from_recorded_extension (checked : (boundary roles).Checked registry)
    (path : B4TargetV8.Reachable (boundary roles) registry root state)
    {old : Plan roles} (stored : old ∈ state.plans) (reserved : List Nat)
    (atoms : List (PresenceNormalForm.Atom Nat)) (allocated : List GeneralNominalIdentities.Origin)
    (frame : Frame (Compiled registry) state.core focus key (extendedPlan reserved atoms allocated old))
    (ordered : children = GeneralNominalVersionedFrame231.children (extendedPlan reserved atoms allocated old).packet)
    (valid : Models state m)
    (witnesses : All₂ (Evidence (Compiled registry) state.core m) children dictionaries) :
    Evidence (Compiled registry) state.core m focus (.node key dictionaries) ∧
    (focus = root ∨ GeneralNominalSaturationState.Generated state.core.erased.current root focus →
      ∀ child ∈ children, GeneralNominalSaturationState.Generated state.core.erased.current root child) := by
  have committed := GeneralNominalVersionedMixedReplay237.recorded_committed reserved atoms allocated path stored frame.context_eq
  refine ⟨GeneralNominalVersionedEvidence231.evidence_node
    ⟨_, recorded_extension checked path stored reserved atoms allocated frame ordered valid⟩ witnesses,?_⟩
  intro reached child member
  have edge := committed.2 child (ordered ▸ member)
  rw [frame.occurrence_eq] at edge
  exact .child (reached.elim (fun h => h ▸ .root) id) edge

end Yulang.GeneralVersionedHistoryEvidence310
