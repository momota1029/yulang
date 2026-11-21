import Yulang.GeneralVersionedRecursiveBridge310

set_option backward.isDefEq.respectTransparency false
/-! Conditional I-55(4) expressed over one actual selected derivation and one
model. The induction is on the given finite dictionary, not the mixed solver
execution. No assertion of algorithmic stopping is made. -/
namespace Yulang.GeneralVersionedSelectedSoundness310
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open GeneralNominalVersionedEvidence231 (Evidence)
open GeneralVersionedRecursiveBridge310 (ReplayFrame ChoiceBridge JointBridge CurrentCandidate)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralNominalSaturationState (Generated)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (All₂ Dictionary)

variable {roles : Roles.RoleDecls} {registry : Registry} {state : State roles} {root focus : Occurrence roles}

theorem children_generated
    (choice : ChoiceBridge roles) (joint : JointBridge roles)
    (checked : (boundary roles).Checked registry)
    (path : B4TargetV8.Reachable (boundary roles) registry root state)
    {key : Nat} {children : List (Occurrence roles)}
    (reached : focus = root ∨ Generated state.core.erased.current root focus)
    (stable : (boundary roles).Stable registry state focus)
    (selected : Local registry state focus (.selected key children))
    (inhabited : ∃ m, Models state m) :
    ∀ child ∈ children, Generated state.core.erased.current root child := by
  classical
  by_cases history : ReplayFrame registry state focus key children
  · obtain ⟨past,present,rs,ats,allocated,frame,order⟩ := history
    have committed := GeneralNominalVersionedMixedReplay237.recorded_committed rs ats allocated path present frame.context_eq
    intro child member
    have edge := committed.2 child (order ▸ member)
    rw [frame.occurrence_eq] at edge
    exact .child (reached.elim (fun same => same ▸ .root) id) edge
  · obtain ⟨effect,g,s,o,k,c⟩ := GeneralNominalVersionedMixedSelectedEffect235.source_effect checked path selected
    have active := GeneralVersionedRecursiveBridge310.enabled
      (effect := effect) ⟨checked,path,reached,stable,selected,inhabited,history⟩ ⟨g,s,o,k,c⟩ choice joint
    exact fun _ member => GeneralNominalVersionedMixedStableEvidence235.selected_generated_children
      stable active o (GeneralNominalVersionedMixedSourceBoundary234.local_iff.mp selected) reached member

theorem invert {v : B4Target.Vocabulary} {b : B4TargetV8.SourceBoundary v}
    {r : v.Registry} {s : v.State} {d : v.Demand} {key : Nat} {ds : List Dictionary}
    (derived : B4TargetV8.Classify b r s d (.selected (.node key ds))) :
    ∃ kids, B4TargetV8.Local b r s d (.selected key kids) ∧
      All₂ (fun child dict => B4TargetV8.Classify b r s child (.selected dict)) kids ds := by
  cases derived with
  | selected pick below => exact ⟨_,pick,below⟩

mutual
  theorem dictionary
      (choice : ChoiceBridge roles) (joint : JointBridge roles)
      (checked : (boundary roles).Checked registry)
      (path : B4TargetV8.Reachable (boundary roles) registry root state)
      (stable : ∀ d, Generated state.core.erased.current root d → (boundary roles).Stable registry state d)
      (m : Assignment) (valid : Models state m)
      (dict : Dictionary) (d : Occurrence roles) (reached : Generated state.core.erased.current root d)
      (derived : B4TargetV8.Classify (boundary roles) registry state d (.selected dict)) :
      Evidence (Compiled registry) state.core m d dict := by
    cases dict with
    | node k ds =>
      obtain ⟨children,pick,derives⟩ := invert derived
      have edges := children_generated choice joint checked path (.inr reached) (stable d reached) pick ⟨m,valid⟩
      have kids := dictionaries choice joint checked path stable m valid ds children edges derives
      exact (GeneralVersionedRecursiveBridge310.node_and_edges choice joint checked path
        (.inr reached) (stable d reached) pick valid kids).1
    termination_by sizeOf dict

  theorem dictionaries
      (choice : ChoiceBridge roles) (joint : JointBridge roles)
      (checked : (boundary roles).Checked registry)
      (path : B4TargetV8.Reachable (boundary roles) registry root state)
      (stable : ∀ d, Generated state.core.erased.current root d → (boundary roles).Stable registry state d)
      (m : Assignment) (valid : Models state m)
      (ds : List Dictionary) (demands : List (Occurrence roles))
      (reached : ∀ d ∈ demands, Generated state.core.erased.current root d)
      (derived : All₂ (fun d result => B4TargetV8.Classify (boundary roles) registry state d (.selected result)) demands ds) :
      All₂ (Evidence (Compiled registry) state.core m) demands ds := by
    cases derived with
    | nil => exact .nil
    | cons first rest =>
      exact .cons (dictionary choice joint checked path stable m valid _ _ (reached _ List.mem_cons_self) first)
        (dictionaries choice joint checked path stable m valid _ _
          (fun _ member => reached _ (List.mem_cons_of_mem _ member)) rest)
    termination_by sizeOf ds
end

theorem on_returned_snapshot
    (choice : ChoiceBridge roles) (joint : JointBridge roles)
    (checked : (boundary roles).Checked registry)
    (path : B4TargetV8.Reachable (boundary roles) registry root state)
    (halted : ∀ next, ¬ (boundary roles).Step registry root state next)
    (dict : Dictionary)
    (result : B4TargetV8.Classify (boundary roles) registry state root (.selected dict)) :
    ∀ m, Models state m → Evidence (Compiled registry) state.core m root dict := by
  have stable := (GeneralNominalVersionedMixedKernel234.closure halted).2
  intro m valid
  exact dictionary choice joint checked path stable m valid dict root .root result

end Yulang.GeneralVersionedSelectedSoundness310
