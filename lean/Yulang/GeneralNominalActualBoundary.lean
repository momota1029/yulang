import Yulang.GeneralNominalGroundHeadMatching
import Yulang.GeneralNominalSettledBoundary
import Yulang.B4SkeletonV5

/-! Operational V5 adapter for actual inspection. Local diagnostic fields
are retained explicitly; their agreement with the newer guards is separate
from these six structural laws. No full V5 implementation is constructed. -/
namespace Yulang.GeneralNominalActualBoundary
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalActualInspectionSteps B4TargetV5
open CommonRoleOutermostResolver (Frontier)

abbrev vocabulary := GeneralNominalValueBoundary.vocabulary
abbrev fields := GeneralNominalSettledBoundary.fields

def Stable (registry : Registry) (state : Tracked roles) (root : Occurrence roles) : Prop :=
  ∀ focus, Generated state.current root focus → ∀ after, ¬ At registry state focus after

def remaining (roles : Roles.RoleDecls) : GeneralNominalLocalBoundary.Remaining (vocabulary roles) :=
  { GeneralNominalSettledBoundary.remaining roles with Step := Step, Stable := Stable }

def boundary (roles : Roles.RoleDecls) : SourceBoundary (vocabulary roles) where
  toSourceBoundary := GeneralNominalLocalBoundary.complete (fields roles) (remaining roles)
  Initial := (GeneralNominalValueBoundary.boundary roles).Initial

abbrev Local (registry : Registry) (state : Tracked roles) :=
  GeneralNominalLocalBoundary.Local (fields roles) registry state

theorem local_correspondence (registry : Registry) (state : Tracked roles) (root : Occurrence roles)
    (frontier : Frontier (Occurrence roles)) :
    B4TargetV3.Local (boundary roles).toSourceBoundary registry state root frontier ↔ Local registry state root frontier :=
  (GeneralNominalLocalBoundary.local_extension (remaining roles) frontier).symm

theorem local_total (registry : Registry) (checked : Checked registry) (state : Tracked roles) (root : Occurrence roles) :
    ∃ frontier, Local registry state root frontier :=
  GeneralNominalLocalBoundary.local_total (fun key first last one two =>
    GeneralNominalRecursiveCandidates.survivor_children_functional registry checked state.current.context root key first last one two)

noncomputable def frontiers (roles : Roles.RoleDecls) : B4SkeletonV3.Frontiers (vocabulary roles) := by
  classical
  exact fun registry state =>
    { frontier := fun root => if checked : Checked registry then
        Classical.choose (local_total registry checked state root) else .pending
      Local := B4TargetV3.Local (boundary roles).toSourceBoundary registry state }

theorem closure (registry : Registry) (_checked : (boundary roles).Checked registry)
    (state : Tracked roles) (root : Occurrence roles) (_reachable : Reachable (boundary roles) registry root state)
    (halted : ∀ after, ¬ (boundary roles).Step registry root state after) :
    (boundary roles).Stable registry state root ∧
      ∀ child, (boundary roles).Generated registry state root child → (boundary roles).Stable registry state child := by
  have stable : Stable registry state root := fun focus reached after action => halted after ⟨focus,reached,action⟩
  exact ⟨stable,fun child reached focus path => stable focus (generated_trans reached path)⟩

theorem stepModels (registry : Registry) (_checked : (boundary roles).Checked registry)
    (root : Occurrence roles) (before after : Tracked roles) (_reachable : Reachable (boundary roles) registry root before)
    (step : (boundary roles).Step registry root before after) :
    ∀ model, (boundary roles).Models after model → (boundary roles).Models before model :=
  GeneralNominalSharedSteps.step_models (step_shared step)

theorem localIdentity (registry : Registry) (state : Tracked roles) (root : Occurrence roles)
    (_reachable : Reachable (boundary roles) registry root state) :
    (frontiers roles registry state).Local = B4TargetV3.Local (boundary roles).toSourceBoundary registry state := rfl

theorem frontierLocal (registry : Registry) (checked : (boundary roles).Checked registry)
    (state : Tracked roles) (root : Occurrence roles) (_reachable : Reachable (boundary roles) registry root state)
    (demand : Occurrence roles) (frontier : Frontier (Occurrence roles)) :
    (frontiers roles registry state).frontier demand = frontier ↔
      B4TargetV3.Local (boundary roles).toSourceBoundary registry state demand frontier := by
  classical
  have valid := Classical.choose_spec (local_total registry checked.2 state demand)
  change (if checked : Checked registry then Classical.choose (local_total registry checked state demand) else .pending) = frontier ↔ _
  rw [dite_eq_left checked.2]
  constructor
  · intro same
    rw [same] at valid
    exact (local_correspondence registry state demand frontier).mpr valid
  · intro given
    exact GeneralNominalLocalBoundary.local_functional valid ((local_correspondence registry state demand frontier).mp given)

theorem dictionaryRefl (dictionary : CommonRoleOutermostResolver.Dictionary) :
    (boundary roles).DictionaryEquivalent dictionary dictionary := GeneralDictionaryPayloadOrder.equivalent_refl dictionary

theorem initialReorders (registry other : Registry) (_checked : (boundary roles).Checked registry)
    (_checkedOther : (boundary roles).Checked other) (order : (boundary roles).Reorders registry other)
    (state : Tracked roles) (root : Occurrence roles) (given : (boundary roles).Initial registry root state) :
    (boundary roles).Initial other root state := by
  obtain ⟨context,formed,same⟩ := given
  exact ⟨context,GeneralDictionaryInitialSource.source_reorders registry other order context root formed,same⟩

theorem reachable_iff_sourceFormed : Reachable (boundary roles) registry root state ↔ SourceFormed registry root state := by
  constructor
  · rintro ⟨start,⟨context,source,rfl⟩,path⟩
    induction path with
    | refl => exact .initial context source
    | tail path step ih => exact .update ih step
  · intro formed
    induction formed with
    | initial context source => exact ⟨_,⟨context,source,rfl⟩,.refl⟩
    | update formed step ih => exact reachable_step (boundary roles) ih step

theorem steps_shared (path : B4Target.Steps (Step registry root) before after) :
    B4Target.Steps (GeneralNominalSharedSteps.Step registry root) before after := by
  induction path with
  | refl => exact .refl
  | tail path step ih => exact .tail ih (step_shared step)

theorem shared_halted (halted : ∀ after, ¬ GeneralNominalSharedSteps.Step registry root state after) :
    ∀ after, ¬ Step registry root state after := fun _ step => halted _ (step_shared step)

/-- The source restriction is part of Initial, not a new Checked premise. -/
def groundBoundary (roles : Roles.RoleDecls) : SourceBoundary (vocabulary roles) :=
  { boundary roles with Initial := fun registry root state => ∃ context labels,
      GeneralNominalSourceFormation.InitialSource registry context root ∧
      GeneralNominalActualBudget.PointSource context root ∧
      GeneralNominalGroundAccessibility.GroundRoots context root labels ∧ state = GeneralNominalSupport.initial context root }

theorem ground_progress (registry : Registry) (checked : (groundBoundary roles).Checked registry)
    (state : Tracked roles) (root : Occurrence roles) (reachable : Reachable (groundBoundary roles) registry root state) :
    Acc (fun next current => (groundBoundary roles).Step registry root current next) state := by
  obtain ⟨start,⟨context,labels,source,point,ground,rfl⟩,path⟩ := reachable
  have accessible := GeneralNominalGroundHeadMatching.ground_class_p_accessible checked.2 source point ground
  induction path with
  | refl => exact accessible
  | tail path step ih => exact ih.inv step

theorem terminal_of_accessible {α : Type} {step : α → α → Prop} {start : α}
    (accessible : Acc (fun next current => step current next) start) :
    ∃ final, B4Target.Steps step start final ∧ ∀ next, ¬ step final next := by
  classical
  induction accessible with
  | intro start below ih =>
    by_cases advances : ∃ next, step start next
    · obtain ⟨next,edge⟩ := advances
      obtain ⟨final,path,halted⟩ := ih next edge
      have compose {a b c : α} (one : B4Target.Steps step a b) (two : B4Target.Steps step b c) :
          B4Target.Steps step a c := by
        induction two with
        | refl => exact one
        | tail path last ih => exact .tail ih last
      exact ⟨final,compose (.tail .refl edge) path,halted⟩
    · exact ⟨start,.refl,fun next edge => advances ⟨next,edge⟩⟩

theorem ground_terminal (registry : Registry) (checked : (groundBoundary roles).Checked registry)
    (state : Tracked roles) (root : Occurrence roles) (reachable : Reachable (groundBoundary roles) registry root state) :
    ∃ final, B4Target.Steps (Step registry root) state final ∧
      (∀ next, ¬ Step registry root final next) ∧ Stable registry final root ∧
      (∀ child, Generated final.current root child → Stable registry final child) ∧
      ∀ model, Models final.current model → Models state.current model := by
  obtain ⟨final,path,halted⟩ := terminal_of_accessible (ground_progress registry checked state root reachable)
  have oldReach : Reachable (boundary roles) registry root state := by
    obtain ⟨start,⟨context,labels,source,point,ground,rfl⟩,trace⟩ := reachable
    exact ⟨_,⟨context,source,rfl⟩,trace⟩
  have stable := closure registry checked final root (reachable_steps (boundary roles) oldReach path) halted
  refine ⟨final,path,halted,stable.1,stable.2,?_⟩
  exact B4SkeletonV5.steps_models (boundary roles) registry root (stepModels registry checked root) oldReach path

end Yulang.GeneralNominalActualBoundary
