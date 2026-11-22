import Yulang.GeneralDeclarativeStoppedFold340
import Yulang.GeneralDeclarativeTaggedDictionary340

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeStoppedLockstep341
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open GeneralNominalCenteredHeadAllocEncoding (registry)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalSaturationState (Generated)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeStoppedFold340 (Produces live_children dictionary)
open CommonRoleOutermostResolver (All₂ Frontier Classify Resolves Summarizes Result Tree Dictionary)

section
variable {roles : Roles.RoleDecls} {r : Registry} {s : State roles}
  {root : Occurrence roles} {project : Occurrence roles → Demand}
  {rule : Demand → Frontier Demand → Prop}

/-- The finite domain actually retained after the raw solver already stops.
The target premises use exactly the ordered projected child demands. -/
def CurrentNodes (r : Registry) (s : State roles) (root : Occurrence roles)
    (project : Occurrence roles → Demand) (rule : Demand → Frontier Demand → Prop) : Prop :=
  ∀ a, Generated s.core.erased.current root a → ∀ key kids,
    Local r s a (.selected key kids) → rule (project a) (.selected key (kids.map project))

structure Terminal (r : Registry) (s : State roles) (root : Occurrence roles) : Prop where
  checked : (boundary roles).Checked r
  path : B4TargetV8.Reachable (boundary roles) r root s
  stopped : ∀ next, ¬ Step (registry r) root s next
  supports : Produces r s root

def translated (rule : Demand → Frontier Demand → Prop) (d : Demand) (dict : Dictionary) : Prop :=
  ∃ tree, Resolves rule d tree ∧ Summarizes tree (.selected dict)

/-- Induct on the given finite success result, not on raw reduction. -/
theorem positive (t : Terminal r s root) (nodes : CurrentNodes r s root project rule)
    (selected : B4TargetV8.Classify (boundary roles) r s root (.selected dict)) :
    Classify rule (project root) (.selected dict) := by
  refine (B4TargetV8.Classify.rec
    (motive_1 := fun a result _ => ∀ d, result = .selected d →
      Generated s.core.erased.current root a → translated rule (project a) d)
    (motive_2 := fun kids ds _ => (∀ a ∈ kids, Generated s.core.erased.current root a) →
      ∃ ts, All₂ (Resolves rule) (kids.map project) ts ∧
        All₂ Summarizes ts (ds.map Result.selected))
    ?_ ?_ ?_ ?_ ?_ ?_ selected) dict rfl .root
  · intro _ _ _ impossible _
    cases impossible
  · intro _ _ _ impossible _
    cases impossible
  · intro _ _ _ impossible _
    cases impossible
  · intro a key kids ds picked _ recurse d equal live
    cases equal
    obtain ⟨_,frame,fit⟩ := t.supports a live key kids picked
    have generated := live_children t.checked t.path picked frame fit live t.stopped
    obtain ⟨ts,checked,summary⟩ := recurse generated
    exact ⟨.selected key ts, .selected (nodes a live key kids picked) checked,
      .selected summary (.selected rfl)⟩
  · intro _
    exact ⟨[],.nil,.nil⟩
  · intro a d as ds _ _ head rest live
    obtain ⟨one,checked,summary⟩ := head d rfl (live a List.mem_cons_self)
    obtain ⟨others,more,out⟩ := rest (fun b h => live b (List.mem_cons_of_mem _ h))
    exact ⟨one::others,.cons checked more,.cons summary out⟩

theorem same_assignment
    {o : GeneralDeclarativeHead320.State} {p : GeneralDeclarativeOrigins321.Supported o done}
    {i : GeneralNominalInspection.Interpretation} {m : GeneralNominalCommonBridge.Assignment}
    {sidecar : List GeneralDeclarativeEndpointOverlay336.Entry}
    {waiting : Demand → GeneralDeclarations.Declaration → Prop}
    (t : Terminal r s root)
    (nodes : CurrentNodes r s root project (GeneralDeclarativeTaggedDictionary340.Rule p sidecar r i waiting))
    (selected : B4TargetV8.Classify (boundary roles) r s root (.selected dict))
    (cover : GeneralNominalCenteredHeadWFSource.Coverage r i)
    (declared : GeneralDeclarativeOutputSource323.Declared r (project root))
    (fit : Models s m) (projectedFit : GeneralDeclarativeExactOverlay337.ModelsExact o sidecar m) :
    Classify (GeneralDeclarativeTaggedDictionary340.Rule p sidecar r i waiting) (project root) (.selected dict) ∧
      GeneralNominalVersionedEvidence231.Evidence (registry r) s.core m root dict ∧
      GeneralDeclarativeExactDictionary337.Evidence r i m (project root) dict := by
  have current := positive t nodes selected
  exact ⟨current,dictionary t.checked t.path t.stopped t.supports fit selected,
    GeneralDeclarativeTaggedDictionary340.dictionary_sound t.checked.2 cover declared current projectedFit⟩

end
end Yulang.GeneralDeclarativeStoppedLockstep341
