import Yulang.GeneralDeclarativeStoppedSelected340

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeStoppedFold340
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalCenters (Plan)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local local_iff)
open GeneralNominalCenteredHeadAllocEncoding (registry)
open GeneralNominalSaturationState (Generated)
open GeneralNominalVersionedEvidence231 (Frame Evidence)
open GeneralDeclarativeStoppedSelected340 (FitFrame install_from_frame source_node)
open GeneralNominalVersionedMixedFrameSelection235 (selected_identifies)
open GeneralDeclarativeStoppedLeaf340 (committed)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (All₂ Dictionary)

-- The producer being cut out here must come from actual sources, not from
-- the desired recursive evidence or from a fabricated install effect.
def Produces (r : Registry) (s : State roles) (root : Occurrence roles) : Prop :=
  ∀ a, Generated s.core.erased.current root a → ∀ key kids, Local r s a (.selected key kids) →
    ∃ plan, Frame (registry r) s.core a key plan ∧ FitFrame (s := s) a plan

theorem live_children {roles : Roles.RoleDecls} {r : Registry}
    {s : State roles} {root a : Occurrence roles} {key : Nat} {kids : List (Occurrence roles)}
    {plan : Plan roles} (checked : (boundary roles).Checked r)
    (path : B4TargetV8.Reachable (boundary roles) r root s)
    (selected : Local r s a (.selected key kids)) (frame : Frame (registry r) s.core a key plan)
    (ready : FitFrame (s := s) a plan)
    (live : Generated s.core.erased.current root a)
    (stopped : ∀ next, ¬ Step (registry r) root s next) :
    ∀ child ∈ kids, Generated s.core.erased.current root child := by
  obtain ⟨effect,rfl,available⟩ := install_from_frame checked path selected frame ready
  have focus : Generated s.core.erased.current root effect.plan.packet.site.occurrence :=
    frame.occurrence_eq.symm ▸ live
  have order := (selected_identifies (local_iff.mp selected) frame).2
  intro child wanted
  apply Generated.child live
  rw [← frame.occurrence_eq]
  exact (committed stopped focus available).2 child (order.symm ▸ wanted)

section
variable {roles : Roles.RoleDecls} {r : Registry} {s : State roles} {root : Occurrence roles}
  {m : Assignment}

theorem dictionary (checked : (boundary roles).Checked r)
    (path : B4TargetV8.Reachable (boundary roles) r root s)
    (stopped : ∀ next, ¬ Step (registry r) root s next)
    (producer : Produces r s root) (fit : Models s m)
    (selected : B4TargetV8.Classify (boundary roles) r s root (.selected dict)) :
    Evidence (registry r) s.core m root dict := by
  refine (B4TargetV8.Classify.rec
    (motive_1 := fun a result _ => ∀ d, result = .selected d →
      Generated s.core.erased.current root a → Evidence (registry r) s.core m a d)
    (motive_2 := fun as ds _ => (∀ a ∈ as, Generated s.core.erased.current root a) →
      All₂ (Evidence (registry r) s.core m) as ds)
    ?_ ?_ ?_ ?_ ?_ ?_ selected) dict rfl .root
  · intro _ _ _ bad _
    cases bad
  · intro _ _ _ bad _
    cases bad
  · intro _ _ _ bad _
    cases bad
  · intro a key kids ds picked _ done this equal lives
    cases equal
    obtain ⟨_,frame,feasible⟩ := producer a lives key kids picked
    have childLive := live_children checked path picked frame feasible lives stopped
    obtain ⟨_,_,_,result⟩ := source_node checked path picked frame feasible lives stopped
    exact (result m fit (done childLive)).1
  · intro _
    exact .nil
  · intro a d as ds _ _ head rest live
    exact .cons (head d rfl (live a List.mem_cons_self))
      (rest (fun later member => live later (List.mem_cons_of_mem _ member)))

theorem producer_necessary_for_claim {dict : Dictionary}
    (checked : (boundary roles).Checked r) (path : B4TargetV8.Reachable (boundary roles) r root s)
    (stopped : ∀ next, ¬ Step (registry r) root s next) (fit : Models s m)
    (picked : B4TargetV8.Classify (boundary roles) r s root (.selected dict))
    (noEvidence : ¬ Evidence (registry r) s.core m root dict) : ¬ Produces r s root :=
  fun p => noEvidence (dictionary checked path stopped p fit picked)

end
end Yulang.GeneralDeclarativeStoppedFold340
