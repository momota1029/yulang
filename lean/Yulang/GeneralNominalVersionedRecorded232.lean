import Yulang.GeneralNominalVersionedBoundary232

/-! Every installed versioned effect has a corresponding full-meaning plan.
The invariant is derived from actual source initialization and kernel steps;
it is not imposed on arbitrary hand-constructed mixed journals. -/
namespace Yulang.GeneralNominalVersionedRecorded232
open GeneralNominalVersionedJournal232
open GeneralNominalVersionedKernel232

def Recorded (state : State roles) : Prop :=
  ∀ effect ∈ state.effects, effect.plan ∈ state.plans

theorem lift (legacy : Legacy.State roles) : Recorded (GeneralNominalVersionedJournal232.lift legacy) := by
  intro effect member
  cases member

theorem initial (context : GeneralNominalCandidates.Context) (root : GeneralSourceDictionaries.Occurrence roles) :
    Recorded (GeneralNominalVersionedJournal232.initial context root) := lift _

theorem install (given : Recorded state) : Recorded (GeneralNominalVersionedInstall232.install state effect) := by
  intro candidate member
  rcases List.mem_cons.mp member with rfl | old
  · exact List.mem_cons_self ..
  · exact List.mem_cons_of_mem _ (given candidate old)

theorem change (given : Recorded state) : Recorded (GeneralNominalVersionedAdministrative232.change state after) := given

theorem enqueue (given : Recorded state) : Recorded (GeneralNominalVersionedAdministrative232.enqueue state focus) := given

theorem equate (given : Recorded state) : Recorded (GeneralNominalVersionedAdministrative232.equate state first last) := given

theorem merge (given : Recorded state) : Recorded (GeneralNominalVersionedAdministrative232.merge state first last) := given

theorem refresh (given : Recorded state) : Recorded (GeneralNominalVersionedRefresh232.refresh state context) := given

theorem reobserve (given : Recorded state) : Recorded (GeneralNominalVersionedRefresh232.reobserve state revision) := given

theorem administrative (action : Administrative before focus after) (given : Recorded before) : Recorded after := by
  cases action <;> exact given

theorem step (action : Step registry root before after) (given : Recorded before) : Recorded after := by
  obtain ⟨_,_,action⟩ := action
  cases action with
  | administrative action => exact administrative action given
  | refresh => exact given
  | install => exact install given
  | merge => exact given

theorem steps (path : B4Target.Steps (Step registry root) before after) (given : Recorded before) : Recorded after := by
  induction path with
  | refl => exact given
  | tail _ action ih => exact step action ih

theorem reachable (path : B4TargetV8.Reachable (GeneralNominalVersionedBoundary232.boundary roles) registry root state) :
    Recorded state := by
  obtain ⟨first,⟨legacy,_,same⟩,path⟩ := path
  subst first
  exact steps path (lift legacy)

theorem effect_full_holds (recorded : Recorded state) (valid : Models state model)
    (present : effect ∈ state.effects) : GeneralNominalVersionedPlans231.Holds effect.plan model :=
  valid.2.1 effect.plan (recorded effect present)

theorem reachable_effect_full_holds
    (path : B4TargetV8.Reachable (GeneralNominalVersionedBoundary232.boundary roles) registry root state)
    (valid : Models state model) (present : effect ∈ state.effects) :
    GeneralNominalVersionedPlans231.Holds effect.plan model :=
  effect_full_holds (reachable path) valid present

end Yulang.GeneralNominalVersionedRecorded232
