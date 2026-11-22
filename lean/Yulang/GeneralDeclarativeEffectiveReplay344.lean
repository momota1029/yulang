import Yulang.GeneralDeclarativeReplayOrder344
import Yulang.GeneralDeclarativeModeBridge343

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeEffectiveReplay344
open GeneralNominalCenters (Site)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeReplayOrder344 (SameBirth)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeStoppedPaired341 (Placement activeDemand placement_targets)
open GeneralDeclarativeModeBridge343 (rows realized written)
open GeneralDeclarativeEntailment320 (appendFacts model_append Holds)
open GeneralStoppedOrdinarySite335 (demand)
open GeneralStoppedPlacement335 (Meaning)
open CommonRoleOutermostResolver (All₂)

noncomputable def effective (raw : GeneralNominalVersionedJournal232.State rs) (site : Site rs) (d : Demand) : Demand :=
  {d with outputs := (activeDemand raw site).outputs}

def appendModes : List (Site rs) → List Demand → List Equation
  | site::ss,d::ds => rows (demand site).arguments d.arguments ++ appendModes ss ds
  | _,_ => []

noncomputable def appendEffective (raw : GeneralNominalVersionedJournal232.State rs) :
    List (Site rs) → List Demand → List Demand
  | site::ss,d::ds => effective raw site d :: appendEffective raw ss ds
  | _,_ => []

theorem equations {m : Assignment} {ss : List (Site rs)} {ds : List Demand}
    (paired : All₂ (SameBirth m) ss ds) :
    ∀ row ∈ appendModes ss ds, Holds m row := by
  induction paired with
  | nil => intro _ h; cases h
  | cons front _ rest =>
    intro row h
    rcases List.mem_append.mp h with first|later
    · exact written front.arguments row first
    · exact rest row later

theorem placements {raw : GeneralNominalVersionedJournal232.State rs}
    {m : Assignment} {ss : List (Site rs)} {ds : List Demand} {s : State}
    (paired : All₂ (SameBirth m) ss ds) (current : ∀ site ∈ ss, site ∈ raw.core.sites)
    (stored : appendModes ss ds ⊆ s.equations) :
    All₂ (fun site logical => Placement raw s site.occurrence logical) ss (appendEffective raw ss ds) := by
  induction paired with
  | nil => exact .nil
  | @cons site logical after later birth remains ih =>
    have agrees := realized birth.arguments (s := s)
      (fun _ h => stored (List.mem_append_left _ h))
    refine .cons ⟨site,current _ List.mem_cons_self,rfl,birth.role,agrees,rfl⟩ ?_
    exact ih (fun site h => current site (List.mem_cons_of_mem _ h))
      (fun _ h => stored (List.mem_append_right _ h))

/-- All modes of all actually registered children can be paired at
once. When live class requests differ, the effective demand records
them literally; the original compiler birth demand is retained
separately and is not represented as those current requests. -/
theorem all_effective {raw : GeneralNominalVersionedJournal232.State rs}
    {m : Assignment} {ss : List (Site rs)} {ds : List Demand} {s : State}
    (paired : All₂ (SameBirth m) ss ds) (current : ∀ site ∈ ss, site ∈ raw.core.sites)
    (valid : Models s m) :
    let t := appendFacts s (appendModes ss ds)
    Models t m ∧
      All₂ (fun site logical => Placement raw t site.occurrence logical) ss (appendEffective raw ss ds) := by
  exact ⟨(model_append m).mpr ⟨valid,equations paired⟩,
    placements paired current (fun _ h => List.mem_append_right _ h)⟩

theorem birth_effective {raw : GeneralNominalVersionedJournal232.State rs}
    {m : Assignment} {ss : List (Site rs)} {ds : List Demand}
    (paired : All₂ (SameBirth m) ss ds)
    (unchanged : ∀ site ∈ ss, (activeDemand raw site).outputs = (demand site).outputs) :
    appendEffective raw ss ds = ds := by
  induction paired with
  | nil => rfl
  | @cons site logical after later birth rest ih =>
    change effective raw site _ :: _ = _
    have eq := (unchanged site List.mem_cons_self).trans birth.targets
    simp only [effective,eq,ih (fun site h => unchanged site (List.mem_cons_of_mem _ h))]

end Yulang.GeneralDeclarativeEffectiveReplay344
