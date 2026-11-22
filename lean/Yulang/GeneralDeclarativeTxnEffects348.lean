import Yulang.GeneralDeclarativeWhereTxn348

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeTxnEffects348
open GeneralNominalCenters (Plan Site)
open GeneralWhereVersionInstall317 (Journal install installCore emitted)
open GeneralWhereOriginSuccessor318 (SilentChildren alias_copy)
open GeneralNominalCandidates (Context)
open GeneralNominalCenteredHeadOutputs (requests)
open GeneralNominalDemandMerging (Site)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalSaturationState (Alias)

private theorem filter_same (xs : List α) (f g : α → Bool)
    (each : ∀ x, f x = g x) : xs.filter f = xs.filter g := by
  induction xs with
  | nil => rfl
  | cons x rest ih => simp [List.filter_cons,each x,ih]

private theorem nil_flatMap (xs : List α) (f : α → List β)
    (all : ∀ x ∈ xs,f x = []) : xs.flatMap f = [] := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    simp [List.flatMap_cons,all x List.mem_cons_self,ih (fun y h => all y (List.mem_cons_of_mem _ h))]

/-- A silent corrected frontier preserves the entire literal request
list, including physical order and duplicates, not just membership. -/
theorem literal_requests (j : Journal rs) (ctx : Context) (p : Plan rs)
    (silent : SilentChildren p) (focus : Occurrence rs) :
    requests (install j ctx p).mixed.core focus = requests j.mixed.core focus := by
  classical
  unfold requests
  let raw0 := j.mixed.core.erased.current
  let raw1 := (install j ctx p).mixed.core.erased.current
  let new := (emitted p).map GeneralNominalCenters.Site.observed
  change ((raw0.sites ++ new).filter
    (fun a => decide (Alias raw1 focus.identity a.occurrence.identity))).flatMap
    (fun a => a.occurrence.demand.outputs) =
      (raw0.sites.filter (fun a => decide (Alias raw0 focus.identity a.occurrence.identity))).flatMap
        (fun a => a.occurrence.demand.outputs)
  have same (a : GeneralNominalDemandMerging.Site rs) :
      decide (Alias raw1 focus.identity a.occurrence.identity) =
        decide (Alias raw0 focus.identity a.occurrence.identity) := by
    have proof : Alias raw1 focus.identity a.occurrence.identity ↔ Alias raw0 focus.identity a.occurrence.identity :=
      ⟨alias_copy (a := raw1) (b := raw0) rfl,alias_copy (a := raw0) (b := raw1) rfl⟩
    by_cases h : Alias raw0 focus.identity a.occurrence.identity
    · simp [h,proof.mpr h]
    · have no : ¬ Alias raw1 focus.identity a.occurrence.identity := fun found => h (proof.mp found)
      simp [no,h]
  rw [List.filter_append,List.flatMap_append,filter_same _ _ _ same]
  have no : (new.filter (fun a => decide (Alias raw1 focus.identity a.occurrence.identity))).flatMap
      (fun a => a.occurrence.demand.outputs) = [] := by
    apply nil_flatMap
    intro a selected
    have present := (List.mem_filter.mp selected).1
    obtain ⟨s,stored,rfl⟩ := List.mem_map.mp present
    exact silent s stored
  rw [no,List.append_nil]

end Yulang.GeneralDeclarativeTxnEffects348
