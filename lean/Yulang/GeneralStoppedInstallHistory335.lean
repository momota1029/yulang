import Yulang.GeneralNominalVersionedMixedGrowth234
import Yulang.GeneralStoppedOrdinarySite335
import Yulang.GeneralNominalVersionedMixedStableLaws235

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralStoppedInstallHistory335
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalCenters (Site)
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalVersionedMixedKernel234 (Step At Administrative Installable Committed)
open GeneralNominalVersionedInstall232 (install)
open GeneralNominalVersionedChildren232 (emitted edges emitted_occurrences child_edge)
open GeneralNominalVersionedFrame231 (children)
open GeneralNominalSaturationState (Generated)
open GeneralNominalVersionedMixedGrowth234 (steps_sites steps_edges steps_plans)
open GeneralStoppedOrdinarySite335 (demand occurrence)
open B4Target (Steps)

/-- Provenance of a stored versioned effect is an actual install step
at its precise previous state, not a later semantic explanation of
why those output equations happen to hold. -/
def InstalledBetween (registry : Registry) (root : Occurrence roles)
    (start final : State roles) (effect : Effect roles) : Prop :=
  ∃ before, Steps (Step registry root) start before ∧
    Generated before.core.erased.current root effect.plan.packet.site.occurrence ∧
    Installable registry before effect ∧ ¬Committed before effect.plan ∧
    Steps (Step registry root) (install before effect) final

theorem roll {registry : Registry} {root : Occurrence roles} {start before after : State roles}
    (found : InstalledBetween registry root start before effect)
    (step : Step registry root before after) : InstalledBetween registry root start after effect := by
  obtain ⟨older,earlier,derived,ok,novel,later⟩ := found
  exact ⟨older,earlier,derived,ok,novel,.tail later step⟩

theorem administrative_effects {before after : State roles}
    (action : Administrative before focus after) : after.effects = before.effects := by
  cases action <;> rfl

/-- Exact historical origin for every stored versioned effect, or a
record already present in the named starting snapshot. -/
theorem effects_origin {registry : Registry} {root : Occurrence roles}
    {start final : State roles} (path : Steps (Step registry root) start final)
    (retained : effect ∈ final.effects) :
    effect ∈ start.effects ∨ InstalledBetween registry root start final effect := by
  induction path with
  | refl => exact .inl retained
  | @tail before after path step ih =>
    have old : effect ∈ before.effects → effect ∈ start.effects ∨ InstalledBetween registry root start after effect :=
      fun h => (ih h).elim Or.inl (fun prior => .inr (roll prior step))
    obtain ⟨focus,generated,action⟩ := step
    cases action with
    | administrative action => exact old ((administrative_effects action) ▸ retained)
    | refresh => exact old retained
    | merge => exact old retained
    | install added enabled novel =>
      rcases List.mem_cons.mp retained with rfl|prev
      · exact .inr ⟨before,path,generated,enabled,novel,.refl⟩
      · exact old prev

theorem installed_origin {registry : Registry} {root : Occurrence roles}
    {start final : State roles} (path : Steps (Step registry root) start final)
    (empty : start.effects = []) (retained : effect ∈ final.effects) :
    InstalledBetween registry root start final effect := by
  exact (effects_origin path retained).resolve_left (fun seen => List.not_mem_nil (empty ▸ seen))

/-- The exact stored child's actual center survives arbitrary later
mixed steps. Edges retain occurrence identity, and every physical
emission is still one of the final state's genuine Sites. -/
theorem retained_sites {registry : Registry} {root : Occurrence roles}
    {start final : State roles} (came : InstalledBetween registry root start final effect) :
    emitted effect.plan ⊆ final.core.sites ∧ edges effect.plan ⊆ final.core.erased.current.edges := by
  obtain ⟨before,_,_,_,_,rest⟩ := came
  constructor
  · intro s added
    exact steps_sites rest (List.mem_append_right _ added)
  · intro e added
    exact steps_edges rest (List.mem_append_right _ added)

theorem retained_projected {registry : Registry} {root : Occurrence roles}
    {start final : State roles} (came : InstalledBetween registry root start final effect) :
    ((emitted effect.plan).map occurrence).map Prod.fst = (children effect.plan.packet).map Occurrence.identity ∧
    (∀ site ∈ emitted effect.plan, site ∈ final.core.sites ∧
      (effect.plan.packet.site.occurrence,site.occurrence) ∈ final.core.erased.current.edges ∧
      (demand site).outputs = site.occurrence.demand.outputs) := by
  constructor
  · rw [GeneralStoppedOrdinarySite335.retained_order,← emitted_occurrences]
    rw [List.map_map]
    rfl
  · intro site used
    have origin : site.occurrence ∈ children effect.plan.packet := by
      rw [← emitted_occurrences]
      exact List.mem_map_of_mem used
    exact ⟨(retained_sites came).1 used,(retained_sites came).2 (child_edge origin),rfl⟩

theorem retained_plan {registry : Registry} {root : Occurrence roles} {start final : State roles}
    (came : InstalledBetween registry root start final effect) :
    effect.plan ∈ final.plans := by
  obtain ⟨before,_,_,_,_,rest⟩ := came
  exact steps_plans rest List.mem_cons_self

/-- Once installed, the original occurrence, ordered projected
requests, and current live class effects travel together. No
uninstalled leaf is inferred from effect membership. -/
theorem saved_projection {registry : Registry} {root : Occurrence roles} {start final : State roles}
    (path : Steps (Step registry root) start final) (empty : start.effects = [])
    (found : effect ∈ final.effects) (fit : Models final model) :
    InstalledBetween registry root start final effect ∧
    (∀ site ∈ emitted effect.plan, site ∈ final.core.sites ∧ site.Holds model) ∧
    effect.Live final.core model := by
  have exactOrigin := installed_origin path empty found
  have semantic := GeneralNominalVersionedJournal232.effect_models fit found
  exact ⟨exactOrigin,fun site there =>
    ⟨(retained_sites exactOrigin).1 there,GeneralNominalVersionedChildren232.emitted_holds (GeneralNominalVersionedJournal232.plan_models fit (retained_plan exactOrigin)) there⟩,semantic.2⟩

end Yulang.GeneralStoppedInstallHistory335
