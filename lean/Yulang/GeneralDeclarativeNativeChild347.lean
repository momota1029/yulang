import Yulang.GeneralDeclarativeCurrentTrace345
import Yulang.GeneralDeclarativeNativeWhere347
import Yulang.GeneralStoppedInstallHistory335
import Yulang.GeneralDeclarativeCommitPosition344

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeNativeChild347
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalCenters (Plan Site)
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalVersionedMixedKernel234 (Step At Administrative)
open GeneralNominalVersionedInstall232 (install)
open GeneralNominalVersionedChildren232 (emitted rawSites emitted_occurrences)
open GeneralStoppedInstallHistory335 (InstalledBetween retained_plan retained_sites)
open GeneralDeclarativeCommitPosition344 (clauses signature)
open GeneralNominalVersionedFrame231 (childSite children)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalSaturationState (Generated)
open B4Target (Steps)

def Preserves (before after : State rs) : Prop :=
  ∃ tail, after.core.sites = before.core.sites ++ tail

theorem administrative {a b : State rs} (act : Administrative a focus b) : Preserves a b := by
  cases act <;> exact ⟨[],(List.append_nil _).symm⟩

theorem step {a b : State rs} (run : Step r root a b) : Preserves a b := by
  obtain ⟨_,_,op⟩ := run
  cases op with
  | administrative act => exact administrative act
  | refresh | merge => exact ⟨[],(List.append_nil _).symm⟩
  | install e _ _ => exact ⟨emitted e.plan,rfl⟩

theorem traces {start final : State rs} {r : Registry} {root : Occurrence rs}
    (trace : Steps (Step r root) start final) : Preserves start final := by
  induction trace with
  | refl => exact ⟨[],(List.append_nil _).symm⟩
  | tail _ action ih =>
    obtain ⟨x,first⟩ := ih
    obtain ⟨y,second⟩ := step action
    exact ⟨x++y,by rw [second,first,List.append_assoc]⟩

theorem retained_centered {start final : State rs} {r : Registry} {root : Occurrence rs}
    (trace : Steps (Step r root) start final) {i : Nat}
    (there : start.core.sites[i]? = some site) : final.core.sites[i]? = some site := by
  obtain ⟨tail,h⟩ := traces trace
  rw [h,List.getElem?_append_left (List.getElem?_eq_some_iff.mp there).1]
  exact there

theorem exact_clause {p : Plan rs} {ord : Nat} {site : Site rs} (emittedAt : (emitted p)[ord]? = some site) :
    ∃ clause, (clauses p)[ord]? = some clause ∧ site = childSite p clause.val (signature p clause) := by
  change ((clauses p).map (fun q => childSite p q.val (signature p q)))[ord]? = some site at emittedAt
  rw [List.getElem?_map] at emittedAt
  cases atOrd : (clauses p)[ord]? with
  | none => rw [atOrd] at emittedAt; cases emittedAt
  | some q =>
    rw [atOrd] at emittedAt
    exact ⟨q,rfl,(Option.some.inj emittedAt).symm⟩

/-- A native install really produces an ordered child site. Later
native steps preserve its exact index in both the centered and
observed lists, and the final model fits the stored actual center. -/
theorem current_positions {r : Registry} {root : Occurrence rs} {start final : State rs}
    {e : Effect rs} (history : InstalledBetween r root start final e) {ord : Nat} {site : Site rs}
    (emittedAt : (emitted e.plan)[ord]? = some site) (m : Assignment) (model : Models final m) :
    ∃ (before : State rs), ∃ clause,
      (clauses e.plan)[ord]? = some clause ∧ site = childSite e.plan clause.val (signature e.plan clause) ∧
      final.core.sites[before.core.sites.length+ord]? = some site ∧
      final.core.erased.current.sites[before.core.erased.current.sites.length+ord]? = some site.observed ∧
      (children e.plan.packet)[ord]? = some site.occurrence ∧
      Generated final.core.erased.current root site.occurrence ∧ site.Holds m := by
  obtain ⟨q,pos,shape⟩ := exact_clause emittedAt
  have kept := retained_plan history
  obtain ⟨before,_,focus,enabled,novel,later⟩ := history
  have childAt : (children e.plan.packet)[ord]? = some site.occurrence := by
    rw [← emitted_occurrences,List.getElem?_map,emittedAt]; rfl
  have birth : (install before e).core.sites[before.core.sites.length+ord]? = some site := by
    change (before.core.sites ++ emitted e.plan)[before.core.sites.length+ord]? = _
    rwa [List.getElem?_append_right (by omega),Nat.add_sub_cancel_left]
  have birthRaw : (install before e).core.erased.current.sites[before.core.erased.current.sites.length+ord]? =
      some site.observed := by
    change (before.core.erased.current.sites ++ rawSites e.plan)[before.core.erased.current.sites.length+ord]? = _
    rw [List.getElem?_append_right (by omega),Nat.add_sub_cancel_left]
    change ((emitted e.plan).map Site.observed)[ord]? = _
    rw [List.getElem?_map,emittedAt]; rfl
  have member := List.mem_iff_getElem?.mpr ⟨_,childAt⟩
  have grows := GeneralNominalVersionedMixedGrowth234.steps later
  have birthParent : Generated (install before e).core.erased.current root e.plan.packet.site.occurrence :=
    GeneralNominalVersionedMixedGrowth234.generated
      (GeneralNominalVersionedMixedGrowth234.at_growth (.install e enabled novel)) focus
  have next : Generated (install before e).core.erased.current root site.occurrence :=
    .child birthParent (GeneralNominalVersionedInstall232.installed_child member)
  exact ⟨before,q,pos,shape,retained_centered later birth,
    GeneralDeclarativeCurrentTrace345.previous_at later birthRaw,childAt,
    GeneralNominalVersionedMixedGrowth234.generated grows next,
    GeneralNominalVersionedChildren232.emitted_holds
      (GeneralNominalVersionedJournal232.plan_models model kept) (List.mem_iff_getElem?.mpr ⟨_,emittedAt⟩)⟩

end Yulang.GeneralDeclarativeNativeChild347
