import Yulang.GeneralDeclarativeMergeOrder345

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeCurrentTrace345
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMixedKernel234 (Administrative At Step)
open GeneralNominalSaturationState (Alias)
open GeneralDeclarativeCurrentOrder345 (Row rows exact_row)
open GeneralNominalDemandMerging (pointSite)

abbrev RawSite (rs : Roles.RoleDecls) := GeneralNominalDemandMerging.Site rs

def Prefix (before after : State rs) : Prop :=
  ∃ extra, after.core.erased.current.sites = before.core.erased.current.sites ++ extra

theorem administrative {before after : State rs} (step : Administrative before focus after) :
    Prefix before after := by
  cases step with
  | enqueue => exact ⟨[pointSite focus],rfl⟩
  | refresh | equate | reobserve => exact ⟨[],(List.append_nil _).symm⟩

theorem at_prefix {r : Registry} {before after : State rs} (step : At r before focus after) :
    Prefix before after := by
  cases step with
  | administrative act => exact administrative act
  | refresh | merge => exact ⟨[],(List.append_nil _).symm⟩
  | install effect _ _ => exact ⟨GeneralNominalVersionedChildren232.rawSites effect.plan,rfl⟩

theorem trace_prefix {r : Registry} {before after : State rs} {root : Occurrence rs}
    (trace : B4Target.Steps (Step r root) before after) : Prefix before after := by
  induction trace with
  | refl => exact ⟨[],(List.append_nil _).symm⟩
  | tail _ action ih =>
    obtain ⟨a,first⟩ := ih
    obtain ⟨_,_,h⟩ := action
    obtain ⟨b,last⟩ := at_prefix h
    exact ⟨a ++ b,by rw [last,first,List.append_assoc]⟩

theorem previous_at {r : Registry} {before after : State rs} {root : Occurrence rs}
    {i : Nat} (trace : B4Target.Steps (Step r root) before after)
    (physical : before.core.erased.current.sites[i]? = some site) :
    after.core.erased.current.sites[i]? = some site := by
  obtain ⟨extra,same⟩ := trace_prefix trace
  rw [same,List.getElem?_append_left (List.getElem?_eq_some_iff.mp physical).1]
  exact physical

theorem previous_row {r : Registry} {before after : State rs} {root focus : Occurrence rs}
    (trace : B4Target.Steps (Step r root) before after) :
    rows before.core focus ⊆ rows after.core focus := by
  intro row member
  obtain ⟨site,atSite,atOut,alias⟩ := exact_row.mp member
  exact exact_row.mpr ⟨site,previous_at trace atSite,atOut,
    GeneralNominalCenteredHeadMatStepTrustedGrowth.aliases
      (GeneralNominalVersionedMixedGrowth234.steps trace).legacy alias⟩

private theorem narrow_scan (l : List α) (p q : α → Bool) (pack : α → List β)
    (widen : ∀ a, p a = true → q a = true) :
    ((l.filter p).flatMap pack).Sublist ((l.filter q).flatMap pack) := by
  induction l with
  | nil => exact .slnil
  | cons a rest ih =>
    cases left : p a <;> cases right : q a
    · simpa [List.filter_cons,left,right] using ih
    · simpa [List.filter_cons,left,right] using ih.trans (List.sublist_append_right _ _)
    · have impossible := widen a left
      rw [right] at impossible
      cases impossible
    · simpa [List.filter_cons,left,right] using ih.append_left (pack a)

/-- An actual finite mixed trace preserves the order and multiplicity
of the original attributed rows as a subsequence. A later merge may
insert an earlier physical site's rows ahead of a surviving one. -/
theorem stable_order {r : Registry} {before after : State rs} {root : Occurrence rs}
    (trace : B4Target.Steps (Step r root) before after) (focus : Occurrence rs) :
    (rows before.core focus).Sublist (rows after.core focus) := by
  classical
  obtain ⟨extra,h⟩ := trace_prefix trace
  unfold rows
  rw [h,List.zipIdx_append,List.filter_append,List.flatMap_append]
  apply List.Sublist.trans _ (List.sublist_append_left _ _)
  apply narrow_scan
  intro row retained
  exact decide_eq_true (GeneralNominalCenteredHeadMatStepTrustedGrowth.aliases
    (GeneralNominalVersionedMixedGrowth234.steps trace).legacy (of_decide_eq_true retained))

end Yulang.GeneralDeclarativeCurrentTrace345
