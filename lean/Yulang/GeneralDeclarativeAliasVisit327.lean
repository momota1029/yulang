import Yulang.GeneralDeclarativeInspect321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeAliasVisit327
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeLowerKnown321 (Alias alias_refl alias_symm)
open GeneralDeclarativeGraphRows321 (observed structural)
open GeneralDeclarativeK2Alias321 (AliasCycle cycle_alias)
open GeneralDeclarativeInspect321 (Visit PatternK2)

theorem structural_name {s : State} (link : Alias s fresh old) (seen : structural s old shape) :
    structural s fresh shape := by
  obtain ⟨source,there,view⟩ := seen
  exact ⟨source,.trans link there,view⟩

/-- The canonical visible-path judgment can move its root along an
ordinary equality. A root visit moves the visited name itself;
proper descent keeps the same observed child. -/
theorem visit {s : State} (link : Alias s fresh old)
    (past : Visit (structural s) old code site) :
    ∃ newSite, Visit (structural s) fresh code newSite ∧ Alias s newSite site := by
  cases past with
  | here visible => exact ⟨_,.here visible,link⟩
  | primitive view pattern arg below =>
    exact ⟨_,.primitive (structural_name link view) pattern arg below,alias_refl _⟩
  | nominal view pattern arg below =>
    exact ⟨_,.nominal (structural_name link view) pattern arg below,alias_refl _⟩
  | field view named pattern below =>
    exact ⟨_,.field (structural_name link view) named pattern below,alias_refl _⟩
  | variant view below =>
    exact ⟨_,.variant (structural_name link view) below,alias_refl _⟩

theorem pattern {s : State} (link : Alias s fresh old) :
    PatternK2 s fresh code ↔ PatternK2 s old code := by
  have forward {a b : Nat} (any : Alias s a b) (known : PatternK2 s b code) : PatternK2 s a code := by
    obtain ⟨_,was,cycled⟩ := known
    obtain ⟨site,now,equal⟩ := visit any was
    exact ⟨site,now,cycle_alias equal cycled⟩
  exact ⟨forward (alias_symm link),forward link⟩

end Yulang.GeneralDeclarativeAliasVisit327
