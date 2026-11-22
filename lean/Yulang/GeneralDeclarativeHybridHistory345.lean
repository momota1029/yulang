import Yulang.GeneralDeclarativeHybridTrace345
import Yulang.GeneralDeclarativeCurrentTrace345

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeHybridHistory345
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralWhereVersionInstall317 (Journal InstallStep emitted)
open GeneralNominalCenters (Plan)
open GeneralDeclarativeHybridTrace345 (Walk)
open GeneralDeclarativeCurrentTrace345 (at_prefix)

theorem both_prefixes {r : Registry} {root : Occurrence rs} {first final : Journal rs}
    (trace : Walk r root first final) :
    (∃ stampTail, final.versionedWhere = first.versionedWhere ++ stampTail) ∧
    (∃ siteTail, final.mixed.core.erased.current.sites =
      first.mixed.core.erased.current.sites ++ siteTail) := by
  induction trace with
  | refl =>
    exact ⟨⟨[],(List.append_nil _).symm⟩,⟨[],(List.append_nil _).symm⟩⟩
  | native _ step ih =>
    obtain ⟨⟨stamps,a⟩,⟨sites,b⟩⟩ := ih
    obtain ⟨_,_,real⟩ := step
    obtain ⟨new,c⟩ := at_prefix real
    exact ⟨⟨stamps,a⟩,⟨sites ++ new,by rw [c,b,List.append_assoc]⟩⟩
  | isolated _ step ih =>
    obtain ⟨⟨stamps,a⟩,⟨sites,b⟩⟩ := ih
    cases step with
    | whereRow ctx p _ _ _ _ _ _ _ =>
      refine ⟨⟨stamps ++ [p],?_⟩,⟨sites ++ (emitted p).map GeneralNominalCenters.Site.observed,?_⟩⟩
      · change _ ++ [p] = _
        rw [a,List.append_assoc]
      · change _ ++ (emitted p).map GeneralNominalCenters.Site.observed = _
        rw [b,List.append_assoc]

theorem positions {r : Registry} {root : Occurrence rs} {first final : Journal rs}
    (trace : Walk r root first final) :
    (∀ (i : Nat) (p : Plan rs), first.versionedWhere[i]? = some p →
      final.versionedWhere[i]? = some p) ∧
    (∀ (i : Nat) (s : GeneralNominalDemandMerging.Site rs),
      first.mixed.core.erased.current.sites[i]? = some s →
      final.mixed.core.erased.current.sites[i]? = some s) := by
  obtain ⟨⟨stamps,a⟩,⟨sites,b⟩⟩ := both_prefixes trace
  constructor
  · intro i p old
    rw [a,List.getElem?_append_left (List.getElem?_eq_some_iff.mp old).1]
    exact old
  · intro i s old
    rw [b,List.getElem?_append_left (List.getElem?_eq_some_iff.mp old).1]
    exact old

end Yulang.GeneralDeclarativeHybridHistory345
