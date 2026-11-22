import Yulang.GeneralDeclarativeTxnEffects348
import Yulang.GeneralDeclarativeCommitSuffix344
import Yulang.GeneralWhereOriginInstall318

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeTxnReceipt348
open GeneralDeclarations (Registry)
open GeneralNominalCenters (Plan Site)
open GeneralNominalCandidates (Context)
open GeneralWhereVersionInstall317 (Journal Models install emitted ordered)
open GeneralWhereVersionCompiler317 (children)
open GeneralDeclarativeWhereTxn348 (Txn)
open GeneralDeclarativeCommitSuffix344 (Receipt child_at)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalSaturationState (Generated)

theorem receipt {r : Registry} {j : Journal rs} {ctx : Context} {p : Plan rs}
    (proof : Txn r j ctx p) (m : Assignment) (fit : Models (install j ctx p) m) :
    Receipt r j (install j ctx p) p m := by
  have present : p ∈ (install j ctx p).versionedWhere := List.mem_append_right _ List.mem_cons_self
  have atStamp : (install j ctx p).versionedWhere[j.versionedWhere.length]? = some p := by
    change (j.versionedWhere ++ [p])[j.versionedWhere.length]? = some p
    rw [List.getElem?_append_right (Nat.le_refl _),Nat.sub_self]
    rfl
  exact ⟨proof.frame,atStamp,rfl,rfl,rfl,ordered p,(fit.2 p present).1,(fit.2 p present).2⟩

/-- Bind the declared current frontier to a specific appended suffix.
Historic aliases by owner and cumulative Generated membership cannot
replace this positional receipt. -/
theorem exact_position {r : Registry} {j : Journal rs} {ctx : Context} {p : Plan rs}
    (proof : Txn r j ctx p) (m : Assignment) (fit : Models (install j ctx p) m)
    {i : Nat} {s : Site rs} (located : (emitted p)[i]? = some s) :
    (install j ctx p).mixed.core.sites[j.mixed.core.sites.length+i]? = some s ∧
    (install j ctx p).mixed.core.erased.current.sites[j.mixed.core.erased.current.sites.length+i]? =
      some s.observed ∧ (children p)[i]? = some s.occurrence := by
  obtain ⟨atCenter,atCompiler⟩ := child_at (receipt proof m fit) located
  refine ⟨atCenter,?_,atCompiler⟩
  rw [(receipt proof m fit).rawSites,List.getElem?_append_right (by omega),Nat.add_sub_cancel_left,
    List.getElem?_map,located]
  rfl

theorem keeps_prior {j : Journal rs} {ctx : Context} {p : Plan rs}
    {i : Nat} {s : Site rs} (stored : j.mixed.core.sites[i]? = some s) :
    (install j ctx p).mixed.core.sites[i]? = some s := by
  change (j.mixed.core.sites ++ emitted p)[i]? = _
  rwa [List.getElem?_append_left (List.getElem?_eq_some_iff.mp stored).1]

end Yulang.GeneralDeclarativeTxnReceipt348
