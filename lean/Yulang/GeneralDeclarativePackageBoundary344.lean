import Yulang.GeneralDeclarativeCommitPackage344

namespace Yulang.GeneralDeclarativePackageBoundary344
open GeneralNominalCenters (Plan)
open GeneralDeclarations (Registry)
open GeneralNominalCommonBridge (Assignment)
open GeneralWhereVersionInstall317 (Journal InstallStep install Models)
open GeneralDeclarativeCommitPackage344 (Witness from_install)
open GeneralNominalCenteredHeadMatEffects (Ready)

/-- A real committed stamp determines the roles in its compiled
registry. No registry-role equality must be assumed separately. -/
theorem stamped_roles {r : Registry} {before after : Journal rs} (step : InstallStep r before after)
    {p : Plan rs} (stamp : after.versionedWhere[before.versionedWhere.length]? = some p) :
    p.packet.registry.roles = rs := by
  cases step with
  | whereRow ctx recorded checked frame selected compatible refinement interpretation feasible =>
    change (before.versionedWhere ++ [recorded])[before.versionedWhere.length]? = some p at stamp
    rw [List.getElem?_append_right (Nat.le_refl _),Nat.sub_self] at stamp
    have eq : recorded = p := Option.some.inj stamp
    subst p
    rw [frame.registry_eq]
    exact checked.1

theorem actual {r : Registry} {before : Journal rs} {ctx : GeneralNominalCandidates.Context}
    {p : Plan rs} (step : InstallStep r before (install before ctx p))
    (m : Assignment) (fit : Models (install before ctx p) m)
    (protect : List Nat)
    (ready : Ready (install before ctx p).mixed.core p.packet.site.occurrence p) :
    ∃ prepared s ports whereRows rootRows n,
      Witness (install before ctx p) p m n protect prepared s ports whereRows rootRows := by
  have recorded := GeneralDeclarativeCommitPosition344.current_stamp r before ctx p step m fit
  exact from_install r before ctx p step m fit protect (stamped_roles step recorded.stamp) ready

theorem adds_one {r : Registry} {before after : Journal rs} (step : InstallStep r before after) :
    after.versionedWhere.length = before.versionedWhere.length + 1 := by
  cases step
  simp [install]

theorem no_unchanged_stamp {r : Registry} {before after : Journal rs}
    (unchanged : after.versionedWhere.length = before.versionedWhere.length) :
    ¬ InstallStep r before after := by
  intro step
  have added := adds_one step
  omega

end Yulang.GeneralDeclarativePackageBoundary344
