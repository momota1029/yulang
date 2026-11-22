import Yulang.GeneralDeclarativeCommitPosition344

namespace Yulang.GeneralDeclarativeLedger344
open GeneralWhereVersionInstall317 (Journal InstallStep Models install emitted)
open GeneralNominalCenters (Plan Site)
open GeneralDeclarations (Registry)
open GeneralNominalCommonBridge (Assignment)
open GeneralWhereVersionSemantics317 (Holds)

/-- A weaker raw observation than choosing a plan: previously recorded
ordinal stamps and centered site positions are kept. This admits
mixed reobservation that may change context without changing the lists. -/
structure Grows {rs : Roles.RoleDecls} (before after : Journal rs) : Prop where
  journal : ∃ tail, after.versionedWhere = before.versionedWhere ++ tail
  sites : ∃ tail, after.mixed.core.sites = before.mixed.core.sites ++ tail

theorem refl (j : Journal rs) : Grows j j :=
  ⟨⟨[],by simp⟩,⟨[],by simp⟩⟩

theorem trans {a b c : Journal rs} (one : Grows a b) (two : Grows b c) : Grows a c := by
  obtain ⟨x,jx⟩ := one.journal
  obtain ⟨y,jy⟩ := two.journal
  obtain ⟨s,sx⟩ := one.sites
  obtain ⟨t,sy⟩ := two.sites
  constructor
  · exact ⟨x++y,by rw [jy,jx,List.append_assoc]⟩
  · exact ⟨s++t,by rw [sy,sx,List.append_assoc]⟩

theorem step {r : Registry} {a b : Journal rs} (done : InstallStep r a b) : Grows a b := by
  cases done with
  | whereRow ctx p checked frame selected compat refinement interpretation fit =>
    exact ⟨⟨[p],rfl⟩,⟨emitted p,rfl⟩⟩

theorem stamped {a b : Journal rs} (growth : Grows a b) {idx : Nat} {p : Plan rs}
    (stamp : a.versionedWhere[idx]? = some p) : b.versionedWhere[idx]? = some p := by
  obtain ⟨tail,exactList⟩ := growth.journal
  have size := (List.getElem?_eq_some_iff.mp stamp).1
  rw [exactList,List.getElem?_append_left size]
  exact stamp

theorem site_kept {a b : Journal rs} (growth : Grows a b) {idx : Nat} {s : Site rs}
    (stamp : a.mixed.core.sites[idx]? = some s) : b.mixed.core.sites[idx]? = some s := by
  obtain ⟨tail,exactList⟩ := growth.sites
  have size := (List.getElem?_eq_some_iff.mp stamp).1
  rw [exactList,List.getElem?_append_left size]
  exact stamp

/-- Archived entries keep their own typed historical rows in every
later model. This by itself gives no authority to use the old row
as the current observation or to assign a latest-wins rule. -/
theorem later_model {a b : Journal rs} (growth : Grows a b) {idx : Nat} {p : Plan rs}
    (stamp : a.versionedWhere[idx]? = some p) (m : Assignment) (fit : Models b m) :
    Holds p m ∧ GeneralNominalVersionedEffects231.ClassEffects b.mixed.core p.packet.site.occurrence p m :=
  fit.2 p (List.mem_of_getElem? (stamped growth stamp))

end Yulang.GeneralDeclarativeLedger344
