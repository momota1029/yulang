import Yulang.GeneralWhereVersionInstall317
import Yulang.GeneralWhereOriginInstall318
import Yulang.GeneralDeclarativeOrderedProjection343

namespace Yulang.GeneralDeclarativeCommitSuffix344
open GeneralWhereVersionInstall317 (Journal install installCore emitted ordered Models InstallStep)
open GeneralWhereVersionCompiler317 (children)
open GeneralWhereVersionSemantics317 (Holds)
open GeneralNominalCenters (Plan Site)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarations (Registry)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalSaturationState (Generated)

/-- The transaction suffix is literal, before position-based logical
renaming. The stamp is a list position, not an implicit latest-wins rule. -/
structure Receipt {rs : Roles.RoleDecls} (r : Registry) (before after : Journal rs)
    (p : Plan rs) (m : Assignment) : Prop where
  frame : Frame (Compiled r) before.mixed.core p.packet.site.occurrence p.packet.declaration.id p
  stamp : after.versionedWhere[before.versionedWhere.length]? = some p
  sites : after.mixed.core.sites = before.mixed.core.sites ++ emitted p
  rawSites : after.mixed.core.erased.current.sites =
    before.mixed.core.erased.current.sites ++ (emitted p).map Site.observed
  edges : after.mixed.core.erased.current.edges = before.mixed.core.erased.current.edges ++
    (children p).map (fun d => (p.packet.site.occurrence,d))
  compilerOrder : (emitted p).map Site.occurrence = children p
  typed : Holds p m
  effects : GeneralNominalVersionedEffects231.ClassEffects after.mixed.core p.packet.site.occurrence p m

theorem from_step {rs : Roles.RoleDecls} {r : Registry} {before after : Journal rs}
    (step : InstallStep r before after) (m : Assignment) (valid : Models after m) :
    ∃ ctx p, after = install before ctx p ∧ Receipt r before after p m := by
  cases step with
  | whereRow ctx p checked frame selected compatible refined interpretation feasible =>
    have h : p ∈ (install before ctx p).versionedWhere := List.mem_append_right _ List.mem_cons_self
    have stamp : (install before ctx p).versionedWhere[before.versionedWhere.length]? = some p := by
      change (before.versionedWhere ++ [p])[before.versionedWhere.length]? = some p
      rw [List.getElem?_append_right (Nat.le_refl _),Nat.sub_self]
      rfl
    exact ⟨ctx,p,rfl,frame,stamp,rfl,rfl,rfl,ordered p,(valid.2 p h).1,(valid.2 p h).2⟩

theorem child_at {rs : Roles.RoleDecls} {r : Registry} {before after : Journal rs}
    {p : Plan rs} {m : Assignment} (receipt : Receipt r before after p m)
    {i : Nat} {s : Site rs} (located : (emitted p)[i]? = some s) :
    after.mixed.core.sites[before.mixed.core.sites.length+i]? = some s ∧
    (children p)[i]? = some s.occurrence := by
  constructor
  · rw [receipt.sites,List.getElem?_append_right (by omega),Nat.add_sub_cancel_left]
    exact located
  · rw [← receipt.compilerOrder,List.getElem?_map,located]
    rfl

end Yulang.GeneralDeclarativeCommitSuffix344
