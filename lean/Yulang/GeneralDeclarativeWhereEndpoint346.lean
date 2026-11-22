import Yulang.GeneralDeclarativeWhereRawTicket346
import Yulang.GeneralDeclarativeCommitPosition344
import Yulang.GeneralWhereOriginConfig318

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWhereEndpoint346
open GeneralDeclarations (Registry)
open GeneralNominalCenters (Plan Site)
open GeneralWhereOriginDelta318 (Cell)
open GeneralWhereVersionInstall317 (Journal InstallStep Models install emitted)
open GeneralWhereVersionCompiler317 (child children schema)
open GeneralDeclarativeCommitPosition344 (clauses signature current_stamp)
open GeneralDeclarativeCommitSuffix344 (child_at)
open GeneralWhereOriginSchema318 (pick)
open GeneralVersionedEndpointAddress315 (atCell)
open GeneralNominalVersionedPlans231 (variables)
open GeneralNominalCommonBridge (Assignment)
open GeneralWhereOriginDescriptor318 (argument)

structure At {rs : Roles.RoleDecls} (before after : Journal rs) (p : Plan rs) (c : Cell p)
    (ord : Nat) (site : Site rs) : Prop where
  stamp : after.versionedWhere[before.versionedWhere.length]? = some p
  physical : after.mixed.core.sites[before.mixed.core.sites.length+ord]? = some site
  emittedHere : (emitted p)[ord]? = some site
  childHere : (children p)[ord]? = some site.occurrence
  canonical : ∃ src, (clauses p)[ord]? = some src ∧ src.val = c.clause
  clauseRole : site.occurrence.demand.role = c.clause.role
  inputHere : ∃ i : Fin (rs site.occurrence.demand.role).arity,
    i.val = c.index ∧ pick c.side (site.occurrence.demand.arguments i) = c.row.target
  written : c.row ∈ (schema p).equations

theorem from_step {r : Registry} {before : Journal rs} {ctx : GeneralNominalCandidates.Context}
    {p : Plan rs} (step : InstallStep r before (install before ctx p))
    (c : Cell p) (m : Assignment) (valid : Models (install before ctx p) m) :
    ∃ ord site, At before (install before ctx p) p c ord site ∧ c.row.Holds (variables p m) m := by
  have canonical : c.clause ∈ GeneralCanonicalChildOrder.canonicalRequirements p.packet.declaration.requirements :=
    (GeneralCanonicalChildOrder.canonicalRequirements_perm _).mem_iff.mp c.listed
  let annot : {q // q ∈ GeneralCanonicalChildOrder.canonicalRequirements p.packet.declaration.requirements} :=
    ⟨c.clause,canonical⟩
  obtain ⟨ord,located⟩ := List.mem_iff_getElem?.mp (show annot ∈ clauses p from List.mem_attach ..)
  let site := child p annot.val (signature p annot)
  have selected : (emitted p)[ord]? = some site := by
    change ((clauses p).map (fun q => child p q.val (signature p q)))[ord]? = some site
    rw [List.getElem?_map,located]; rfl
  have formed := child_at (current_stamp r before ctx p step m valid) selected
  have whereReceipt := current_stamp r before ctx p step m valid
  have stampMember : p ∈ (install before ctx p).versionedWhere :=
    List.mem_iff_getElem?.mpr ⟨_,whereReceipt.stamp⟩
  refine ⟨ord,site,⟨whereReceipt.stamp,formed.1,selected,formed.2,⟨annot,located,rfl⟩,rfl,?_,c.written.1⟩,
    (valid.2 p stampMember).1.rows _ c.written.1⟩
  have bounded := (List.getElem?_eq_some_iff.mp c.located).1
  have sig := signature p annot
  let i : Fin (rs c.clause.role).arity := ⟨c.index,by rw [← sig.1]; exact bounded⟩
  refine ⟨i,rfl,?_⟩
  change pick c.side ((child p c.clause sig).occurrence.demand.arguments i) = c.row.target
  rw [argument sig i c.located c.compound c.translated]
  change pick c.side (atCell p .lower c.clause.id c.index c.expression,
      atCell p .upper c.clause.id c.index c.expression) = atCell p c.side c.clause.id c.index c.expression
  cases c.side <;> rfl

end Yulang.GeneralDeclarativeWhereEndpoint346
