import Yulang.GeneralVersionedSharingBinderRows313
import Yulang.GeneralNominalVersionedCurrentProjection237

set_option backward.isDefEq.respectTransparency false
/-! The sharing diagnostic supplies actual reads. A point binder is already
fixed by the same read through the inspection bounds; free private binders
cohere by name. Only protected private binders require a separate producer. -/
namespace Yulang.GeneralVersionedSharingBinderTable313
open GeneralNominalCenters GeneralNominalMaterialization GeneralNominalRecursiveInspection
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedFrame231 (binder)
open GeneralNominalAllocation (occurrences)
open GeneralVersionedSharingBinderRows313
open GeneralVersionedAliasHeadWrites312 (pool)
open GeneralVersionedBinderTargets312 (actualName cases_binder point_binding point_in_pool same_fresh_name)
open GeneralFiniteTypedWrites312 (Coherent Protected Holds transitive symmetric)
open CommonNominalFullCarrier (Equivalent Subtype)
open GeneralNominalQueryProvenance183 (headInspection)

def PrivateAgrees (plan : Plan roles) (names : List Nat) (m : Assignment)
    (sharing : GeneralDictionaryHeadSharing220.Holds plan m) : Prop :=
  ∀ use, ∀ present : use ∈ plan.headSchema.variables,
    binder plan use.name = actualName plan use.name →
    actualName plan use.name ∈ pool plan names →
    Equivalent (m (actualName plan use.name)).1 (read plan m sharing use present)

theorem point_agrees {s : State roles} {plan : Plan roles}
    (frame : Frame registry s.core focus key plan)
    (m : Assignment) (valid : Models s m)
    (sharing : GeneralDictionaryHeadSharing220.Holds plan m)
    (tests : Tests plan m) (use : Use) (present : use ∈ plan.headSchema.variables)
    (point : Nat) (one : occurrences plan.packet.bindings use.name = [(point,point)]) :
    Equivalent (m point).1 (read plan m sharing use present) := by
  have agreement := GeneralDictionaryHeadSharing220.agreement_of_holds plan m sharing
  have projection := (GeneralNominalVersionedCurrentProjection237.projection_iff
    plan frame m valid tests).mpr agreement
  have found := point_binding plan use.name point one
  rw [← GeneralDictionaryDefaultProjectionBounds215.head_bindings plan] at found
  obtain ⟨captured,listed,cap⟩ := List.mem_map.mp found
  have fields := Prod.mk.inj cap
  have endpoints := Prod.mk.inj fields.2
  obtain ⟨origin,reported,used⟩ := GeneralNominalCenteredCaptureSchema.many_capture
    plan.packet.context.state _ plan.packet.bounds _ 0 captured listed
  let site : Use := ⟨captured.name,origin,.actual⟩
  have sitePresent : site ∈ plan.headSchema.variables := used
  have siteName : site.name = use.name := fields.1
  have seen := read_present plan m sharing site sitePresent
  have bound := (projection.1 _ (GeneralNominalCaptureAnchors.many_anchored plan.packet.context.state
    _ plan.packet.bounds _ 0 captured listed origin reported)).2 _ seen
  change Subtype (m _).1 _ ∧ Subtype _ (m _).1 at bound
  rw [endpoints.1,endpoints.2] at bound
  exact transitive bound (observations_agree plan m sharing site use sitePresent present siteName)

theorem table {s : State roles} {plan : Plan roles} (frame : Frame registry s.core focus key plan)
    (names : List Nat) (m : Assignment) (valid : Models s m)
    (sharing : GeneralDictionaryHeadSharing220.Holds plan m) (tests : Tests plan m)
    (old : PrivateAgrees plan names m sharing) :
    Coherent (rows plan m sharing) ∧ Protected (rows plan m sharing) (pool plan names) m := by
  have fixed : Protected (rows plan m sharing) (pool plan names) m := by
    intro row placed hit
    obtain ⟨use,present,rfl⟩ := (row_iff ..).mp placed
    have input := GeneralNominalHeadSchemaNames186.head_input plan use present
    change Equivalent (m (binder plan use.name)).1 (read plan m sharing use present)
    rcases cases_binder plan use.name input with ⟨point,found,eq⟩|fresh
    · rw [eq]
      exact point_agrees frame m valid sharing tests use present point found
    · rw [fresh]
      exact old use present fresh (fresh ▸ hit)
  refine ⟨?_,fixed⟩
  intro a am b bm equal
  by_cases inside : a.1 ∈ pool plan names
  · have x := fixed a am inside
    have y := fixed b bm (equal ▸ inside)
    unfold Holds at x y
    rw [equal] at x
    exact transitive (symmetric x) y
  · obtain ⟨first,firstPresent,rfl⟩ := (row_iff ..).mp am
    obtain ⟨last,lastPresent,rfl⟩ := (row_iff ..).mp bm
    have privateTarget (use : Use) (member : use ∈ plan.headSchema.variables)
        (notIn : binder plan use.name ∉ pool plan names) : binder plan use.name = actualName plan use.name := by
      rcases cases_binder plan use.name (GeneralNominalHeadSchemaNames186.head_input plan use member) with ⟨point,one,eq⟩|fresh
      · exact False.elim (notIn (eq.symm ▸ point_in_pool plan names use.name point one))
      · exact fresh
    have firstNew := privateTarget first firstPresent inside
    have lastNew := privateTarget last lastPresent (fun h => inside (equal.symm ▸ h))
    exact observations_agree plan m sharing first last firstPresent lastPresent
      (same_fresh_name plan (firstNew.symm.trans (equal.trans lastNew)))

end Yulang.GeneralVersionedSharingBinderTable313
