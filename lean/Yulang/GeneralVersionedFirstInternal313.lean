import Yulang.GeneralVersionedCompoundRows313
import Yulang.GeneralNominalFiniteBracket

set_option backward.isDefEq.respectTransparency false
/-! First-install compound where rows are either fixed identities or
independent free targets; the true class and every RHS read remain fixed. -/
namespace Yulang.GeneralVersionedFirstInternal313
open GeneralNominalCenters GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedTraceSupport237 (Reachable)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralVersionedFirstHead313 (names)
open GeneralVersionedPrivateWriteNames313 (excludes)
open GeneralVersionedCompoundRows313
open GeneralVersionedRootWrites312 (inner internalRows)
open GeneralVersionedJointWrites312 (rhs inputNames protect equations rhs_preserved)
open GeneralNominalCommonBridge (Assignment)
open GeneralFiniteTypedWrites312 (Holds reflexive symmetric transitive)
open CommonNominalFullCarrier (Equivalent Ty)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open GeneralNominalVersionedMixedMaterialization237 (Residual)

theorem taut_reads (p : Plan roles) (e : GeneralNominalCenteredHeadMatSchemas.Equation) (taut : Taut p e) :
    e.target ∈ inputNames p e := by
  apply Classical.byContradiction
  intro absent
  let a : Assignment := fun _ => (.base .int,Common.rowEmpty)
  let b : Assignment := fun n => if n = e.target then (.base .bool,Common.rowEmpty) else a n
  have readEq := rhs_preserved p a b e (by
    intro n member
    have ne : n ≠ e.target := fun eq => absent (eq ▸ member)
    simp [b,ne])
  have left : Equivalent (.base .int) (rhs p a e) := taut a
  have right : Equivalent (.base .bool) (rhs p b e) := by
    simpa only [GeneralNominalCenteredHeadMatSchemas.Equation.Holds,rhs,b,ite_true] using taut b
  rw [← readEq] at right
  have equal := transitive left (symmetric right)
  have head := GeneralNominalFiniteBracket.subtype_head
    (.scalar .int) (.scalar .bool) Fin.elim0 Fin.elim0 equal.1
  cases head

theorem taut_protected {s : State roles} {e : Effect roles}
    {q : GeneralNominalCenteredHeadMatSchemas.Equation}
    (listed : q ∈ inner e.plan) (taut : Taut e.plan q) :
    q.target ∈ protect s e (names s) := by
  have all : q ∈ equations e.plan := by
    rw [GeneralVersionedRootWrites312.separates]
    exact List.mem_append_right _ listed
  have reads : q.target ∈ (equations e.plan).flatMap (inputNames e.plan) :=
    List.mem_flatMap.mpr ⟨q,all,taut_reads e.plan q taut⟩
  simp [protect,reads]

theorem cell_free {s : State roles} {e : Effect roles}
    (actual : Reachable registry root s) (empty : s.plans = [])
    (frame : Frame (Compiled registry) s.core focus key e.plan)
    {q : GeneralNominalCenteredHeadMatSchemas.Equation}
    (cell : Cell e.plan q) :
    q.target ∉ protect s e (names s) := by
  obtain ⟨clause,_,pos,kind,pat,which,_,_,target,_⟩ := cell
  intro present
  have safe := GeneralVersionedFirstFootprint313.protected_names actual empty frame _ present
  rw [target] at safe
  apply excludes e.plan clause.id pos kind _ safe
  rcases which with rfl|rfl|rfl <;> decide

theorem internal {s : State roles} {e : Effect roles}
    (actual : Reachable registry root s) (empty : s.plans = [])
    (frame : Frame (Compiled registry) s.core focus key e.plan)
    (outputs : ForwardedResult e.plan.packet.declaration) :
    GeneralVersionedSelectedJointWrites312.InternalReady s e (names s) := by
  intro m _ _ _ _
  constructor
  · intro a aMem b bMem same free
    obtain ⟨one,ho,rfl⟩ := List.mem_map.mp aMem
    obtain ⟨two,ht,rfl⟩ := List.mem_map.mp bMem
    have fromOne : Cell e.plan one := (classifies e.plan outputs _ ho).resolve_left
      (fun taut => free (taut_protected ho taut))
    have fromTwo : Cell e.plan two := (classifies e.plan outputs _ ht).resolve_left
      (fun taut => free (same.symm ▸ taut_protected ht taut))
    have exactEq := coherent_address fromOne fromTwo same
    rw [exactEq]
    exact reflexive _
  · intro row present protectedName
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp present
    rcases classifies e.plan outputs q hq with taut|free
    · exact taut m
    · exact False.elim (cell_free actual empty frame free protectedName)


theorem sites_covered {s : State roles} (actual : Reachable registry root s) (empty : s.plans = []) :
    GeneralNominalVersionedTraceSiteSupport237.Covered s (names s) := by
  obtain ⟨first,⟨legacy,⟨ctx,labels,formation,point,ground,coverage,rfl⟩,rfl⟩,steps⟩ := actual
  intro site member k inside
  have sourceEq : s.core.erased.source = ctx := GeneralNominalVersionedMixedGrowth234.steps_source steps
  rcases (GeneralVersionedSiteOrigins312.trace steps).origin site member with same|⟨p,recorded,_⟩
  · subst site
    obtain ⟨block,seen,hits⟩ := List.mem_flatten.mp inside
    obtain ⟨index,rfl⟩ := List.mem_ofFn.mp seen
    change k ∈ [(root.demand.arguments index).1,(root.demand.arguments index).2,(rootSite ctx.state.seed root).center index] at hits
    rw [point_center ctx.state.seed root index (point index)] at hits
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hits
    change k ∈ GeneralNominalState.sources s.core.erased.source.state
    rw [sourceEq]
    rcases hits with e|e|e <;> rw [e]
    · exact (formation.linked.1 index).1
    · exact (formation.linked.1 index).2
    · exact (formation.linked.1 index).1
  · rw [empty] at recorded
    cases recorded

theorem joint {s : State roles} {e : Effect roles}
    (checked : (boundary roles).Checked registry) (actual : Reachable registry root s)
    (empty : s.plans = [])
    (pick : Local registry s e.plan.packet.site.occurrence (.selected e.plan.packet.declaration.id children))
    (registryEq : e.registry = Compiled registry) (snapshot : e.snapshot = s.core)
    (inhabited : ∃ m, Models s m)
    (outputs : ForwardedResult e.plan.packet.declaration) :
    ∃ m, Residual s e m := by
  have frame : Frame (Compiled registry) s.core e.plan.packet.site.occurrence e.plan.packet.declaration.id e.plan :=
    registryEq ▸ snapshot ▸ e.frame
  exact GeneralVersionedSelectedJointWrites312.joint_from_internal checked actual pick registryEq snapshot
    (GeneralVersionedBeforeFirstInstall313.support_initial actual empty) (sites_covered actual empty)
    (GeneralVersionedFirstFootprint313.class_aggregate_free actual empty frame)
    (GeneralVersionedFirstGroundHead313.head checked actual empty pick frame inhabited)
    (internal actual empty frame outputs)

theorem installable {s : State roles} {e : Effect roles}
    (checked : (boundary roles).Checked registry) (actual : Reachable registry root s)
    (empty : s.plans = [])
    (pick : Local registry s e.plan.packet.site.occurrence (.selected e.plan.packet.declaration.id children))
    (registryEq : e.registry = Compiled registry) (snapshot : e.snapshot = s.core)
    (inhabited : ∃ m, Models s m)
    (outputs : ForwardedResult e.plan.packet.declaration) :
    GeneralNominalVersionedMixedKernel234.Installable (Compiled registry) s e := by
  refine (GeneralNominalVersionedMixedMaterialization237.source_installable_iff checked actual pick registryEq snapshot).mpr
    ⟨?_,joint checked actual empty pick registryEq snapshot inhabited outputs⟩
  intro prior recorded _
  rw [(GeneralNominalVersionedMixedChoiceHistory236.reachable actual).2,empty] at recorded
  cases recorded

end Yulang.GeneralVersionedFirstInternal313
