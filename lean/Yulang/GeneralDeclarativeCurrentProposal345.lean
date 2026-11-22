import Yulang.GeneralDeclarativeCurrentBodies345
import Yulang.GeneralDeclarativeStoppedLeaf340
import Yulang.GeneralDeclarativeCurrentSnapshot345

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeCurrentProposal345
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalCenters (Plan)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary checked_compiled)
open GeneralNominalCenteredHeadAllocEncoding (registry)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedMixedKernel234 (Committed Step Installable)
open GeneralNominalSaturationState (Generated)
open GeneralDeclarativeCurrentJoint345 (Block Attributed)
open GeneralDeclarativeCurrentOrder345 (rows outputs exact_row)
open GeneralDeclarativeStoppedOrder339 (complete_known checked_order member_authored)
open GeneralDeclarativeStoppedLeaf340 (receipt_holds committed)
open GeneralDeclarativeCurrentPosition345 (align enrich)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedFrame231 (children)

theorem actual_current {r : Registry} {root : Occurrence rs} {final : State rs} {e : Effect rs}
    (checked : (boundary rs).Checked r)
    (reached : B4TargetV8.Reachable (boundary rs) r root final)
    (sameRegistry : e.registry = registry r) (sameSnapshot : e.snapshot = final.core)
    (accepted : Committed final e.plan)
    (m : Assignment) (fit : Models final m) :
    ∃ equations, Block r root final e equations ∧
      (∀ equation ∈ equations,Holds m equation) ∧
      (∀ child ∈ children e.plan.packet,
        (e.plan.packet.site.occurrence,child) ∈ final.core.erased.current.edges) := by
  have frame : Frame (registry r) final.core e.plan.packet.site.occurrence e.plan.packet.declaration.id e.plan := by
    rw [← sameRegistry,← sameSnapshot]
    exact e.frame
  have ready := GeneralNominalVersionedMixedReady235.ready checked reached frame
  obtain ⟨equations,ran⟩ := complete_known (effect := e) ready (fun _ h => h)
  obtain ⟨all,_⟩ := checked_order (fun _ h => h) ran
  have current := (accepted.1 m fit).2
  have valid : ∀ term ∈ equations,Holds m term := by
    intro term present
    obtain ⟨_,_,receipt⟩ := member_authored all present
    exact receipt_holds current receipt
  have source := GeneralNominalVersionedMixedRoles235.reachable checked reached
  rw [← outputs] at all
  refine ⟨equations,enrich (align all) ?_,valid,accepted.2⟩
  intro row member eq receipt
  obtain ⟨site,atSite,atOut,alias⟩ := exact_row.mp member
  obtain ⟨_,_,written⟩ := receipt.authored
  exact ⟨receipt,GeneralDeclarativeStoppedOutput339.fixed_target written,site,atSite,atOut,alias,
    source.raw _ (List.mem_iff_getElem?.mpr ⟨_,atSite⟩)⟩

/-- No journal membership premise. The conditional stop theorem still
requires an independently installable current proposal; returned-state
stability alone must not conjure a full packet. -/
theorem stopped_current {r : Registry} {root : Occurrence rs} {final : State rs} {e : Effect rs}
    (checked : (boundary rs).Checked r)
    (reached : B4TargetV8.Reachable (boundary rs) r root final)
    (stopped : ∀ next, ¬ Step (registry r) root final next)
    (generated : Generated final.core.erased.current root e.plan.packet.site.occurrence)
    (enabled : Installable (registry r) final e)
    (m : Assignment) (fit : Models final m) :
    ∃ equations, Block r root final e equations ∧
      (∀ equation ∈ equations,Holds m equation) ∧
      (∀ child ∈ children e.plan.packet,
        (e.plan.packet.site.occurrence,child) ∈ final.core.erased.current.edges) :=
  actual_current checked reached enabled.registry_eq enabled.snapshot_eq
    (committed stopped generated enabled) m fit

end Yulang.GeneralDeclarativeCurrentProposal345
