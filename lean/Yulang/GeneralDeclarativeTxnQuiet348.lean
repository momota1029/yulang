import Yulang.GeneralDeclarativeTxnHistory348

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeTxnQuiet348
open GeneralDeclarations (Registry)
open GeneralNominalCenters (Plan Site)
open GeneralNominalCandidates (Context)
open GeneralNominalReobservationSteps (Revision)
open GeneralWhereVersionInstall317 (Journal Models install emitted)
open GeneralWhereOriginSuccessor318 (SilentChildren)
open GeneralWhereOriginSupport318 (journalSources)
open GeneralDeclarativeWhereTxn348 (Txn)
open GeneralDeclarativeTxnObserve348 (refresh revise)
open GeneralDeclarativeTxnTrace348 (Step)
open GeneralNominalCenteredHeadOutputs (requests)
open GeneralNominalCenteredHeadMatEffects (Ready)
open GeneralNominalVersionedEffects231 (class_effects_iff)
open GeneralNominalCommonBridge (Assignment)

inductive QuietStep (r : Registry) (keep : List Nat) : Journal rs → Journal rs → Prop
  | add {j} (ctx : Context) (p : Plan rs) :
      Txn r j ctx p → SilentChildren p → keep ⊆ journalSources j → QuietStep r keep j (install j ctx p)
  | see {j} (ctx : Context) :
      GeneralNominalVersionedMixedObservations233.Refresh j.mixed ctx →
      QuietStep r keep j (refresh j ctx)
  | reviseNow {j} (revision : Revision j.mixed.core.erased.current) :
      GeneralNominalVersionedMixedObservations233.Reobserve j.mixed revision →
      GeneralNominalReobservationSteps.Improves revision → QuietStep r keep j (revise j revision)

theorem forget {a b : Journal rs} (hop : QuietStep r keep a b) : Step r keep a b := by
  cases hop with
  | add ctx p t _ stable => exact .transaction ctx p t stable
  | see ctx h => exact .observe ctx h
  | reviseNow re seen better => exact .reobserve re seen better

theorem forget_path {a b : Journal rs} (path : B4Target.Steps (QuietStep r keep) a b) :
    B4Target.Steps (Step r keep) a b := by
  induction path with
  | refl => exact .refl
  | tail _ next ih => exact .tail ih (forget next)

private theorem literal_same {a b : GeneralNominalCenteredSteps.State rs}
    (sites : a.erased.current.sites = b.erased.current.sites)
    (aliases : a.erased.current.aliases = b.erased.current.aliases) (focus) :
    requests a focus = requests b focus := by
  classical
  unfold requests
  have guards : (fun (s : GeneralNominalDemandMerging.Site rs) =>
      decide (GeneralNominalSaturationState.Alias a.erased.current focus.identity s.occurrence.identity)) =
    (fun (s : GeneralNominalDemandMerging.Site rs) =>
      decide (GeneralNominalSaturationState.Alias b.erased.current focus.identity s.occurrence.identity)) := by
    funext s
    have copies : GeneralNominalSaturationState.Alias a.erased.current focus.identity s.occurrence.identity ↔
        GeneralNominalSaturationState.Alias b.erased.current focus.identity s.occurrence.identity :=
      ⟨GeneralWhereOriginSuccessor318.alias_copy aliases,GeneralWhereOriginSuccessor318.alias_copy aliases.symm⟩
    by_cases h : GeneralNominalSaturationState.Alias a.erased.current focus.identity s.occurrence.identity
    · rw [decide_eq_true h,decide_eq_true (copies.mp h)]
    · have no : ¬ GeneralNominalSaturationState.Alias b.erased.current focus.identity s.occurrence.identity := fun t => h (copies.mpr t)
      rw [decide_eq_false h,decide_eq_false no]
  rw [sites,guards]

theorem preserves {a b : Journal rs} (hop : QuietStep r keep a b) (focus) :
    requests b.mixed.core focus = requests a.mixed.core focus := by
  cases hop with
  | add ctx p _ silent _ => exact GeneralDeclarativeTxnEffects348.literal_requests _ ctx p silent focus
  | see ctx _ => exact literal_same (a := (refresh a ctx).mixed.core) (b := a.mixed.core) rfl rfl focus
  | reviseNow re _ _ => exact literal_same (a := (revise a re).mixed.core) (b := a.mixed.core) rfl rfl focus

theorem requests_after {a b : Journal rs} (path : B4Target.Steps (QuietStep r keep) a b) (focus) :
    requests b.mixed.core focus = requests a.mixed.core focus := by
  induction path with
  | refl => rfl
  | tail _ next ih => exact (preserves next focus).trans ih

/-- A previously completed where writer's original ordered requested
outputs remain witnessed in the actual final assignment. This is an
explicit silent-success fragment, not closure of general request-changing
solver paths. -/
theorem outputs_after {basis a b : Journal rs} {p : Plan rs} {c : GeneralWhereOriginDelta318.Cell p}
    {ord : Nat} {s : Site rs}
    (path : B4Target.Steps (QuietStep r keep) a b)
    (born : GeneralDeclarativeWhereEndpoint346.At basis a p c ord s)
    (ready : Ready a.mixed.core p.packet.site.occurrence p)
    (m : Assignment) (fit : Models b m) :
    ∀ out ∈ requests a.mixed.core p.packet.site.occurrence,
      GeneralDictionaryDefaultEvidence204.OutputWitness p m out := by
  have stayed := GeneralDeclarativeTxnHistory348.born_path (forget_path path) born
  have stamped : p ∈ b.versionedWhere := List.mem_iff_getElem?.mpr ⟨_,stayed.stamp⟩
  have valid := (class_effects_iff ..).mp (fit.2 p stamped).2
  have same := requests_after path p.packet.site.occurrence
  have next : Ready b.mixed.core p.packet.site.occurrence p := by
    unfold Ready at ready ⊢
    rw [same]
    exact ready
  intro out requested
  exact GeneralDictionaryDefaultEvidence204Laws.output_of_class_effects next valid (same.symm ▸ requested)

end Yulang.GeneralDeclarativeTxnQuiet348
