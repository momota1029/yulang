import Yulang.GeneralWhereOriginChild318

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 26000
set_option maxHeartbeats 18000000
namespace Yulang.GeneralWhereOriginSuccessor318
open GeneralNominalCenters (Plan Site observed_holds)
open GeneralNominalCenteredSteps (State)
open GeneralWhereVersionInstall317 (Journal Models install installCore emitted InstallStep)
open GeneralWhereVersionCompiler317 (children child)
open GeneralNominalCenteredHeadOutputs (requests mem_requests_iff)
open GeneralNominalVersionedEffects231 (ClassEffects)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCandidates (Context)

def SilentChildren (p : Plan rs) : Prop :=
  ∀ s ∈ emitted p, s.occurrence.demand.outputs = []

theorem alias_copy {a b : GeneralNominalSaturationState.State rs} (same : a.aliases = b.aliases)
    (rel : GeneralNominalSaturationState.Alias a x y) :
    GeneralNominalSaturationState.Alias b x y := by
  induction rel with
  | refl i => exact .refl i
  | edge member => exact .edge (same ▸ member)
  | symm _ ih => exact .symm ih
  | trans _ _ ih jh => exact .trans ih jh

/-- Appending output-free generated sites does not alter any representative
class's requests, even when input intervals and recorded occurrences change. -/
theorem requests_unchanged (core : State rs) (ctx : Context) (p : Plan rs)
    (silent : SilentChildren p) (focus out) :
    out ∈ requests (installCore core ctx p) focus ↔ out ∈ requests core focus := by
  simp only [mem_requests_iff]
  constructor
  · rintro ⟨s,used,aliased,output⟩
    change s ∈ core.erased.current.sites ++ (emitted p).map Site.observed at used
    rcases List.mem_append.mp used with old|new
    · exact ⟨s,old,alias_copy (a := (installCore core ctx p).erased.current) (b := core.erased.current) rfl aliased,output⟩
    · obtain ⟨c,there,rfl⟩ := List.mem_map.mp new
      change out ∈ c.occurrence.demand.outputs at output
      rw [silent c there] at output
      cases output
  · rintro ⟨s,present,apart,output⟩
    exact ⟨s,List.mem_append_left _ present,alias_copy (a := core.erased.current) (b := (installCore core ctx p).erased.current) rfl apart,output⟩

theorem existing_models {j : Journal rs} {p : Plan rs} {ctx : Context} {m : Assignment}
    (prior : GeneralNominalVersionedJournal232.Models j.mixed m)
    (raw : GeneralNominalState.Models ctx.state m)
    (newSites : ∀ s ∈ emitted p, s.Holds m)
    (silent : SilentChildren p) :
    GeneralNominalVersionedJournal232.Models (install j ctx p).mixed m := by
  refine ⟨⟨raw,prior.1.2.1,?_,?_,prior.1.2.2.2.2.1,?_⟩,prior.2.1,?_⟩
  · intro s present
    change s ∈ j.mixed.core.erased.current.sites ++ (emitted p).map Site.observed at present
    rcases List.mem_append.mp present with old|fresh
    · exact prior.1.2.2.1 s old
    · obtain ⟨new,found,rfl⟩ := List.mem_map.mp fresh
      exact observed_holds new m (newSites _ found)
  · intro s present
    change s ∈ j.mixed.core.sites ++ emitted p at present
    exact (List.mem_append.mp present).elim (prior.1.2.2.2.1 s) (newSites s)
  · intro effect member
    have h := prior.1.2.2.2.2.2 effect member
    exact ⟨h.1,GeneralNominalCenteredHeadMatEffects.restrict
      (fun out held => (requests_unchanged j.mixed.core ctx p silent _ out).mp held) h.2⟩
  · intro effect member
    have h := prior.2.2 effect member
    exact ⟨h.1,GeneralNominalVersionedJournal232.live_restrict
      (fun out held => (requests_unchanged j.mixed.core ctx p silent _ out).mp held) h.2⟩

theorem with_parent {j : Journal rs} {p : Plan rs} {ctx : Context} {m : Assignment}
    (prior : Models j m)
    (raw : GeneralNominalState.Models ctx.state m)
    (newPlan : GeneralWhereVersionSemantics317.Holds p m)
    (newClass : ClassEffects j.mixed.core p.packet.site.occurrence p m)
    (silent : SilentChildren p) :
    Models (install j ctx p) m := by
  have sites : ∀ s ∈ emitted p, s.Holds m := by
    intro s member
    obtain ⟨clause,present,rfl⟩ := List.mem_map.mp member
    have visible := (GeneralCanonicalChildOrder.canonicalRequirements_perm _).mem_iff.mpr clause.property
    exact (newPlan.childSemantics clause.val visible _).1
  refine ⟨existing_models prior.1 raw sites silent,?_⟩
  intro q stored
  change q ∈ j.versionedWhere ++ [p] at stored
  have substClass {t : Plan rs} (valid : ClassEffects j.mixed.core t.packet.site.occurrence t m) :
      ClassEffects (install j ctx p).mixed.core t.packet.site.occurrence t m :=
    (GeneralNominalVersionedFrameTransport232.class_effects_iff
      (fun out => requests_unchanged j.mixed.core ctx p silent _ out)).mpr valid
  rcases List.mem_append.mp stored with old|added
  · have h := prior.2 q old
    exact ⟨h.1,substClass h.2⟩
  · cases List.mem_singleton.mp added
    exact ⟨newPlan,substClass newClass⟩

end Yulang.GeneralWhereOriginSuccessor318
