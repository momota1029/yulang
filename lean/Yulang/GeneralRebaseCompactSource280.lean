import Yulang.GeneralRebaseArchiveLocal280
import Yulang.GeneralRebaseCompactEvidenceAt279

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 11000000
namespace Yulang.GeneralRebaseCompactSource280
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalCenteredHeadAllocEncoding (registry)
open B4SkeletonV8 (EvidenceAt)
open GeneralRebaseGraphBisim280 (Related models evidence generated stable)
open GeneralRebaseCompactMachine280 (compact CompactStep compact_related)
open GeneralRebaseArchiveLocal280 (adapter_local)
open CommonRoleOutermostResolver (All₂)

private theorem all_mono {A C : Type} {xs : List A} {ys : List C} {p q : A → C → Prop}
    (take : ∀ a b, p a b → q a b) (h : All₂ p xs ys) : All₂ q xs ys := by
  induction h with
  | nil => exact .nil
  | cons one _ ih => exact .cons (take _ _ one) ih

theorem evidenceAt_forward {a b : State roles} (same : Related a b)
    (cert : EvidenceAt (boundary roles) r a root) : EvidenceAt (boundary roles) r b root := by
  intro m valid d key kids data active quiet quietKids selected childEvidence
  have evidence_eq (goal : Occurrence roles) (payload : GeneralDictionaryReadback.Payload) :
      (boundary roles).Evidence r a m goal payload ↔ (boundary roles).Evidence r b m goal payload :=
    evidence same (registry r) goal m payload
  apply (evidence_eq d _).mp
  apply cert m ((models same m).mpr valid) d key kids data
  · exact active.imp id ((generated same root d).mpr)
  · exact (stable same).mpr quiet
  · exact fun c mem => (stable same).mpr (quietKids c mem)
  · exact (adapter_local same _).mpr selected
  · exact all_mono (fun c p old => (evidence_eq c p).mpr old) childEvidence

theorem evidenceAt_iff {a b : State roles} (same : Related a b) :
    EvidenceAt (boundary roles) r a root ↔ EvidenceAt (boundary roles) r b root :=
  ⟨evidenceAt_forward same,evidenceAt_forward same.symm⟩

theorem compact_EvidenceAt (s : State roles) :
    EvidenceAt (boundary roles) r s root ↔ EvidenceAt (boundary roles) r (compact s) root :=
  evidenceAt_iff (compact_related s)

theorem compact_initial {s : State roles} (init : (boundary roles).Initial r root s) :
    compact s = s := by
  obtain ⟨legacy,⟨ctx,_,_,_,_,_,rfl⟩,rfl⟩ := init
  rfl

def SourceCompact (r : Registry) (root : Occurrence roles) (a b : State roles) : Prop :=
  CompactStep (registry r) root a b

theorem reach_lift {a next : State roles} (_init : (boundary roles).Initial r root a)
    (walk : B4Target.Steps ((boundary roles).Step r root) a next) :
    ∃ other, B4Target.Steps (SourceCompact r root) a other ∧ Related next other :=
  GeneralRebaseCompactMachine280.lift_path (Related.refl a) walk

theorem reach_lower {a next : State roles} (_init : (boundary roles).Initial r root a)
    (walk : B4Target.Steps (SourceCompact r root) a next) :
    ∃ other, B4Target.Steps ((boundary roles).Step r root) a other ∧ Related other next :=
  GeneralRebaseCompactMachine280.lower_path (Related.refl a) walk

theorem source_accessible {a : State roles} (init : (boundary roles).Initial r root a) :
    Acc (fun after before => (boundary roles).Step r root before after) a ↔
      Acc (fun after before => SourceCompact r root before after) a := by
  have h := GeneralRebaseCompactMachine280.acc_exact a (registry r) root
  rw [compact_initial init] at h
  exact h

theorem finish {a : State roles} (init : (boundary roles).Initial r root a) :
    (∃ target, B4Target.Steps ((boundary roles).Step r root) a target ∧
      (boundary roles).Stable r target root ∧ EvidenceAt (boundary roles) r target root) ↔
    (∃ target, B4Target.Steps (SourceCompact r root) a target ∧
      (¬ ∃ out, SourceCompact r root target out) ∧ EvidenceAt (boundary roles) r target root) := by
  constructor
  · rintro ⟨target,walk,halted,body⟩
    obtain ⟨out,trace,rel⟩ := reach_lift init walk
    exact ⟨out,trace,(GeneralRebaseCompactMachine280.terminal_iff rel).mp halted,
      evidenceAt_forward rel body⟩
  · rintro ⟨target,walk,halted,body⟩
    obtain ⟨out,trace,rel⟩ := reach_lower init walk
    exact ⟨out,trace,(GeneralRebaseCompactMachine280.terminal_iff rel).mpr halted,
      evidenceAt_forward rel.symm body⟩

end Yulang.GeneralRebaseCompactSource280
