import Yulang.GeneralRebaseReceiptMachine289

/-! A scoped product of the unchanged raw relation and a read-only sidecar.
Only raw steps can change the underlying journal. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29000
set_option maxHeartbeats 18500000
namespace Yulang.GeneralRebaseReceiptRawProduct289
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentFrame287 (after)
open GeneralRebaseReceiptFixture289 (wire request)
open GeneralRebaseReceiptMachine289 (Phase tick weight advance run)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedKernel234 (Step)

structure Config where
  raw : State roles
  phase : Phase

noncomputable def aux (choice : Bool) (s : Config) : Option Phase :=
  tick (wire choice s.raw) (request choice) s.phase

inductive Next (choice : Bool) : Config → Config → Prop
  | raw (s t : State roles) (phase : Phase) :
      Step (registry choice) root s t → Next choice ⟨s,phase⟩ ⟨t,.scan⟩
  | side (s : State roles) (p q : Phase) :
      tick (wire choice s) (request choice) p = some q → Next choice ⟨s,p⟩ ⟨s,q⟩

abbrev initial : Config := ⟨before,.scan⟩

theorem erase_one (choice : Bool) {x y : Config} (edge : Next choice x y) :
    Step (registry choice) root x.raw y.raw ∨ x.raw = y.raw := by
  cases edge with
  | raw _ _ _ old => exact .inl old
  | side _ _ _ _ => exact .inr rfl

theorem erase_path (choice : Bool) {x y : Config} (path : B4Target.Steps (Next choice) x y) :
    B4Target.Steps (Step (registry choice) root) x.raw y.raw := by
  induction path with
  | refl => exact .refl
  | tail _ edge ih =>
    rcases erase_one choice edge with raw | eq
    · exact .tail ih raw
    · exact eq ▸ ih

theorem lift_raw (choice : Bool) {s t : State roles}
    (path : B4Target.Steps (Step (registry choice) root) s t) :
    B4Target.Steps (Next choice) ⟨s,.scan⟩ ⟨t,.scan⟩ := by
  induction path with
  | refl => exact .refl
  | tail _ edge ih => exact .tail ih (.raw _ _ _ edge)

theorem path_iff (choice : Bool) (s : State roles) :
    (∃ p, B4Target.Steps (Next choice) initial ⟨s,p⟩) ↔
      GeneralRebaseReceiptWitness289.ActualPath choice s := by
  constructor
  · rintro ⟨p,path⟩
    exact erase_path choice path
  · intro path
    exact ⟨.scan,lift_raw choice path⟩

theorem aux_preserves_models (choice : Bool) (s : State roles) (p q : Phase)
    (taken : tick (wire choice s) (request choice) p = some q) :
    (∀ m, Models (⟨s,p⟩ : Config).raw m ↔ Models (⟨s,q⟩ : Config).raw m) ∧ weight q < weight p :=
  ⟨fun _ => Iff.rfl,GeneralRebaseReceiptMachine289.decreases _ _ _ _ taken⟩

theorem terminal_iff (choice : Bool) (x : Config) :
    (∀ y, ¬ Next choice x y) ↔
      (∀ s, ¬ Step (registry choice) root x.raw s) ∧ aux choice x = none := by
  rcases x with ⟨s,p⟩
  constructor
  · intro halt
    refine ⟨fun t raw => halt ⟨t,.scan⟩ (.raw s t p raw),?_⟩
    unfold aux
    cases value : tick (wire choice s) (request choice) p with
    | none => rfl
    | some q => exact (halt ⟨s,q⟩ (.side s p q value)).elim
  · rintro ⟨raw,auxiliary⟩ y next
    cases next with
    | raw _ _ _ edge => exact raw _ edge
    | side _ _ q edge => rw [aux] at auxiliary; rw [auxiliary] at edge; cases edge

end Yulang.GeneralRebaseReceiptRawProduct289
