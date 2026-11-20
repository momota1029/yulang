import Yulang.GeneralRebaseReceiptCatalogueFixture289

/-! Replace only the auxiliary read function by the finite catalogue gate.
The two actual raw traces have the same executable phases. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29200
set_option maxHeartbeats 19000000
namespace Yulang.GeneralRebaseReceiptGuardedProduct289
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentPacket287 (child)
open GeneralRebaseRowParentFrame287 (after)
open GeneralRebaseReceiptFixture289 (wire request)
open GeneralRebaseReceiptCatalogue289 (boundedWire guarded constructorKeys)
open GeneralRebaseReceiptCatalogueFixture289 (sealed_after sealed_before)
open GeneralRebaseReceiptWire289 (Offer)
open GeneralRebaseReceiptMachine289 (Phase tick)
open GeneralRebaseReceiptRawProduct289 (Config initial)
open GeneralRebaseReceiptWitness289 (ActualPath)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalVersionedJournal232 (State)
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)

def guardedTick (r : Registry) (s : State rs) (focus : Occurrence rs) (ask : Offer) (p : Phase) : Option Phase :=
  match boundedWire r s focus with
  | some w => tick w ask p
  | none => match p with
    | .published _ | .stopped _ => none
    | .scan | .received _ => some (.stopped (.denied .wrongWorld))

noncomputable def aux (choice : Bool) (s : State roles) (p : Phase) : Option Phase :=
  guardedTick (registry choice) s (child choice) (request choice) p

theorem tick_agrees (choice : Bool) {s : State roles} (path : ActualPath choice s) (p : Phase) :
    aux choice s p = tick (wire choice s) (request choice) p := by
  unfold aux guardedTick
  rcases GeneralRebaseRowActualPaths287.one_or_zero choice s path with rfl | rfl
  · rw [sealed_before]
  · rw [sealed_after]

inductive Next (choice : Bool) : Config → Config → Prop
  | raw (s t : State roles) (phase : Phase) :
      Step (registry choice) root s t → Next choice ⟨s,phase⟩ ⟨t,.scan⟩
  | side (s : State roles) (p q : Phase) :
      aux choice s p = some q → Next choice ⟨s,p⟩ ⟨s,q⟩

theorem move_iff (choice : Bool) {x y : Config}
    (prior : ActualPath choice x.raw) :
    Next choice x y ↔ GeneralRebaseReceiptRawProduct289.Next choice x y := by
  constructor
  · intro edge
    cases edge with
    | raw s t phase old => exact .raw s t phase old
    | side s p q one =>
      rw [tick_agrees choice prior] at one
      exact .side s p q one
  · intro edge
    cases edge with
    | raw s t phase old => exact .raw s t phase old
    | side s p q one =>
      rw [← tick_agrees choice prior] at one
      exact .side s p q one

theorem equivalent_paths (choice : Bool) (s : Config) :
    B4Target.Steps (Next choice) initial s ↔ B4Target.Steps (GeneralRebaseReceiptRawProduct289.Next choice) initial s := by
  constructor
  · intro path
    induction path with
    | refl => exact .refl
    | tail _ move ih =>
      exact .tail ih ((move_iff choice (GeneralRebaseReceiptRawProduct289.erase_path choice ih)).mp move)
  · intro path
    induction path with
    | refl => exact .refl
    | tail earlier move ih =>
      exact .tail ih ((move_iff choice (GeneralRebaseReceiptRawProduct289.erase_path choice earlier)).mpr move)

theorem exact_terminals (choice : Bool) (s : Config) :
    (B4Target.Steps (Next choice) initial s ∧ (∀ t, ¬ Next choice s t)) ↔
      s = ⟨after choice,GeneralRebaseReceiptScopedTrace289.finalPhase choice⟩ := by
  rw [← GeneralRebaseReceiptScopedTrace289.terminal_config choice s]
  constructor
  · rintro ⟨path,halt⟩
    have old := (equivalent_paths choice s).mp path
    exact ⟨old,fun t move => halt t ((move_iff choice
      (GeneralRebaseReceiptRawProduct289.erase_path choice old)).mpr move)⟩
  · rintro ⟨path,halt⟩
    exact ⟨(equivalent_paths choice s).mpr path,fun t move => halt t ((move_iff choice
      (GeneralRebaseReceiptRawProduct289.erase_path choice path)).mp move)⟩

theorem raw_path_iff (choice : Bool) (s : State roles) :
    (∃ p, B4Target.Steps (Next choice) initial ⟨s,p⟩) ↔ ActualPath choice s := by
  constructor
  · rintro ⟨p,path⟩
    exact (GeneralRebaseReceiptRawProduct289.path_iff choice s).mp
      ⟨p,(equivalent_paths choice ⟨s,p⟩).mp path⟩
  · intro path
    obtain ⟨p,lifted⟩ := (GeneralRebaseReceiptRawProduct289.path_iff choice s).mpr path
    exact ⟨p,(equivalent_paths choice ⟨s,p⟩).mpr lifted⟩

end Yulang.GeneralRebaseReceiptGuardedProduct289
