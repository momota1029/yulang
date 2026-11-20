import Yulang.GeneralRebaseReceiptStampMachine289

/-! Add exact typed-stamp revalidation around the strict sidecar. The old
raw state is still the first component, and raw steps reset auxiliary work. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29500
set_option maxHeartbeats 20000000
namespace Yulang.GeneralRebaseReceiptStampedProduct289
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentPacket287 (child)
open GeneralRebaseReceiptFixture289 (wire request)
open GeneralRebaseReceiptMachine289 (tick received_exact published_exact)
open GeneralRebaseReceiptTypedStamp289 (Stamp capture)
open GeneralRebaseReceiptStampMachine289 (Phase erase lift Valid step)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralRebaseReceiptWitness289 (ActualPath)

def currentStamp (choice : Bool) (s : State roles) : Stamp :=
  capture s.core.erased.current.context.state root (child choice) (request choice)

noncomputable def runPhase (choice : Bool) (s : State roles) (p : Phase) : Option Phase :=
  step (currentStamp choice s) (GeneralRebaseReceiptAnchorProduct289.aux choice s) p

structure Config where
  raw : State roles
  phase : Phase

def project (config : Config) : GeneralRebaseReceiptRawProduct289.Config :=
  ⟨config.raw,erase config.phase⟩

def decorate (choice : Bool) (config : GeneralRebaseReceiptRawProduct289.Config) : Config :=
  ⟨config.raw,lift (currentStamp choice config.raw) config.phase⟩

def ValidConfig (choice : Bool) (config : Config) : Prop :=
  Valid (currentStamp choice config.raw) config.phase

theorem project_decorate (choice : Bool) (config : GeneralRebaseReceiptRawProduct289.Config) :
    project (decorate choice config) = config := by
  cases config with
  | mk s phase =>
    unfold project decorate
    rw [GeneralRebaseReceiptStampMachine289.erase_lift]

theorem decorate_project (choice : Bool) (config : Config) (valid : ValidConfig choice config) :
    decorate choice (project config) = config := by
  cases config with
  | mk s phase =>
    unfold project decorate
    rw [GeneralRebaseReceiptStampMachine289.lift_erase _ _ valid]

inductive Next (choice : Bool) : Config → Config → Prop
  | raw (s t : State roles) (phase : Phase) :
      Step (registry choice) root s t → Next choice ⟨s,phase⟩ ⟨t,.scan⟩
  | side (s : State roles) (p q : Phase) :
      runPhase choice s p = some q → Next choice ⟨s,p⟩ ⟨s,q⟩

abbrev initial : Config := ⟨before,.scan⟩

theorem output_valid (choice : Bool) {s : State roles} (path : ActualPath choice s) {p q : Phase}
    (valid : Valid (currentStamp choice s) p) (advance : runPhase choice s p = some q) :
    Valid (currentStamp choice s) q := by
  unfold runPhase at advance
  rw [GeneralRebaseReceiptStampMachine289.stable_tick _ _ _ valid,
    GeneralRebaseReceiptAnchorProduct289.agrees_raw choice path] at advance
  cases base : tick (wire choice s) (request choice) (erase p) with
  | none => rw [base] at advance; cases advance
  | some result =>
    rw [base] at advance
    change some (lift (currentStamp choice s) result) = some q at advance
    cases Option.some.inj advance
    apply GeneralRebaseReceiptStampMachine289.lift_valid
    constructor
    · intro key found
      have proof := (received_exact _ _ key _).mp (found ▸ base)
      exact proof.2.1
    · intro key found
      have proof := (published_exact _ _ key _).mp (found ▸ base)
      exact proof.2.1

theorem project_edge (choice : Bool) {x y : Config} (prior : ActualPath choice x.raw)
    (valid : ValidConfig choice x) (edge : Next choice x y) :
    ValidConfig choice y ∧ GeneralRebaseReceiptAnchorProduct289.Next choice (project x) (project y) := by
  cases edge with
  | raw s t p old => exact ⟨trivial,.raw s t (erase p) old⟩
  | side s p q moved =>
    have erases := GeneralRebaseReceiptStampMachine289.erases_tick (currentStamp choice s)
      (GeneralRebaseReceiptAnchorProduct289.aux choice s) p valid
    change (runPhase choice s p).map erase = _ at erases
    rw [moved] at erases
    exact ⟨output_valid choice prior valid moved,.side s (erase p) (erase q) erases.symm⟩

theorem project_path (choice : Bool) {s : Config} (path : B4Target.Steps (Next choice) initial s) :
    ValidConfig choice s ∧
      B4Target.Steps (GeneralRebaseReceiptAnchorProduct289.Next choice) GeneralRebaseReceiptRawProduct289.initial (project s) := by
  induction path with
  | refl => exact ⟨trivial,.refl⟩
  | tail _ edge ih =>
    have plain := (GeneralRebaseReceiptAnchorProduct289.paths_iff choice _).mp ih.2
    have actual := GeneralRebaseReceiptRawProduct289.erase_path choice plain
    have proof := project_edge choice actual ih.1 edge
    exact ⟨proof.1,.tail ih.2 proof.2⟩

theorem decorate_valid (choice : Bool) {s : GeneralRebaseReceiptRawProduct289.Config}
    (path : B4Target.Steps (GeneralRebaseReceiptAnchorProduct289.Next choice) GeneralRebaseReceiptRawProduct289.initial s) :
    ValidConfig choice (decorate choice s) := by
  have plain := (GeneralRebaseReceiptAnchorProduct289.paths_iff choice s).mp path
  have family := (GeneralRebaseReceiptScopedTrace289.family_iff choice s).mp plain
  cases family <;> first | trivial | rfl

theorem decorate_edge (choice : Bool) {x y : GeneralRebaseReceiptRawProduct289.Config}
    (valid : ValidConfig choice (decorate choice x))
    (edge : GeneralRebaseReceiptAnchorProduct289.Next choice x y) :
    Next choice (decorate choice x) (decorate choice y) := by
  cases edge with
  | raw s t p old => exact .raw _ _ _ old
  | side s p q moved =>
    apply Next.side _ _ _
    unfold runPhase
    change Valid (currentStamp choice s) (lift (currentStamp choice s) p) at valid
    change step (currentStamp choice s) (GeneralRebaseReceiptAnchorProduct289.aux choice s)
      (lift (currentStamp choice s) p) = some (lift (currentStamp choice s) q)
    rw [GeneralRebaseReceiptStampMachine289.stable_tick _ _ _ valid,
      GeneralRebaseReceiptStampMachine289.erase_lift,moved]
    rfl

theorem decorate_path (choice : Bool) {s : GeneralRebaseReceiptRawProduct289.Config}
    (path : B4Target.Steps (GeneralRebaseReceiptAnchorProduct289.Next choice) GeneralRebaseReceiptRawProduct289.initial s) :
    B4Target.Steps (Next choice) initial (decorate choice s) := by
  induction path with
  | refl => exact .refl
  | tail earlier edge ih => exact .tail ih (decorate_edge choice (decorate_valid choice earlier) edge)

theorem paths_iff (choice : Bool) (s : Config) :
    B4Target.Steps (Next choice) initial s ↔
      ValidConfig choice s ∧
        B4Target.Steps (GeneralRebaseReceiptAnchorProduct289.Next choice)
          GeneralRebaseReceiptRawProduct289.initial (project s) := by
  constructor
  · exact project_path choice
  · rintro ⟨valid,path⟩
    exact decorate_project choice s valid ▸ decorate_path choice path

end Yulang.GeneralRebaseReceiptStampedProduct289
