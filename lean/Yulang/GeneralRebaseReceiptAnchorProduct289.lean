import Yulang.GeneralRebaseReceiptAnchorFixture289

/-! The most constrained sidecar revalidates finite constructor entries and
the full occurrence/producer on both ticks. Old raw Steps remain separate. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29500
set_option maxHeartbeats 20000000
namespace Yulang.GeneralRebaseReceiptAnchorProduct289
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentPacket287 (child)
open GeneralRebaseRowParentFrame287 (after)
open GeneralRebaseReceiptFixture289 (request wire)
open GeneralRebaseReceiptMachine289 (Phase tick)
open GeneralRebaseReceiptExactLink289 (anchoredWire boundedDecision Anchored)
open GeneralRebaseReceiptAnchorFixture289 (before_anchor_wire after_anchor_wire)
open GeneralRebaseReceiptWitness289 (ActualPath)
open GeneralRebaseReceiptGuardedProduct289 (equivalent_paths exact_terminals)
open GeneralRebaseReceiptRawProduct289 (Config initial)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalVersionedJournal232 (State)
open GeneralSourceDictionaries (Occurrence)
open GeneralDeclarations (Registry)
open GeneralRebaseReceiptWire289 (Offer)

def strictTick (r : Registry) (s : State rs) (up down : Occurrence rs)
    (ask : Offer) (p : Phase) : Option Phase :=
  match anchoredWire r s up down ask with
  | some w => tick w ask p
  | none => match p with
    | .published _ | .stopped _ => none
    | .scan | .received _ => some (.stopped (.denied .wrongWorld))

noncomputable def aux (choice : Bool) (s : State roles) (p : Phase) : Option Phase :=
  strictTick (registry choice) s root (child choice) (request choice) p

theorem published_anchor {rs : Roles.RoleDecls} {r : Registry} {s : State rs}
    {up down : Occurrence rs} {ask stamp : Offer} {p : Phase}
    (took : strictTick r s up down ask p = some (.published stamp)) :
    stamp = ask ∧ Anchored r s up down ask := by
  unfold strictTick at took
  cases reads : anchoredWire r s up down ask with
  | none =>
    rw [reads] at took
    cases p <;> cases took
  | some w =>
    rw [reads] at took
    have pass := (GeneralRebaseReceiptMachine289.published_exact w ask stamp p).mp took
    refine ⟨pass.2.1,GeneralRebaseReceiptExactLink289.accept_has_actual_anchor ?_⟩
    unfold boundedDecision
    rw [reads]
    exact pass.2.2

theorem agrees_raw (choice : Bool) {s : State roles} (path : ActualPath choice s) (p : Phase) :
    aux choice s p = tick (wire choice s) (request choice) p := by
  unfold aux strictTick
  rcases GeneralRebaseRowActualPaths287.one_or_zero choice s path with rfl | rfl
  · rw [before_anchor_wire]
  · rw [after_anchor_wire]

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
      rw [agrees_raw choice prior] at one
      exact .side s p q one
  · intro edge
    cases edge with
    | raw s t phase old => exact .raw s t phase old
    | side s p q one =>
      rw [← agrees_raw choice prior] at one
      exact .side s p q one

theorem paths_iff (choice : Bool) (s : Config) :
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

theorem raw_paths_iff (choice : Bool) (raw : State roles) :
    (∃ p, B4Target.Steps (Next choice) initial ⟨raw,p⟩) ↔ ActualPath choice raw := by
  constructor
  · rintro ⟨p,path⟩
    exact (GeneralRebaseReceiptRawProduct289.path_iff choice raw).mp ⟨p,(paths_iff choice _).mp path⟩
  · intro actual
    obtain ⟨p,path⟩ := (GeneralRebaseReceiptRawProduct289.path_iff choice raw).mpr actual
    exact ⟨p,(paths_iff choice _).mpr path⟩

theorem exact_terminals (choice : Bool) (s : Config) :
    (B4Target.Steps (Next choice) initial s ∧ (∀ t, ¬ Next choice s t)) ↔
      s = ⟨after choice,GeneralRebaseReceiptScopedTrace289.finalPhase choice⟩ := by
  rw [← GeneralRebaseReceiptScopedTrace289.terminal_config choice s]
  constructor
  · rintro ⟨path,halt⟩
    have old := (paths_iff choice s).mp path
    exact ⟨old,fun t move => halt t ((move_iff choice
      (GeneralRebaseReceiptRawProduct289.erase_path choice old)).mpr move)⟩
  · rintro ⟨path,halt⟩
    exact ⟨(paths_iff choice s).mpr path,fun t move => halt t ((move_iff choice
      (GeneralRebaseReceiptRawProduct289.erase_path choice path)).mp move)⟩

end Yulang.GeneralRebaseReceiptAnchorProduct289
