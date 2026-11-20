import Yulang.GeneralSourceRoleCstMissingReceipt294

/-! Range-only Missing scope is information-theoretically insufficient when
two verified raw addresses at that range lie on opposite sides of the focus. -/
namespace Yulang.GeneralSourceRoleCstMissingAmbiguity294
open GeneralSourceRoleCstWire293 (Wire)
open GeneralSourceRoleCstTree293 (Path)
open GeneralSourceRoleCstSpan293 (Extent)
open GeneralSourceRoleCstMissingReceipt294 (MissingAnchor verified independentlyOutside)

theorem no_extent_only_decider (w : Wire) (p : Path) (a b : MissingAnchor)
    (sameRange : a.span = b.span)
    (aVer : verified w a = true) (bVer : verified w b = true)
    (aBlocked : independentlyOutside w p a = false)
    (bOutside : independentlyOutside w p b = true) :
    ¬ ∃ guess : Extent → Bool, ∀ e, verified w e = true →
      guess e.span = independentlyOutside w p e := by
  rintro ⟨guess,correct⟩
  have lhs := correct a aVer
  have rhs := correct b bVer
  rw [sameRange,aBlocked] at lhs
  rw [bOutside] at rhs
  cases lhs.symm.trans rhs

theorem select_path_allowed_iff (w : Wire) (p : Path) (item : MissingAnchor)
    (ok : verified w item = true) :
    independentlyOutside w p item = true ↔ ¬ p <+: item.path ∧ ¬ item.path <+: p := by
  rw [GeneralSourceRoleCstMissingReceipt294.outside_exact]
  simp [ok]

/-- Closed same-offset case: one missing node is inside the focus, the
other is under a distinct sibling. -/
def equalOffsets : Wire :=
  .node "Root" [.node "CaseScrutinee" [.node "Missing" []],
                .node "CaseBlock" [.node "Missing" []]]

def leftCase : MissingAnchor := ⟨[0,0],⟨0,0⟩⟩
def rightCase : MissingAnchor := ⟨[1,0],⟨0,0⟩⟩

theorem missing_scope_needs_more_than_extent :
    ¬ ∃ guess : Extent → Bool, ∀ e, verified equalOffsets e = true →
      guess e.span = independentlyOutside equalOffsets [0] e :=
  no_extent_only_decider equalOffsets [0] leftCase rightCase rfl rfl rfl rfl rfl

end Yulang.GeneralSourceRoleCstMissingAmbiguity294
