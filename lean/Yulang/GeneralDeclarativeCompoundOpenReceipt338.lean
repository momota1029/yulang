import Yulang.GeneralDeclarativeCompoundOpenPrefix338

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeCompoundOpenReceipt338
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativeExactOverlay337 (ModelsExact)
open GeneralDeclarativeExactSupport337 (receipts_same)
open GeneralDeclarativeCompoundOpenPrefix338 (Read residuals residual_interval)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeEndpointBatch336 (prepare slots patch fit patch_values preserves atSlots)
open GeneralDeclarativeEndpointConserve336 (names)
open GeneralDeclarativeFootprint321 (stateNames)
open GeneralNominalCommonBridge (Assignment)

def scope (arg : Capture) (old : List GeneralDeclarativeEndpointOverlay336.Entry) (keep : List Nat) : List Nat :=
  [arg.lower,arg.center,arg.upper] ++ (names old ++ keep)

def receipt (m : Assignment) (arg : Capture) (keys : List Nat) (new : Capture) : Prop :=
  atSlots m new = residuals keys m arg

theorem receipt_current {m n : Assignment} {a : Capture} {keys : List Nat} {out : Capture}
    (l : n a.lower = m a.lower) (c : n a.center = m a.center) (u : n a.upper = m a.upper)
    (left : n out.lower = m out.lower) (middle : n out.center = m out.center)
    (right : n out.upper = m out.upper) : receipt n a keys out ↔ receipt m a keys out := by
  simp only [receipt,atSlots,residuals,l,c,u,left,middle,right]

/-- Give exact unknown-tail values a real fresh interval, protecting
older receipts and fixed output targets. The ordinary state only gets
ordinary interval atoms; no arbitrary residual Expr equality is emitted
or treated as new author support. -/
theorem exact_named {s : State} {p : Supported s done}
    (read : Read p arg keys ls us first last le ue) (m : Assignment) (oldFit : ModelsExact s old m)
    (keep : List Nat) :
    let saved := scope arg old keep
    ∃ n, ModelsExact (prepare s saved 1) old n ∧
      receipt n arg keys (slots s saved 0) ∧ ∀ x ∈ stateNames s ++ saved, n x = m x := by
  let protect := scope arg old keep
  let triple := residuals keys m arg
  let n := patch s protect [triple] m
  have kept : ∀ x ∈ stateNames s ++ protect, n x = m x := preserves [triple] m
  have valid : GeneralDeclarativeHead320.Models (prepare s protect 1) n :=
    fit oldFit.1 protect [triple] (fun v h => by
      cases List.mem_singleton.mp h
      exact residual_interval read m oldFit.1)
  have keepOld : ∀ x ∈ names old, n x = m x := by
    intro x got
    exact kept x (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ got)))
  have inArg : ∀ x ∈ [arg.lower,arg.center,arg.upper], n x = m x := by
    intro x got
    exact kept x (List.mem_append_right _ (List.mem_append_left _ got))
  have atReceipt : atSlots n (slots s protect 0) = triple := by
    exact patch_values (s := s) (protect := protect) (m := m) (by rfl)
  refine ⟨n,⟨valid,(receipts_same keepOld).mpr oldFit.2⟩,?_ ,kept⟩
  unfold receipt
  rw [atReceipt]
  simp only [triple,residuals,inArg _ List.mem_cons_self,
    inArg _ (List.mem_cons_of_mem _ List.mem_cons_self),
    inArg _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))]

end Yulang.GeneralDeclarativeCompoundOpenReceipt338
