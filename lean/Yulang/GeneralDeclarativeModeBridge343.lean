import Yulang.GeneralDeclarativeStoppedPaired341
import Yulang.GeneralDeclarativeObserverGrowth330

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 15300
set_option maxHeartbeats 6500000
namespace Yulang.GeneralDeclarativeModeBridge343
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeEntailment320 (Holds appendFacts model_append)
open GeneralStoppedPlacement335 (SameCapture SameDemand Meaning)
open GeneralDeclarativeLowerKnown321 (Alias)
open GeneralDeclarativeCurrentReceipt330 (literal)
open GeneralDeclarativeGrowth327 (facts)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeObserverGrowth330 (preserve backed_same)
open GeneralDeclarativeStoppedPaired341 (Placement activeDemand)
open CommonRoleOutermostResolver (All₂)
open GeneralNominalCenters (Site)
open GeneralNominalCommonBridge (Assignment)

def pair (x y : Capture) : List Equation :=
  [⟨x.lower,.variable y.lower⟩,⟨x.center,.variable y.center⟩,⟨x.upper,.variable y.upper⟩]

def rows : List Capture → List Capture → List Equation
  | x::xs,y::ys => pair x y ++ rows xs ys
  | _,_ => []

def joined (s : State) (x y : Demand) : State := appendFacts s (rows x.arguments y.arguments)

theorem pointwise (m : Assignment) (x y : Capture) :
    (∀ row ∈ pair x y, Holds m row) ↔ Meaning m x y := by
  constructor
  · intro all
    exact ⟨all _ List.mem_cons_self,all _ (List.mem_cons_of_mem _ List.mem_cons_self),
      all _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))⟩
  · intro all row seen
    rcases List.mem_cons.mp seen with one|later
    · cases one
      exact all.1
    · rcases List.mem_cons.mp later with one|last
      · cases one
        exact all.2.1
      · cases List.mem_singleton.mp last
        exact all.2.2

theorem written {m : Assignment} (sound : All₂ (Meaning m) xs ys) :
    ∀ row ∈ rows xs ys, Holds m row := by
  induction sound with
  | nil => intro _ h; cases h
  | cons one _ next =>
    intro row written
    rcases List.mem_append.mp written with own|later
    · exact (pointwise m _ _).mpr one row own
    · exact next row later

theorem recovered {m : Assignment} (xs ys : List Capture) (size : xs.length = ys.length)
    (sound : ∀ row ∈ rows xs ys, Holds m row) : All₂ (Meaning m) xs ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => exact .nil
    | cons y rest => cases size
  | cons x rest prior =>
    cases ys with
    | nil => cases size
    | cons y after =>
      exact .cons ((pointwise m x y).mp (fun row known => sound row (List.mem_append_left _ known)))
        (prior after (Nat.succ.inj size) (fun row known => sound row (List.mem_append_right _ known)))

theorem source_iff {s : State} {x y : Demand} (m : Assignment) (arity : x.arguments.length = y.arguments.length) :
    Models (joined s x y) m ↔ Models s m ∧ All₂ (Meaning m) x.arguments y.arguments := by
  unfold joined
  rw [model_append]
  exact and_congr_right (fun _ => ⟨recovered _ _ arity,written⟩)

theorem realized {s : State} {m : Assignment}
    (meaning : All₂ (Meaning m) xs ys) (visible : rows xs ys ⊆ s.equations) :
    All₂ (SameCapture s) xs ys := by
  induction meaning with
  | nil => exact .nil
  | cons _ _ next =>
    refine .cons ⟨.forward (visible (List.mem_append_left _ List.mem_cons_self)),
      .forward (visible (List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self))),
      .forward (visible (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))⟩ ?_
    exact next (fun _ present => visible (List.mem_append_right _ present))

/-- Literal role, arity and output order accompany separate per-mode
semantic equations in a common model. Appending just these aliases
certifies positive placement, but does not authorize reads, decide
K2, or justify where the common model itself came from. -/
theorem with_actual_site {roles : Roles.RoleDecls} {raw : GeneralNominalVersionedJournal232.State roles}
    {site : Site roles} {s : State} {logic : Demand} {m : Assignment}
    (actual : site ∈ raw.core.sites)
    (role : (activeDemand raw site).role = logic.role)
    (targets : (activeDemand raw site).outputs = logic.outputs)
    (meaning : All₂ (Meaning m) (activeDemand raw site).arguments logic.arguments)
    (check : Models s m) :
    let t := joined s (activeDemand raw site) logic
    Models t m ∧ Placement raw t site.occurrence logic := by
  refine ⟨(model_append m).mpr ⟨check,written meaning⟩,site,actual,rfl,role,?_,targets⟩
  exact realized meaning (fun _ row => List.mem_append_right _ row)

theorem no_fresh_origin {s : State} {x y : Demand} (p : Supported s done) (r : Equation) :
    r ∈ (restriction (preserve p (facts s (rows x.arguments y.arguments)))).equations ↔
      r ∈ (restriction p).equations :=
  backed_same p _ r

end Yulang.GeneralDeclarativeModeBridge343
