import Yulang.GeneralDeclarativeRecordReconstruct330
import Yulang.GeneralDeclarativeOpaqueNames328

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeRecordNames330
open GeneralDeclarativeHead320 (State Equation Models environment)
open GeneralDeclarativeDemand320 (Bounds bounds_sound)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeEntailment320 (Entails appendFacts model_append)
open GeneralDeclarativeFootprint321 (stateNames preserves_models)
open GeneralDeclarativeOpaqueNames328 (kept first second extend unchanged unchanged_root left_value right_value)
open GeneralDeclarativeEqualities322 (Derives)
open GeneralDeclarativeRecordChannel330 (project)
open GeneralDeclarativeRecordIntervals330 (present)
open GeneralDeclarativeRecordReconstruct330 (exact reconstruct)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open CommonNominalFullCarrier (Ty Equivalent Subtype subtype_trans record)

def row (s : State) (root key : Nat) (protect : List Nat) : Equation :=
  ⟨root,.record key (.variable (first s root protect)) (.variable (second s root protect))⟩
def expose (s : State) (root key : Nat) (protect : List Nat) : State :=
  appendFacts s [row s root key protect]

theorem named {s : State} (root key : Nat) (protect : List Nat) :
    Derives (expose s root key protect) (.variable root) (row s root key protect).right :=
  .row (List.mem_append_right _ List.mem_cons_self)

theorem lifts {s : State} (root key : Nat) (protect : List Nat) (m : Assignment)
    (old : Models s m) (observed : Equivalent (m root).1 (record key a b)) :
    Models (expose s root key protect) (extend s root protect m a b) ∧
      ∀ n ∈ kept s root protect, extend s root protect m a b n = m n := by
  let next := extend s root protect m a b
  have constant : ∀ n ∈ kept s root protect, next n = m n := fun _ h => unchanged m a b h
  refine ⟨(model_append next).mpr ⟨(preserves_models s
    (fun n before => constant n (List.mem_append_left _ before))).mpr old,?_⟩,constant⟩
  intro eq listed
  cases List.mem_singleton.mp listed
  change Equivalent (next root).1 (record key (next (first s root protect)).1 (next (second s root protect)).1)
  dsimp only [next]
  rw [unchanged_root s root protect m a b,left_value,right_value]
  exact observed

def Agreement (key : Nat) (value : Ty) : Prop :=
  ∃ req opt, project key false [] value = some req ∧ project key true [] value = some opt ∧ Equivalent req opt

/-- Precise model-level criterion for a conservative fresh ordinary
record equation, preserving every old name and all requested output
targets. Existence does not authorize the new tail for source probing. -/
theorem model_exact {s : State} (key : Nat) (protect : List Nat) (m : Assignment)
    (bounds : Bounds s cap)
    (low : Entails s ⟨cap.lower,.record key lo loRest⟩)
    (high : Entails s ⟨cap.upper,.record key hi hiRest⟩) :
    (∃ next, Models (expose s cap.center key protect) next ∧
       ∀ n ∈ kept s cap.center protect, next n = m n) ↔
      Models s m ∧ Agreement key (m cap.center).1 := by
  constructor
  · rintro ⟨next,valid,unchanged⟩
    have first := (model_append next).mp valid
    have old := (preserves_models s (fun n seen => unchanged n (List.mem_append_left _ seen))).mp first.1
    have capEq := unchanged cap.center (List.mem_append_right _ List.mem_cons_self)
    have actual := first.2 (row s cap.center key protect) List.mem_cons_self
    change Equivalent (next cap.center).1
      (record key (next (GeneralDeclarativeOpaqueNames328.first s cap.center protect)).1
        (next (second s cap.center protect)).1) at actual
    rw [capEq] at actual
    have box := bounds_sound bounds m old
    have bot := subtype_trans (low m old).2 box.1
    have top := subtype_trans box.2 (high m old).1
    obtain ⟨r,someReq⟩ := present key false top
    obtain ⟨o,someOpt⟩ := present key true top
    exact ⟨old,r,o,someReq,someOpt,(exact bot top someReq someOpt).mp ⟨_,_,actual⟩⟩
  · rintro ⟨old,req,opt,p,q,same⟩
    have box := bounds_sound bounds m old
    have bot := subtype_trans (low m old).2 box.1
    have top := subtype_trans box.2 (high m old).1
    have chosen := reconstruct bot top p q same
    exact ⟨_,lifts cap.center key protect m old chosen⟩

end Yulang.GeneralDeclarativeRecordNames330
