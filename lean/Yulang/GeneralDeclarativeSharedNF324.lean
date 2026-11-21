import Yulang.GeneralDeclarativeNFComplete324

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeSharedNF324
open GeneralDeclarativeHead320 (State Models byMode)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeNFHead324 (Scan)
open GeneralDeclarativeRepeatedActual323 (BindsAt OccursAt eqAt)
open GeneralDeclarativeTermWalk322 (Occurrence)
open GeneralDeclarativeTermOccurrences322 (source_binders actual_positions)
open GeneralDeclarativeStructuralScan323 (ReadBack)
open GeneralDeclarativeExactWalk323 (Exact)
open GeneralDeclarationPatterns (Pattern normalize normalizeArgs variablesArgs)
open GeneralDeclarativeSourceEmission322 (Names)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans eqv_symm)
open CommonNominalFullCarrier (Equivalent)
open CommonRoleOutermostResolver (All₂)

theorem binder_observed {s : State} (seen : Scan s c interp arg pattern uses)
    (binder : Nat) (appears : binder ∈ (normalize pattern).variables) :
    ∃ occurrence ∈ uses, occurrence.binder = binder ∧ occurrence.mode = .actual := by
  obtain ⟨_,_,_,compiled,actual⟩ := seen.observed
  exact (source_binders compiled actual.walked).2 binder appears

theorem one_position {s : State} (read : Scan s c interp arg pattern uses)
    (l : BindsAt m left uses) (r : BindsAt m right uses)
    (binder : Nat) (appears : binder ∈ (normalize pattern).variables) :
    Equivalent (m (left binder).center).1 (m (right binder).center).1 := by
  obtain ⟨o,whereSeen,eq,mode⟩ := binder_observed read binder appears
  have lBind := l o whereSeen
  have rBind := r o whereSeen
  rw [OccursAt,eq,mode,byMode] at lBind rBind
  exact eqv_trans (eqv_symm lBind) rBind

/-- Two source captures of the same real normalized observations agree
at every visible input binder. An erased field contributes no occurrence
and no equation; unrelated extra fields of the capture map can differ. -/
theorem shared_heads {s : State} {ps : List Pattern}
    (both : All₂ (fun arg p => ∃ uses, Scan s c interp arg p uses ∧
      BindsAt m left uses ∧ BindsAt m right uses) args ps) :
    ∀ binder ∈ variablesArgs (normalizeArgs ps),
      Equivalent (m (left binder).center).1 (m (right binder).center).1 := by
  induction both with
  | nil => exact fun _ bad => False.elim (List.not_mem_nil bad)
  | cons first rest ih =>
    intro binder occurs
    obtain ⟨uses,seen,l,r⟩ := first
    rcases List.mem_append.mp occurs with atFirst|atRest
    · exact one_position seen l r binder atFirst
    · exact ih binder atRest

end Yulang.GeneralDeclarativeSharedNF324
