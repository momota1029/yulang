import Yulang.GeneralSourceRoleCstScopeRefine294

/-! A genuinely empty authoritative receipt imposes no extra branch check.
Whole-policy success can be reused without altering the unresolved payload. -/
namespace Yulang.GeneralSourceRoleCstStrictTransport294
open GeneralSourceRoleCstWire293 (Wire decode decode_exact Transfer)
open GeneralSourceRoleCstVisibleReceipt294 (project project_exact)
open GeneralSourceRoleCstMixedReceipt294 (Receipt exportChecked export_exact)
open GeneralSourceRoleCstMarkPolicy294 (Policy guarded allows guarded_exact whole_implies_branch)
open GeneralSourceRoleCstSnapshot293 (Address)
open GeneralSourceRoleCstRustSnapshot293 (exportAt)
open GeneralSourceRoleTrack292 (Tracked)

theorem empty_receipt_exact {Scope Brand : Type} [DecidableEq Brand] (policy : Policy)
    (scope : Scope) (w : Wire) (brand : Brand) (a : Address Brand)
    (out : Tracked Scope (Address Brand)) :
    project policy scope w brand a (.reported brand []) = some out ↔
      ∃ root, Transfer w root ∧ guarded policy scope ⟨brand,root⟩ a = some out := by
  rw [project_exact,export_exact]
  constructor
  · rintro ⟨⟨root,_,mapped,_,_,safe,picked⟩,_⟩
    exact ⟨root,mapped,(guarded_exact ..).mpr ⟨safe,picked⟩⟩
  · rintro ⟨root,mapped,f⟩
    obtain ⟨safe,picked⟩ := (guarded_exact ..).mp f
    exact ⟨⟨root,[],mapped,rfl,by simp,safe,picked⟩,⟨brand,[],rfl,by simp⟩⟩

theorem whole_receipt_exact {Scope Brand : Type} [DecidableEq Brand]
    (scope : Scope) (w : Wire) (brand : Brand) (a : Address Brand) (r : Receipt Brand)
    (out : Tracked Scope (Address Brand)) :
    project .whole scope w brand a r = some out ↔ r = .reported brand [] ∧
      ∃ root, Transfer w root ∧ guarded .whole scope ⟨brand,root⟩ a = some out := by
  constructor
  · intro h
    obtain ⟨strict,_⟩ := (project_exact ..).mp h
    obtain ⟨root,events,mapped,payload,each,safe,picked⟩ := (export_exact ..).mp strict
    have seen : GeneralSourceRoleCstMixedReceipt294.valid .whole w ⟨brand,root⟩ a.path r = true :=
      (GeneralSourceRoleCstMixedReceipt294.valid_exact ..).mpr ⟨events,payload,each⟩
    exact ⟨(GeneralSourceRoleCstMixedReceipt294.whole_valid_exact ..).mp seen,
      root,mapped,(guarded_exact ..).mpr ⟨safe,picked⟩⟩
  · rintro ⟨rfl,existsRoot⟩
    exact (empty_receipt_exact ..).mpr existsRoot

theorem whole_to_selected {Scope Brand : Type} [DecidableEq Brand]
    (scope : Scope) (w : Wire) (brand : Brand) (a : Address Brand) (r : Receipt Brand)
    (out : Tracked Scope (Address Brand))
    (ok : project .whole scope w brand a r = some out) :
    project .selectedBranch scope w brand a r = some out := by
  obtain ⟨rfl,root,mapped,done⟩ := (whole_receipt_exact ..).mp ok
  exact (empty_receipt_exact ..).mpr
    ⟨root,mapped,GeneralSourceRoleCstMarkPolicy294.selected_gate_preserves_whole_success _ _ _ _ done⟩

end Yulang.GeneralSourceRoleCstStrictTransport294
