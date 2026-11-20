import Yulang.GeneralSourceRoleCstMaximalRuns294

/-! Recovery scope can shrink to a descendant, but that fact alone does not
establish that the descendant is an actual selectable role. -/
namespace Yulang.GeneralSourceRoleCstScopeRefine294
open GeneralSourceRoleCstTree293 (Tree Path)
open GeneralSourceRoleCstWire293 (Wire)
open GeneralSourceRoleCstMarkPolicy294 (BranchPlain branchClear branch_exact Policy)
open GeneralSourceRoleCstMarkScope294 (Zone classify unrelated_exact)
open GeneralSourceRoleCstSnapshot293 (Snapshot Address)
open GeneralSourceRoleCstSpan293 (Extent)
open GeneralSourceRoleCstVisibleRange294 (checkVisible visible_range_exact)
open GeneralSourceRoleCstMixedReceipt294 (Evidence Receipt valid valid_exact)
open GeneralSourceRoleCstDiagnostics294 (IndependentPermission)

theorem unrelated_descends {p q m : Path} (step : p <+: q)
    (clear : (¬ p <+: m) ∧ ¬ m <+: p) : (¬ q <+: m) ∧ ¬ m <+: q := by
  constructor
  · intro bad
    exact clear.1 (step.trans bad)
  · intro bad
    rcases List.prefix_or_prefix_of_prefix step bad with a | b
    · exact clear.1 a
    · exact clear.2 b

theorem branch_descends (root : Tree) {p q : Path} (step : p <+: q)
    (safe : branchClear root p = true) : branchClear root q = true := by
  apply (branch_exact ..).mpr
  intro path tag marked
  exact unrelated_descends step ((branch_exact ..).mp safe path tag marked)

theorem visible_range_descends (w : Wire) (range : Extent) {p q : Path} (step : p <+: q)
    (pass : checkVisible w range p = true) : checkVisible w range q = true := by
  obtain ⟨cs,root,row,shape,mapped,group,clear⟩ := (visible_range_exact ..).mp pass
  exact (visible_range_exact ..).mpr
    ⟨cs,root,row,shape,mapped,group,fun item h =>
      ⟨unrelated_descends step (clear item h).1,(clear item h).2⟩⟩

theorem evidence_descends (w : Wire) (root : Tree) {p q : Path} (step : p <+: q)
    (e : Evidence) (safe : e.Scoped .selectedBranch w root p) :
    e.Scoped .selectedBranch w root q := by
  cases e with
  | errorGroupRange r =>
    change (_ ∧ ∃ _, _ ∧ _) at safe ⊢
    obtain ⟨branch,row,found,clear⟩ := safe
    exact ⟨branch,row,found,fun item h => unrelated_descends step (clear item h)⟩
  | otherDiagnostic d =>
    have old : IndependentPermission .selectedBranch p d ∧ _ := safe
    obtain ⟨⟨policy,owner,isOwner,clear⟩,inTree⟩ := old
    exact ⟨⟨policy,owner,isOwner,unrelated_descends step clear⟩,inTree⟩

theorem reported_scope_descends {Brand : Type} [DecidableEq Brand] (w : Wire)
    (s : Snapshot Brand) {p q : Path} (step : p <+: q) (packet : Receipt Brand)
    (ok : valid .selectedBranch w s p packet = true) :
    valid .selectedBranch w s q packet = true := by
  obtain ⟨events,reported,allowed⟩ := (valid_exact ..).mp ok
  exact (valid_exact ..).mpr ⟨events,reported,fun e h => evidence_descends w s.root step e (allowed e h)⟩

end Yulang.GeneralSourceRoleCstScopeRefine294
