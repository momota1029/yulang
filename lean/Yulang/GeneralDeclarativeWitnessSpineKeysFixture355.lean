import Yulang.GeneralDeclarativeWitnessSpineFrontModel355
import Yulang.GeneralDeclarativeWitnessSpineEdgeMeaning355
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65000
set_option maxHeartbeats 75000000
namespace Yulang.GeneralDeclarativeWitnessSpineKeysFixture355
open GeneralDeclarativeWitnessSpineFront355 (Found Wire read)
open GeneralDeclarativeWitnessSpineFrontFixture355 (source code)
open GeneralDeclarativeWitnessSpineFrontModel355 (established_model)
open GeneralDeclarativeWitnessSpineLedger355 (Checked.keys Checked.nodePaths)
open GeneralDeclarativeWitnessSpineEdgeMeaning355 (Meaning Checked.emissions same_view_for_authorized_tree)
open GeneralDeclarativeWitnessTypedRelease354 (Key)
open GeneralDeclarativeWitnessTypedEvidence355 (Evidence)
open GeneralDeclarativeWitnessCovariantOrigin353 (Valuation)
open GeneralDeclarativeWitnessGrandchildModel355 (model)
open GeneralDeclarativeHead320 (State Models)

def expected : List Key :=
  [⟨⟨[4],1,92,7⟩,1,1,10⟩,⟨⟨[4,0],3,93,8⟩,0,4,10⟩,
   ⟨⟨[4,0,0],4,94,9⟩,0,7,10⟩,⟨⟨[4,0,0,0],5,95,10⟩,0,8,10⟩]

def keysAreExact : Bool :=
  (code.map (fun (s,w) => ((read source s w).map (fun a =>
    decide (GeneralDeclarativeWitnessSpineLedger355.Checked.keys a.checked = expected ∧
      GeneralDeclarativeWitnessSpineLedger355.Checked.nodePaths a.checked = [[4],[4,0],[4,0,0],[4,0,0,0],[4,0,0,0,0]]))).getD false)).getD false

theorem actual_four_exact_releases_in_order : keysAreExact = true := by decide +kernel

theorem explicit_author_and_model_at_every_edge :
    ∃ (s : State) (w : Wire) (a : Found source s w) (v : Valuation),
      Models s model ∧ GeneralDeclarativeWitnessSpineLedger355.Checked.keys a.checked = expected ∧
      Evidence s model v source.problem.demand a.checked.dictionary ∧
      ∀ e ∈ GeneralDeclarativeWitnessSpineEdgeMeaning355.Checked.emissions a.checked,Meaning model v e := by
  have verified := actual_four_exact_releases_in_order
  unfold keysAreExact at verified
  cases s1 : code with
  | none => rw [s1] at verified; cases verified
  | some pair =>
    obtain ⟨s,w⟩ := pair
    cases s2 : read source s w with
    | none => simp [s1,s2] at verified
    | some a =>
      have must : decide (GeneralDeclarativeWitnessSpineLedger355.Checked.keys a.checked = expected ∧
          GeneralDeclarativeWitnessSpineLedger355.Checked.nodePaths a.checked = [[4],[4,0],[4,0,0],[4,0,0,0],[4,0,0,0,0]]) = true := by
        simpa [s1,s2] using verified
      have m := established_model s1
      obtain ⟨v,full,meaning⟩ := same_view_for_authorized_tree a model m
      exact ⟨s,w,a,v,m,(of_decide_eq_true must).1,full,meaning⟩

end Yulang.GeneralDeclarativeWitnessSpineKeysFixture355
