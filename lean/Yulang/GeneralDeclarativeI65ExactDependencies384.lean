import Yulang.GeneralDeclarativeI65LogicalOrdinaryOutput383
import Yulang.GeneralDeclarativeI65LogicalNominalOutput383

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open CommonRoleOutermostResolver (Dictionary)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeWitnessDeclaredState357 (AuthoredNominal)

/-- Exact logical support obligations in a local positive source rule.
Same numeric targets, same request without its dictionary, and rows not
emitted by this ordinal do not suffice. No compiler state is indexed. -/
inductive OutputNeed384 where
  | ordinary (producer : Request) (dictionary : Dictionary) (ordinal : Nat) (row : Equation)
  | tagged (producer : Request) (dictionary : Dictionary) (ordinal : Nat) (row : AuthoredNominal)

def OutputNeed384.producer : OutputNeed384 → Request
  | .ordinary producer _ _ _ | .tagged producer _ _ _ => producer

def OutputNeed384.dictionary : OutputNeed384 → Dictionary
  | .ordinary _ dictionary _ _ | .tagged _ dictionary _ _ => dictionary

/-- Same-state literal emission, not proof of producer completion.
This type intentionally excludes raw read success and physical release. -/
inductive LiteralEmission384 (ordinary : LogicalOutputEquation383)
    (tagged : ChosenTaggedBinding383) (s : State) : OutputNeed384 → Type where
  | ordinary :
      LogicalOutputLink383 ordinary s q d i row →
      row ∈ s.current.ordinary.equations →
      LiteralEmission384 ordinary tagged s (.ordinary q d i row)
  | tagged :
      LogicalTaggedUnaryOutput383 tagged s q d i row →
      row ∈ s.current.visible →
      LiteralEmission384 ordinary tagged s (.tagged q d i row)

/-- A positive interface; a real final candidate verdict including all
visible alternatives and required K2/pending priorities remains to be
supplied. A matching rule does not justify arbitrary output choices. -/
abbrev ExactSelectedRule384 := State → Request → List OutputNeed384 → Nat → List Request → Prop

mutual
inductive ExactSelected384 (source : ExactSelectedRule384)
    (ordinary : LogicalOutputEquation383) (tagged : ChosenTaggedBinding383) (s : State) :
    Request → Dictionary → Type where
  | selected :
      source s q deps key kids →
      ExactSupportForest384 source ordinary tagged s deps →
      ExactWhereForest384 source ordinary tagged s kids whereDicts →
      ExactSelected384 source ordinary tagged s q (.node key whereDicts)

inductive ExactSupportForest384 (source : ExactSelectedRule384)
    (ordinary : LogicalOutputEquation383) (tagged : ChosenTaggedBinding383) (s : State) :
    List OutputNeed384 → Type where
  | nil : ExactSupportForest384 source ordinary tagged s []
  | cons :
      LiteralEmission384 ordinary tagged s need →
      ExactSelected384 source ordinary tagged s need.producer need.dictionary →
      ExactSupportForest384 source ordinary tagged s rest →
      ExactSupportForest384 source ordinary tagged s (need::rest)

inductive ExactWhereForest384 (source : ExactSelectedRule384)
    (ordinary : LogicalOutputEquation383) (tagged : ChosenTaggedBinding383) (s : State) :
    List Request → List Dictionary → Type where
  | nil : ExactWhereForest384 source ordinary tagged s [] []
  | cons :
      ExactSelected384 source ordinary tagged s q d →
      ExactWhereForest384 source ordinary tagged s qs ds →
      ExactWhereForest384 source ordinary tagged s (q::qs) (d::ds)
end

structure ExactSupport384 (source : ExactSelectedRule384)
    (ordinary : LogicalOutputEquation383) (tagged : ChosenTaggedBinding383) (s : State)
    (need : OutputNeed384) where
  emission : LiteralEmission384 ordinary tagged s need
  proof : ExactSelected384 source ordinary tagged s need.producer need.dictionary

/-- Recover the exact cell, not a selection whose request happens to
agree but may have a different associated dictionary. -/
def exact_support_at384 {source ordinary tagged s needs}
    (forest : ExactSupportForest384 source ordinary tagged s needs)
    (i : Nat) {need : OutputNeed384} (atIndex : needs[i]? = some need) :
    ExactSupport384 source ordinary tagged s need := by
  cases forest with
  | nil => simp at atIndex
  | cons emitted selected later =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at atIndex
      subst need
      exact ⟨emitted,selected⟩
    | succ i =>
      exact exact_support_at384 later i (by simpa using atIndex)

/-- Erasing producer dictionary and literal output from indices yields
C383's positive source-rule interface. Erasure is one-way; one cannot
reconstruct exact support from the projected request list. -/
def ForgetExactRule384 (source : ExactSelectedRule384) : SelectedSourceRule383 :=
  fun s q deps key kids =>
    ∃ exact, exact.map OutputNeed384.producer = deps ∧ source s q exact key kids

/-- Structural projection. The result dictionary comes from exactly
the ordered where forest, not from the auxiliary support list. -/
noncomputable def erase_exact_selected384 {source ordinary tagged s q d}
    (p : ExactSelected384 source ordinary tagged s q d) :
    SelectedSourceProof383 (ForgetExactRule384 source) s q d := by
  exact ExactSelected384.rec
    (motive_1 := fun q d _ => SelectedSourceProof383 (ForgetExactRule384 source) s q d)
    (motive_2 := fun needs _ => Σ ds, SelectedSourceForest383
      (ForgetExactRule384 source) s (needs.map OutputNeed384.producer) ds)
    (motive_3 := fun qs ds _ => SelectedSourceForest383
      (ForgetExactRule384 source) s qs ds)
    (fun rule _ _ aux kids =>
      .selected ⟨_,rfl,rule⟩ aux.2 kids)
    ⟨[],.nil⟩
    (fun _ _ _ proof rest => ⟨_,.cons proof rest.2⟩)
    .nil
    (fun _ _ proof rest => .cons proof rest)
    p

theorem exact_selected_projects_literal_where384 {source ordinary tagged s q d}
    (p : ExactSelected384 source ordinary tagged s q d) :
    ∃ t : CommonRoleOutermostResolver.Tree,
      CommonRoleOutermostResolver.Resolves
        (SupportedSelectedFrontier383 (ForgetExactRule384 source) s) q t ∧
      CommonRoleOutermostResolver.Summarizes t (.selected d) :=
  selected_proof_projects_literal_where383 (erase_exact_selected384 p)

end Yulang.GeneralDeclarativeI65
