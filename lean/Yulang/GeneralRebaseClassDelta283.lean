import Yulang.GeneralRebaseInstallCache283
import Yulang.GeneralRebaseCompiledInstall282

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseClassDelta283
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryAssociatedProvenance (Body lookup)
open GeneralNominalVersionedEffects231 (BodyHolds ClassEffects)
open GeneralSourceState (Output)
open GeneralNominalCenteredHeadOutputs (requests)
open GeneralNominalVersionedInstall232 (installCore requests_included)

def Bodies (plan : Plan roles) (asgn : Assignment) (outputs : Output → Prop) : Prop :=
  ∀ o, outputs o → ∀ body : Body,
    lookup roles plan.packet.declaration o.name = some body → BodyHolds plan o.target asgn body

def EqPairs (asgn : Assignment) (pair : Output → Output → Prop) : Prop :=
  ∀ a, ∀ b, pair a b → a.name = b.name → CommonNominalFullCarrier.Equivalent (asgn a.target).1 (asgn b.target).1

def Growth (plan : Plan roles) (asgn : Assignment)
    (old next : Output → Prop) : Prop :=
  Bodies plan asgn (fun o => next o ∧ ¬ old o) ∧
    EqPairs asgn (fun a b => next a ∧ next b ∧ (¬ old a ∨ ¬ old b))

theorem factor (plan : Plan roles) (asgn : Assignment)
    (old next : Output → Prop) (retain : ∀ o, old o → next o) :
    (Bodies plan asgn next ∧ EqPairs asgn (fun a b => next a ∧ next b)) ↔
      (Bodies plan asgn old ∧ EqPairs asgn (fun a b => old a ∧ old b)) ∧
        Growth plan asgn old next := by
  classical
  constructor
  · rintro ⟨bodies,eqs⟩
    exact ⟨⟨fun o prior => bodies o (retain o prior),
      fun a b old => eqs a b ⟨retain a old.1,retain b old.2⟩⟩,
      fun o fresh => bodies o fresh.1,fun a b fresh => eqs a b ⟨fresh.1,fresh.2.1⟩⟩
  · rintro ⟨⟨prior,priorPairs⟩,fresh,pairs⟩
    constructor
    · intro o used
      by_cases had : old o
      · exact prior o had
      · exact fresh o ⟨used,had⟩
    · intro a b used
      by_cases one : old a
      · by_cases two : old b
        · exact priorPairs a b ⟨one,two⟩
        · exact pairs a b ⟨used.1,used.2,Or.inr two⟩
      · exact pairs a b ⟨used.1,used.2,Or.inl one⟩

theorem class_factor (core next : GeneralNominalCenteredSteps.State roles) (focus : Occurrence roles)
    (plan : Plan roles) (asgn : Assignment)
    (retain : ∀ o ∈ requests core focus, o ∈ requests next focus) :
    ClassEffects next focus plan asgn ↔ ClassEffects core focus plan asgn ∧
      Growth plan asgn (· ∈ requests core focus) (· ∈ requests next focus) := by
  have split := factor plan asgn (· ∈ requests core focus) (· ∈ requests next focus) retain
  have same (s : GeneralNominalCenteredSteps.State roles) : ClassEffects s focus plan asgn ↔
      Bodies plan asgn (· ∈ requests s focus) ∧ EqPairs asgn (fun a b => a ∈ requests s focus ∧ b ∈ requests s focus) := by
    refine and_congr Iff.rfl ⟨?_,?_⟩
    · exact fun eq a b pair => eq a pair.1 b pair.2
    · exact fun eq a one b two => eq a b ⟨one,two⟩
  exact (same next).trans (split.trans (and_congr (same core).symm Iff.rfl))

theorem class_install (core : GeneralNominalCenteredSteps.State roles) (focus : Occurrence roles)
    (stored installing : Plan roles) (asgn : Assignment) :
    ClassEffects (installCore core installing) focus stored asgn ↔ ClassEffects core focus stored asgn ∧
      Growth stored asgn (· ∈ requests core focus) (· ∈ requests (installCore core installing) focus) :=
  class_factor core (installCore core installing) focus stored asgn (requests_included core installing)

end Yulang.GeneralRebaseClassDelta283
