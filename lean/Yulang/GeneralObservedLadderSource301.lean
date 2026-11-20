import Yulang.GeneralNominalOutputGrowthModels
import Yulang.GeneralNominalPeelingExamples

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralObservedLadderSource301
open GeneralDeclarationExamples (constructors)
open GeneralSourceState (equationAtoms)
open GeneralNominalOutputGrowth (PrefixModels tower)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
open Core.PresenceGeneration (TyTerm)

abbrev endpoint (n : Nat) : Fin (n+2) := ⟨n+1,by omega⟩

abbrev shapes (n : Nat) (i : Fin 0) : GeneralSourceState.Shape (n+2) := Fin.elim0 i

def heads (n : Nat) (slot : Fin (n+2)) : GeneralSourceState.Head (shapes n) :=
  if slot = endpoint n then .scalar .int else .unresolved

abbrev base (n : Nat) : GeneralSourceState.State where
  slots := n+2
  source := Fin.val
  source_injective := fun _ _ eq => Fin.ext eq
  rowSource := Fin.val
  ordinary := equationAtoms (endpoint n) (.base .int)
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro i; exact Fin.elim0 i
  heads := heads n
  intervals := []
  heads_sound := by
    intro m valid slot term equation
    by_cases scalar : slot = endpoint n
    · subst slot
      have eq : (.base .int : TyTerm (Fin (n+2))) = term := by
        simpa [heads,GeneralSourceState.Head.equation] using equation
      subst term
      exact (GeneralSourceState.equationAtoms_exact ..).mp valid
    · simp [heads,scalar,GeneralSourceState.Head.equation] at equation
  intervals_sound := by intro _ _ _ impossible; cases impossible

abbrev view (n : Nat) : GeneralNormalizedObservation.Snapshot (base n) where
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro i; exact Fin.elim0 i
  canonical := by intro i; exact Fin.elim0 i
  heads := fun slot => if slot = endpoint n then .scalar .int else .deferred .unresolved
  checked := by
    intro slot term found
    by_cases scalar : slot = endpoint n
    · subst slot
      have eq : (.base .int : TyTerm (Fin (n+2))) = term := by
        simpa [GeneralNormalizedObservation.Head.term] using found
      subst term
      exact .head (by simp [heads,GeneralSourceState.Head.equation])
    · simp [scalar,GeneralNormalizedObservation.Head.term,GeneralNormalizedObservation.Deferred.term] at found

def snapshot (n : Nat) : GeneralNominalState.State where
  base := base n
  view := view n
  constructors := constructors
  nominals := fun slot => if bound : slot.val ≤ n then
    some (GeneralNominalOutputGrowthModels.descriptor n slot bound) else none
  catalogue := by
    intro slot desc found
    split at found
    · cases Option.some.inj found; rfl
    · cases found
  bodies_opaque := by
    intro slot desc found
    change (if bound : slot.val ≤ n then
      some (GeneralNominalOutputGrowthModels.descriptor n slot bound) else none) = some desc at found
    split at found
    · rename_i bound
      have diff : slot ≠ endpoint n := by intro equal; cases equal; change n+1 ≤ n at bound; omega
      simp [view,diff]
    · cases found
  seed := n+1

theorem nominal_at (n i : Nat) (hi : i ≤ n) :
    (snapshot n).nominals ⟨i,by change i < n+2; omega⟩ =
      some (GeneralNominalOutputGrowthModels.descriptor n ⟨i,by omega⟩ hi) :=
  dite_eq_left hi

theorem scalar_at (n : Nat) : (snapshot n).view.heads (endpoint n) = .scalar .int := by
  simp [snapshot,view]

theorem scalar_model (n : Nat) (m : Assignment)
    (satisfies : GeneralNominalState.Models (snapshot n) m) :
    Equivalent (m (n+1)).1 (.base .int) := by
  exact GeneralNominalState.normalized_models (snapshot n) m satisfies
    (endpoint n) (.base .int) (by simp [snapshot,view,GeneralNormalizedObservation.Head.term])

theorem linear_model (n : Nat) (m : Assignment) (satisfies : GeneralNominalState.Models (snapshot n) m) :
    PrefixModels n m := by
  intro i hi
  let pos : Fin (n+2) := ⟨i,by omega⟩
  exact (GeneralNominalState.denotes_singleton_exact (base n) m pos
    ⟨i+1,by change i+1 < n+2; omega⟩ (GeneralNominalOutputGrowthModels.descriptor n pos hi) rfl).mp
    (satisfies.2.1 pos _ (nominal_at n i hi))

theorem models_exact (n : Nat) (m : Assignment) :
    GeneralNominalState.Models (snapshot n) m ↔
    PrefixModels n m ∧ Equivalent (m (n+1)).1 (.base .int) := by
  constructor
  · exact fun h => ⟨linear_model n m h,scalar_model n m h⟩
  · rintro ⟨linked,last⟩
    refine ⟨⟨?_,?_,?_⟩,?_,PresenceNormalForm.all_nil _ _⟩
    · intro atom present
      change atom ∈ equationAtoms (endpoint n) (.base .int) at present
      simp only [equationAtoms,List.mem_cons,List.not_mem_nil,or_false] at present
      rcases present with rfl|rfl
      · exact last.1
      · exact last.2
    · intro slot term eq
      change (heads n slot).equation = some term at eq
      by_cases yes : slot = endpoint n
      · subst slot
        have same : (.base .int : TyTerm (Fin (n+2))) = term := by
          simpa [heads,GeneralSourceState.Head.equation] using eq
        subst term
        exact last
      · simp [heads,yes,GeneralSourceState.Head.equation] at eq
    · intro _ impossible; cases impossible
    · intro slot desc found
      change (if h : slot.val ≤ n then
        some (GeneralNominalOutputGrowthModels.descriptor n slot h) else none) = some desc at found
      split at found
      · rename_i h
        cases Option.some.inj found
        exact (GeneralNominalState.denotes_singleton_exact (base n) m slot
          ⟨slot.val+1,by change slot.val+1 < n+2; omega⟩ (GeneralNominalOutputGrowthModels.descriptor n slot h) rfl).mpr
          (linked slot.val h)
      · cases found

theorem model_exists (n : Nat) :
    GeneralNominalState.Models (snapshot n) (GeneralNominalOutputGrowth.finiteModel n) := by
  refine (models_exact n _).mpr ⟨GeneralNominalOutputGrowth.finite_prefix_models n,?_⟩
  change Equivalent (tower (n+1-(n+1))) (.base .int)
  rw [Nat.sub_self]
  exact ⟨subtype_refl _,subtype_refl _⟩

theorem slot_model (n : Nat) (m : Assignment)
    (satisfies : GeneralNominalState.Models (snapshot n) m) (remaining : Nat) (cap : remaining ≤ n+1) :
    Equivalent (m (n+1-remaining)).1 (tower remaining) := by
  have facts := (models_exact n m).mp satisfies
  induction remaining with
  | zero => simpa only [Nat.sub_zero,tower] using facts.2
  | succ remaining ih =>
    have previous := ih (by omega)
    have position : n+1-(remaining+1) ≤ n := by omega
    have next : n+1-(remaining+1)+1 = n+1-remaining := by omega
    have linked := facts.1 _ position
    rw [next] at linked
    have tail := GeneralNominalPeelingExamples.nominal_congr previous 0
    exact ⟨subtype_trans linked.1 tail.1,subtype_trans tail.2 linked.2⟩

end Yulang.GeneralObservedLadderSource301
