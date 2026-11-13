import Yulang.GeneralNominalFreshPumpDeclarations
import Yulang.GeneralNominalValueSteps
import Yulang.GeneralNominalOutputGrowthModels

/-! The algebraic obstruction behind the fresh analysis: one fixed checked
source, arbitrarily long consistent nominal output prefixes, and accumulator
values that cannot be covered by a finite extensional basis. These statements
do not assert that the entire output prefix is a sequence of solver updates. -/
set_option linter.unusedSimpArgs false
namespace Yulang.GeneralNominalFreshPump
open GeneralNominalFreshPumpDeclarations
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralNominalSaturationState CommonNominalFullCarrier
open GeneralNominalOutputGrowth (tower tower_equivalent)

abbrev base := GeneralNominalOutputGrowthModels.base 6
abbrev view := GeneralNominalOutputGrowthModels.view 6
abbrev descriptor (child : Fin 8) : GeneralNominalState.Descriptor 8 :=
  ⟨0,⟨[.type],0⟩,[.type (child,child)],rfl⟩
abbrev entries (slot : Fin 8) : Option (GeneralNominalState.Descriptor 8) :=
  if slot = 0 then some (descriptor 1)
  else if slot = 1 then some (descriptor 2)
  else if slot = 2 then some (descriptor 3)
  else if slot = 4 then some (descriptor 5)
  else if slot = 6 then some (descriptor 7) else none

abbrev state : GeneralNominalState.State where
  base := base
  view := view
  constructors := constructors
  nominals := entries
  catalogue := by
    intro slot desc recorded
    unfold entries at recorded
    repeat first
      | split at recorded
      | cases Option.some.inj recorded; rfl
      | cases recorded
  bodies_opaque := by intro _ _ _; rfl
  seed := 7

abbrev context : GeneralNominalCandidates.Context := ⟨state,GeneralNominalExamples.interpretation⟩
abbrev root : Occurrence roles :=
  ⟨8,⟨0,fun index => if index.val = 0 then (0,0) else if index.val = 1 then (4,4) else (6,6),
    [],by intro _ impossible; cases impossible⟩⟩
abbrev start := GeneralNominalSupport.initial context root
abbrev L (a : Ty) : Ty := nominal 0 [.inl a]

def model (a b u : Ty) : GeneralNominalCommonBridge.Assignment := fun source =>
  (match source with
    | 0 => L (L (L a))
    | 1 => L (L a)
    | 2 => L a
    | 3 => a
    | 4 => L b
    | 5 => b
    | 6 => L u
    | 7 => u
    | _ => .base .int,
    Common.rowEmpty)

theorem source_models (a b u : Ty) : GeneralNominalState.Models state (model a b u) := by
  refine ⟨⟨PresenceNormalForm.all_nil _ _,?_,?_⟩,?_,PresenceNormalForm.all_nil _ _⟩
  · intro _ _ impossible; cases impossible
  · intro _ member; cases member
  · intro slot desc recorded
    change entries slot = some desc at recorded
    unfold entries at recorded
    repeat first
      | split at recorded
      | (rename_i same; subst slot; cases Option.some.inj recorded
         apply (GeneralNominalState.denotes_singleton_exact base _ _ _ _ rfl).mpr
         exact ⟨subtype_refl _,subtype_refl _⟩)
      | cases recorded

theorem initial_source : GeneralNominalSourceFormation.InitialSource registry context root := by
  have member (slot : Fin 8) : slot.val ∈ GeneralNominalState.sources state :=
    List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨slot,rfl⟩)))
  refine ⟨rfl,⟨rfl,?_⟩,?_,?_,?_,rfl⟩
  · intro name primitive found
    change (if name = 2 then some (.scalar .int) else none) = some primitive at found
    split at found
    · rename_i same; subst name; cases Option.some.inj found
      exact ⟨⟨[],2⟩,rfl,rfl⟩
    · cases found
  · constructor
    · intro index
      change (if index.val = 0 then (0,0) else if index.val = 1 then (4,4) else (6,6)).1 ∈ _ ∧
        (if index.val = 0 then (0,0) else if index.val = 1 then (4,4) else (6,6)).2 ∈ _
      split <;> try split
      all_goals first
        | exact ⟨member 0,member 0⟩
        | exact ⟨member 4,member 4⟩
        | exact ⟨member 6,member 6⟩
    · intro output impossible; cases impossible
  · intro assignment valid index
    change Subtype (assignment (if index.val = 0 then (0,0) else if index.val = 1 then (4,4) else (6,6)).1).1
      (assignment (if index.val = 0 then (0,0) else if index.val = 1 then (4,4) else (6,6)).2).1
    split <;> try split
    all_goals exact subtype_refl _
  · intro identity present
    change identity ≤ 7
    simp only [GeneralNominalState.sources,state,List.mem_append,List.not_mem_nil,List.flatMap_nil,or_false] at present
    rcases present with first | last
    all_goals obtain ⟨slot,equal⟩ := List.mem_ofFn.mp ‹_›
    all_goals have bound := slot.isLt
    all_goals change slot.val < 8 at bound
    all_goals change slot.val = identity at equal
    all_goals omega

theorem formed : GeneralNominalValueSteps.SourceFormed registry root start := .initial context initial_source

theorem initial_models (a b u : Ty) : Models start.current (model a b u) :=
  (GeneralNominalSaturationState.initial_models context root _).mpr (source_models a b u)

def bind (a b m : Pattern) : Nat → Pattern
  | 0 => a
  | 1 => b
  | _ => m

/-- Two replenished constructors pay for one consumed constructor and one
new accumulator constructor. This is equality of the existing source patterns. -/
theorem pump_round (a b m : Pattern) :
    substArgs (bind (list (list a)) b m) recurChild.arguments =
      substArgs (bind a (list b) m) p.head := rfl

def iterate : Nat → Ty → Ty
  | 0, a => a
  | n+1, a => L (iterate n a)

theorem iterate_tower (n : Nat) : iterate n (.base .int) = tower n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg L ih

/-- Every finite number of output equations has solutions with arbitrary
terminal tail, accumulator leaf, and blocked input. There is no constraint on U. -/
theorem finite_prefix (horizon : Nat) (a b u : Ty) :
    ∃ tails middles accumulators : Nat → Ty,
      Models start.current (model (tails 0) b u) ∧
      (∀ n, n < horizon → tails n = L (middles n) ∧ middles n = L (tails (n+1))) ∧
      accumulators 0 = L b ∧
      (∀ n, accumulators (n+1) = L (accumulators n)) ∧
      (∀ n, accumulators n = iterate (n+1) b) := by
  refine ⟨(fun n => iterate (2*(horizon-n)) a),
    (fun n => L (iterate (2*(horizon-(n+1))) a)),
    (fun n => iterate (n+1) b),initial_models _ b u,?_,rfl,?_,?_⟩
  · intro n bounded
    have sizes : 2*(horizon-n) = 2*(horizon-(n+1))+2 := by omega
    dsimp only
    rw [sizes]
    exact ⟨rfl,rfl⟩
  · intro n; rfl
  · intro n; rfl

theorem accumulators_distinct (first last : Nat) :
    Equivalent (iterate (first+1) (.base .int)) (iterate (last+1) (.base .int)) ↔ first = last := by
  rw [iterate_tower,iterate_tower,tower_equivalent]
  omega

/-- Applies to retained actual origins, including nonpoint endpoint frames;
the two Denotes premises expose the precise operational bridge still needed. -/
theorem distinct_pending_inputs (models : GeneralNominalCommonBridge.Assignment → Prop)
    (first last : GeneralNominalDemandMerging.Site roles) (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : models assignment) (i j : Nat) (different : i ≠ j) (u v : Ty)
    (one : GeneralNominalDemandMerging.Denotes assignment first [tower (i+1),u])
    (two : GeneralNominalDemandMerging.Denotes assignment last [tower (j+1),v]) :
    ¬ GeneralNominalDemandMerging.SameInputs models first last := by
  apply GeneralNominalDemandMerging.different_inputs_prevent_merge models first last assignment valid _ _ one two
  intro equal
  cases equal with
  | cons head tail =>
    have same := (tower_equivalent _ _).mp head
    exact different (by omega)

private theorem finite_tower_bound (basis : List Ty) :
    ∃ bound : Nat, ∀ n value, value ∈ basis → Equivalent (tower n) value → n ≤ bound := by
  classical
  induction basis with
  | nil => exact ⟨0,by intro _ _ impossible; cases impossible⟩
  | cons value rest ih =>
    obtain ⟨bound,limited⟩ := ih
    by_cases hasHeight : ∃ k, Equivalent (tower k) value
    · obtain ⟨k,atHeight⟩ := hasHeight
      refine ⟨max k bound,?_⟩
      intro n actual present equal
      rcases List.mem_cons.mp present with rfl | member
      · have same := (tower_equivalent n k).mp
          ⟨subtype_trans equal.1 atHeight.2,subtype_trans atHeight.1 equal.2⟩
        subst n
        exact Nat.le_max_left _ _
      · exact Nat.le_trans (limited n actual member equal) (Nat.le_max_right _ _)
    · refine ⟨bound,?_⟩
      intro n actual present equal
      rcases List.mem_cons.mp present with rfl | member
      · exact False.elim (hasHeight ⟨n,equal⟩)
      · exact limited n actual member equal

/-- Even quotienting nominal values by the actual semantic equivalence leaves
infinitely many accumulator signatures. Counting only outer head tags loses
the distinctions required by same-input merging. -/
theorem no_finite_accumulator_basis :
    ¬ ∃ basis : List Ty, ∀ n, ∃ value ∈ basis, Equivalent (iterate (n+1) (.base .int)) value := by
  rintro ⟨basis,covers⟩
  obtain ⟨bound,limited⟩ := finite_tower_bound basis
  obtain ⟨value,member,equal⟩ := covers bound
  rw [iterate_tower] at equal
  have impossible := limited (bound+1) value member equal
  omega

end Yulang.GeneralNominalFreshPump
