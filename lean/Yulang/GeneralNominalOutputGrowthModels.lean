import Yulang.GeneralNominalOutputGrowth

/-! Finite separating models for the output-growth example. The same nominal
observations as feedback K2 decrease tower depth in a finite separating model;
therefore the model rules out every entailed cycle, including edges obtained
through equality. -/
namespace Yulang.GeneralNominalOutputGrowthModels

open GeneralNominalOutputGrowth CommonNominalFullCarrier
open GeneralDeclarationExamples (roles constructors)
open GeneralNominalProjections (Observes)
open GeneralNominalSaturationState GeneralSourceDictionaries

private theorem int_not_nominal (name : Nat) (arguments : List Argument) :
    ¬ Subtype (.base .int) (nominal name arguments) := by
  intro below
  exact (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (below 0) 0
    ⟨fun _ => .bottom,fun _ => []⟩ (.nominalHead name arguments.length) ⟨rfl,by simp⟩

theorem observation_decreases (model : GeneralNominalCommonBridge.Assignment)
    (depth : Nat → Nat) (values : ∀ source, (model source).1 = tower (depth source))
    (first last name index : Nat) (actual : Ty)
    (observed : Observes model (.argument (.source first) name index) (.inl actual))
    (same : Equivalent actual (model last).1) : depth last < depth first := by
  cases observed with
  | argument parent compared found =>
    cases parent
    rw [values first] at compared
    rw [values last] at same
    cases equation : depth first with
    | zero =>
      rw [equation] at compared
      exact False.elim (int_not_nominal _ _ compared.1)
    | succ previous =>
      rw [equation] at compared
      have invariant := (nominal_regular_invariant_exact _ _ _ _).mp compared.1
      have length := invariant.2.1
      have zero : index = 0 := by
        obtain ⟨bound,_⟩ := List.getElem?_eq_some_iff.mp found
        simp only [List.length_cons,List.length_nil] at length
        omega
      subst index
      have child := invariant.2.2 0 (.inl (tower previous)) (.inl actual) rfl found
      have equal := (tower_equivalent previous (depth last)).mp
        ⟨subtype_trans child.1 same.1,subtype_trans same.2 child.2⟩
      omega

theorem feedback_acyclic (state : State roleDecls)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model)
    (depth : Nat → Nat) (values : ∀ source, (model source).1 = tower (depth source))
    (noStructural : ∀ first last, ¬ GeneralNominalFeedbackK2.Structural state first last)
    (source : Nat) : ¬ GeneralNominalFeedbackK2.Cycle state source := by
  have decreasing : ∀ first last, GeneralNominalFeedbackK2.Edge state first last → depth last < depth first := by
    intro first last edge
    rcases edge.2.2 with structural | argument
    · exact False.elim (noStructural first last structural)
    · obtain ⟨name,index,actual,seen,same⟩ := GeneralNominalFeedbackK2.argument_sound argument model valid
      exact observation_decreases model depth values first last name index actual seen same
  have paths : ∀ first last, GeneralNominalFeedbackK2.Path state first last → depth last ≤ depth first := by
    intro first last path
    induction path with
    | nil => exact Nat.le_refl _
    | cons edge _ ih => exact Nat.le_trans ih (Nat.le_of_lt (decreasing _ _ edge))
  rintro ⟨next,edge,path⟩
  have one := decreasing _ _ edge
  have two := paths _ _ path
  omega

abbrev base (length : Nat) : GeneralSourceState.State where
  slots := length+2
  source := Fin.val
  source_injective := fun _ _ equal => Fin.ext equal
  rowSource := Fin.val
  ordinary := []
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro i; exact Fin.elim0 i
  heads := fun _ => .unresolved
  intervals := []
  heads_sound := by intro _ _ _ _ impossible; cases impossible
  intervals_sound := by intro _ _ _ impossible; cases impossible

abbrev view (length : Nat) : GeneralNormalizedObservation.Snapshot (base length) where
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro i; exact Fin.elim0 i
  canonical := by intro i; exact Fin.elim0 i
  heads := fun _ => .deferred .unresolved
  checked := by intro _ _ impossible; cases impossible

def descriptor (length : Nat) (index : Fin (length+2)) (bounded : index.val ≤ length) :
    GeneralNominalState.Descriptor (length+2) :=
  ⟨0,⟨[.type],0⟩,[.type (⟨index.val+1,by omega⟩,⟨index.val+1,by omega⟩)],rfl⟩

def source (length : Nat) : GeneralNominalState.State where
  base := base length
  view := view length
  constructors := constructors
  nominals := fun index => if bounded : index.val ≤ length then some (descriptor length index bounded) else none
  catalogue := by
    intro index d recorded
    split at recorded
    · have same := Option.some.inj recorded; subst d; rfl
    · cases recorded
  bodies_opaque := by intro _ _ _; rfl
  seed := length+1

theorem source_models (length : Nat) (model : GeneralNominalCommonBridge.Assignment) :
    GeneralNominalState.Models (source length) model ↔ PrefixModels length model := by
  constructor
  · intro valid index bounded
    let slot : Fin (length+2) := ⟨index,by omega⟩
    have recorded : (source length).nominals slot = some (descriptor length slot bounded) := dite_eq_left bounded
    exact (GeneralNominalState.denotes_singleton_exact (base length) model slot
      ⟨index+1,by change index+1 < length+2; omega⟩ (descriptor length slot bounded) rfl).mp
      (valid.2.1 slot _ recorded)
  · intro valid
    refine ⟨⟨PresenceNormalForm.all_nil _ _,?_,?_⟩,?_,PresenceNormalForm.all_nil _ _⟩
    · intro _ _ impossible; cases impossible
    · intro _ member; cases member
    · intro slot d recorded
      change (if bounded : slot.val ≤ length then some (descriptor length slot bounded) else none) = some d at recorded
      split at recorded
      · rename_i bounded
        have same := Option.some.inj recorded; subst d
        exact (GeneralNominalState.denotes_singleton_exact (base length) model slot
          ⟨slot.val+1,by change slot.val+1 < length+2; omega⟩
          (descriptor length slot bounded) rfl).mpr (valid slot.val bounded)
      · cases recorded

abbrev context (length : Nat) : GeneralNominalRecursiveCandidates.Context :=
  ⟨source length,GeneralNominalExamples.interpretation⟩

abbrev root (length : Nat) : Occurrence roles :=
  ⟨length+2,⟨1,fun _ => (length,length),[⟨0,length+1⟩],by
    intro output member; have same := List.mem_singleton.mp member; subst output; exact ⟨none,rfl⟩⟩⟩

abbrev snapshot (length : Nat) : State roles := initial (context length) (root length)

theorem snapshot_models (length : Nat) (model : GeneralNominalCommonBridge.Assignment) :
    Models (snapshot length) model ↔ PrefixModels length model :=
  (initial_models (context length) (root length) model).trans (source_models length model)

theorem snapshot_acyclic (length source : Nat) : ¬ GeneralNominalFeedbackK2.Cycle (snapshot length) source :=
  feedback_acyclic (snapshot length) (finiteModel length)
    ((snapshot_models length _).mpr (finite_prefix_models length)) (fun i => length+1-i)
    (fun _ => rfl) (by rintro _ _ ⟨_,_,⟨kind,_,_,_,_⟩,_,_⟩; exact Fin.elim0 kind) source

theorem raw_acyclic (length : Nat) (slot : Fin (source length).base.slots) :
    ¬ GeneralNominalCycleK2.Cycle (source length) slot := by
  have edgeDecreases : ∀ first last, GeneralNominalCycleK2.Edge (source length) first last →
      length+1-last.val < length+1-first.val := by
    intro first last edge
    rcases edge with ⟨kind,_,_,_,_⟩ | ⟨d,_,index,observed⟩
    · exact Fin.elim0 kind
    · obtain ⟨actual,seen,same⟩ := observed (finiteModel length)
        ((source_models length _).mpr (finite_prefix_models length))
      exact observation_decreases (finiteModel length) (fun i => length+1-i) (fun _ => rfl)
        first.val last.val d.declaration.name index actual seen same
  have paths : ∀ first last, GeneralNominalCycleK2.Path (source length) first last →
      length+1-last.val ≤ length+1-first.val := by
    intro first last path
    induction path with
    | nil => exact Nat.le_refl _
    | cons edge _ ih => exact Nat.le_trans ih (Nat.le_of_lt (edgeDecreases _ _ edge))
  rintro ⟨next,edge,path⟩
  have one := edgeDecreases _ _ edge
  have two := paths _ _ path
  omega

theorem not_rootK2 (length : Nat) : ¬ GeneralNominalFeedbackK2.RootK2 (snapshot length) (root length) := by
  rintro (⟨_,_,_,slot,_,cycle⟩ | ⟨_,_,_,cycle,_⟩)
  · exact raw_acyclic length slot (GeneralNominalCycleK2.recurs_cycle _ _ cycle)
  · exact snapshot_acyclic length _ cycle

theorem not_candidateK2 (length : Nat) :
    ¬ GeneralNominalFeedbackK2.CandidateK2 registry (snapshot length) (root length) := by
  rintro (⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ | ⟨_,_,_,_,_,_,_,_,visited,_,cycle,_⟩)
  · exact raw_acyclic length visited.1 (GeneralNominalCycleK2.recurs_cycle _ _ cycle)
  · exact snapshot_acyclic length _ cycle

theorem source_member (length : Nat) (slot : Fin (length+2)) :
    slot.val ∈ GeneralNominalState.sources (source length) :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_ofFn.mpr ⟨slot,rfl⟩)))

theorem metadata (length : Nat) : GeneralNominalRecursiveCandidates.Metadata registry (context length) :=
  ⟨rfl,GeneralNominalReadbackCounterexample.prepared.1.2⟩

theorem linked (length : Nat) : GeneralNominalState.Linked (source length) (root length).demand := by
  constructor
  · intro index
    exact ⟨source_member length ⟨length,by omega⟩,source_member length ⟨length,by omega⟩⟩
  · intro output member
    have same := List.mem_singleton.mp member; subst output
    exact source_member length ⟨length+1,by omega⟩

theorem initial_source (length : Nat) :
    GeneralNominalSourceFormation.InitialSource registry (context length) (root length) := by
  refine ⟨rfl,metadata length,linked length,(by intro _ _ _; exact subtype_refl _),?_,rfl⟩
  intro identity member
  change identity ≤ length+1
  simp only [GeneralNominalState.sources,source,List.mem_append,List.not_mem_nil,
    List.flatMap_nil,or_false] at member
  rcases member with first | last
  all_goals obtain ⟨slot,equal⟩ := List.mem_ofFn.mp ‹_›
  all_goals have bound := slot.isLt
  all_goals change slot.val < length+2 at bound
  all_goals change slot.val = identity at equal
  all_goals omega

theorem formed (length : Nat) : GeneralNominalFeedbackSteps.SourceFormed registry
    (root length) (snapshot length) := .initial (context length) (initial_source length)

theorem ready (length : Nat) : ¬ GeneralNominalState.RootPending (source length) (root length).demand := by
  rintro ⟨index,unknown⟩
  exact unknown ⟨⟨length,by change length < length+2; omega⟩,rfl,
    Or.inr ⟨descriptor length ⟨length,by omega⟩ (Nat.le_refl _),dite_eq_left (Nat.le_refl _)⟩⟩

end Yulang.GeneralNominalOutputGrowthModels
