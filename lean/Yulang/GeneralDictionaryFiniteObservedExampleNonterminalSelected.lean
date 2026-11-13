import Yulang.GeneralDictionaryFiniteObservedExampleNonterminal
import Yulang.GeneralNominalSupportExamples

namespace Yulang.GeneralDictionaryFiniteObservedExampleNonterminalSelected
open GeneralDictionaryFiniteObservedExampleNonterminal
open GeneralDictionaryFiniteObservedExample (model descriptor state_models)
open CommonNominalFullCarrier
open GeneralDeclarationExamples (roles)
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalSupport GeneralNominalSaturationState

private def height (source : Nat) : Nat := if source = 0 then 1 else 0

private theorem int_not_nominal (name : Nat) (args : List Argument) :
    ¬ Subtype (.base .int) (nominal name args) := by
  intro below
  exact (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (below 0) 0
    ⟨fun _ => .bottom,fun _ => []⟩ (.nominalHead name args.length) ⟨rfl,by simp⟩

theorem observation_decreases (first last name index : Nat) (actual : Ty)
    (observed : GeneralNominalProjections.Observes model (.argument (.source first) name index) (.inl actual))
    (same : Equivalent actual (model last).1) : height last < height first := by
  cases observed with
  | argument parent compared found =>
    cases parent
    by_cases zero : first = 0
    · subst first
      have invariant := (nominal_regular_invariant_exact _ _ _ _).mp compared.1
      have length := invariant.2.1
      have bound : index < 3 := by
        obtain ⟨bound,_⟩ := List.getElem?_eq_some_iff.mp found
        change 3 = _ at length
        omega
      have nth : GeneralDictionaryFiniteObservedExample.arguments[index]? = some (.inl (.base .int)) := by
        have cases : index = 0 ∨ index = 1 ∨ index = 2 := by omega
        rcases cases with rfl | rfl | rfl <;> rfl
      have child := invariant.2.2 index (.inl (.base .int)) (.inl actual) nth found
      have notzero : last ≠ 0 := by
        intro eq; subst last
        exact int_not_nominal _ _ (subtype_trans child.1 same.1)
      simp [height,notzero]
    · have int : (model first).1 = .base .int := by
        change (if first = 0 then nominal 0 GeneralDictionaryFiniteObservedExample.arguments else .base .int) = .base .int
        exact ite_eq_right zero
      rw [int] at compared
      exact False.elim (int_not_nominal _ _ compared.1)

private theorem raw_acyclic (slot : Fin source.base.slots) : ¬ GeneralNominalCycleK2.Cycle source slot := by
  have decreasing : ∀ first last, GeneralNominalMixedRecurrence.Edge source first last →
      height last.val < height first.val := by
    intro first last edge
    rcases edge with ⟨kind,_,_,_⟩ | argument
    · exact Fin.elim0 kind
    · obtain ⟨descriptor,recorded,index,actual,seen,same⟩ :=
        GeneralNominalMixedRecurrence.actual_edge_sound _ _ _ argument model source_models
      exact observation_decreases _ _ _ _ actual seen same
  have paths : ∀ first last, GeneralNominalMixedRecurrence.Path source first last → height last.val ≤ height first.val := by
    intro first last path
    induction path with
    | nil => exact Nat.le_refl _
    | cons edge _ ih => exact Nat.le_trans ih (Nat.le_of_lt (decreasing _ _ edge))
  rintro ⟨next,edge,path⟩
  have smaller := decreasing _ _ edge
  have larger := paths _ _ path
  omega

private theorem no_raw_recurs (slot : Fin source.base.slots) :
    ¬ GeneralNominalCycleK2.RecursAt source slot := by
  rintro (⟨child,edge,path⟩ | ⟨cycle,_⟩)
  · exact raw_acyclic slot ⟨child,GeneralNominalCycleK2.direct_edge_sound edge,GeneralNominalCycleK2.direct_path_sound path⟩
  · exact raw_acyclic slot cycle

private theorem no_feedback_cycle (identity : Nat) :
    ¬ GeneralNominalFeedbackK2.Cycle start.current identity := by
  have decreasing : ∀ first last, GeneralNominalFeedbackK2.Edge start.current first last → height last < height first := by
    intro first last edge
    rcases edge.2.2 with ⟨_,_,⟨kind,_,_,_⟩,_,_⟩ | argument
    · exact Fin.elim0 kind
    · obtain ⟨name,index,actual,seen,same⟩ := GeneralNominalFeedbackK2.argument_sound argument model initial_models
      exact observation_decreases _ _ _ _ actual seen same
  have paths : ∀ first last, GeneralNominalFeedbackK2.Path start.current first last → height last ≤ height first := by
    intro first last path
    induction path with
    | nil => exact Nat.le_refl _
    | cons edge _ ih => exact Nat.le_trans ih (Nat.le_of_lt (decreasing _ _ edge))
  rintro ⟨next,edge,path⟩
  have smaller := decreasing _ _ edge
  have larger := paths _ _ path
  omega

theorem no_root : ¬ GeneralNominalFeedbackK2.RootK2 start.current root := by
  rintro (⟨_,_,_,slot,_,cycle⟩ | ⟨_,_,index,cycle,_⟩)
  · exact no_raw_recurs slot cycle
  · exact no_feedback_cycle _ cycle

theorem no_candidate :
    ¬ GeneralNominalFeedbackK2.CandidateK2 registry start.current root := by
  rintro (⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ | ⟨_,_,_,_,_,_,_,_,visited,_,cycle,_⟩)
  · exact no_raw_recurs visited.1 cycle
  · exact no_feedback_cycle _ cycle


theorem unique : GeneralNominalLocalBoundary.Unique (GeneralNominalFeedbackK2.fields roles)
    registry start.current root declaration.id children := by
  refine ⟨survivor,?_⟩
  rintro key kids ⟨_,decl,visible,check,identity,role,bounds,located,ready,emitted⟩
  rcases List.mem_cons.mp visible with same | rest
  · subst decl
    have same : ([(0,0)] : List (Fin 2 × Fin 2)) = bounds := Option.some.inj located
    subst bounds
    exact ⟨identity.symm,emitted⟩
  · have same := List.mem_singleton.mp rest
    subst decl
    cases role

theorem selected : GeneralNominalFeedbackK2.Local registry start.current root
    (.selected declaration.id children) := by
  refine .selected ⟨root_ready,no_root,no_candidate,?_⟩ unique
  rintro (old | ⟨_,legacy⟩)
  · obtain ⟨_,decl,visible,check,role,_,absent⟩ := old
    rcases List.mem_cons.mp visible with same | rest
    · subst decl; exact absent prepared
    · have same := List.mem_singleton.mp rest
      subst decl
      cases role
  · rcases legacy with ⟨⟨_,_,_,_,_,⟨⟨kind,_,_⟩,_⟩⟩,_⟩ |
        ⟨⟨_,_,_,_,_,_,_,_,_,_,⟨⟨kind,_,_⟩,_⟩⟩,_⟩ <;> exact Fin.elim0 kind

theorem decisions : DecisionGuard start registry root [] := by
  refine ⟨(by intro _ impossible; cases impossible),?_,?_⟩
  · intro index
    exact source_ready start 0 (.nominal 0 3) _ _
      (Head.nominal (snapshot := source) 0 descriptor rfl)
      (Head.nominal (snapshot := source) 0 descriptor rfl) []
  · intro decl visible role bounds located slot member
    have bounded := slot.isLt
    change slot.val < 2 at bounded
    by_cases zero : slot.val = 0
    · have same : slot = (0 : Fin 2) := Fin.ext zero
      subst slot
      exact source_ready start 0 (.nominal 0 3) _ _
        (Head.nominal (snapshot := source) 0 descriptor rfl)
        (Head.nominal (snapshot := source) 0 descriptor rfl) []
    · have same : slot = (1 : Fin 2) := by apply Fin.ext; change slot.val = 1; omega
      subst slot
      exact source_ready start 1 (.scalar .int) _ _
        (Head.scalar (snapshot := source) 1 .int rfl)
        (Head.scalar (snapshot := source) 1 .int rfl) []

theorem support_selected : GeneralNominalSupportBoundary.Local registry start root
    (.selected declaration.id children) :=
  GeneralNominalSupportBoundary.selected_supported selected [] decisions
end Yulang.GeneralDictionaryFiniteObservedExampleNonterminalSelected
