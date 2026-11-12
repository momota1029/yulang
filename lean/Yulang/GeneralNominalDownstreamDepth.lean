import Yulang.GeneralNominalDownstreamSupport

/-! Grounded support has finite depth at a fixed journal snapshot. The proof
uses the finite stored dependency pool, not finiteness of all possible refresh
certificates. This is not a bound shared by successive installation states. -/
namespace Yulang.GeneralNominalDownstreamDepth
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalSupportChoices GeneralNominalDownstreamSupport

variable {roles : Roles.RoleDecls} {registry : Registry} {state : Tracked roles} {producer : Occurrence roles}

/-- Depth counts output-dependency expansions; discharged producers need none. -/
def AtDepth (registry : Registry) (state : Tracked roles) : Nat → Occurrence roles → Prop
  | 0, producer => Discharged state.current producer
  | depth+1, producer => Discharged state.current producer ∨
      ∀ child, Waiting state.current producer child → ¬ Discharged state.current child →
        ∀ identity test, Need registry state child identity test →
          ∃ support, HeadSupported state support identity test ∧
            ∀ dependency ∈ support, AtDepth registry state depth dependency

theorem depth_step (depth : Nat) (known : AtDepth registry state depth producer) :
    AtDepth registry state (depth+1) producer := by
  induction depth generalizing producer with
  | zero => exact Or.inl known
  | succ depth ih =>
    rcases known with done | heads
    · exact Or.inl done
    · exact Or.inr (fun child path unresolved identity test needed => by
        obtain ⟨support,entailed,previous⟩ := heads child path unresolved identity test needed
        exact ⟨support,entailed,fun dependency member => ih (previous dependency member)⟩)

theorem depth_mono (bound : first ≤ last) (known : AtDepth registry state first producer) :
    AtDepth registry state last producer := by
  induction bound with
  | refl => exact known
  | step _ ih => exact depth_step _ ih

private theorem finite_bound (list : List α) (claim : Nat → α → Prop)
    (mono : ∀ first last, first ≤ last → ∀ element, claim first element → claim last element)
    (existsDepth : ∀ element ∈ list, ∃ depth, claim depth element) :
    ∃ depth, ∀ element ∈ list, claim depth element := by
  induction list with
  | nil => exact ⟨0,by intro _ impossible; cases impossible⟩
  | cons head tail ih =>
    obtain ⟨one,first⟩ := existsDepth head (by simp)
    obtain ⟨rest,others⟩ := ih (fun element member => existsDepth element (by simp [member]))
    refine ⟨max one rest,?_⟩
    intro element member
    rcases List.mem_cons.mp member with rfl | later
    · exact mono one _ (Nat.le_max_left _ _) _ first
    · exact mono rest _ (Nat.le_max_right _ _) _ (others element later)

/-- The induction hypotheses are only needed for producers actually used by
some chosen explanation. Restricting to stored dependencies preserves every
entailed head and yields one finite maximum. -/
theorem grounded_depth (grounded : Grounded registry state producer) :
    ∃ depth, AtDepth registry state depth producer := by
  classical
  induction grounded with
  | discharged producer done => exact ⟨0,done⟩
  | provisional producer supports heads dependencies ih =>
    let used : Occurrence roles → Prop := fun dependency => ∃ child,
      Waiting state.current producer child ∧ ¬ Discharged state.current child ∧
      ∃ identity test, Need registry state child identity test ∧ dependency ∈ supports child identity test
    let pool := (dependencyPool state).filter (fun dependency => decide (used dependency))
    have depths : ∀ dependency ∈ pool, ∃ depth, AtDepth registry state depth dependency := by
      intro dependency member
      have occurs : used dependency := of_decide_eq_true (List.mem_filter.mp member).2
      obtain ⟨child,path,unresolved,identity,test,needed,present⟩ := occurs
      exact ih child path unresolved identity test needed dependency present
    obtain ⟨bound,uniform⟩ := finite_bound pool (fun depth dependency => AtDepth registry state depth dependency)
      (fun _ _ le _ proof => depth_mono le proof) depths
    refine ⟨bound+1,Or.inr ?_⟩
    intro child path unresolved identity test needed
    let support := supports child identity test
    obtain ⟨snapshot,observation,head,entailed⟩ := heads child path unresolved identity test needed
    refine ⟨restrict state support,⟨snapshot,observation,head,?_⟩,?_⟩
    · intro model valid
      exact entailed model ((slice_restrict state support model).mp valid)
    · intro dependency member
      have present := (restrict_mem state support dependency).mp member
      exact uniform dependency (List.mem_filter.mpr ⟨present.1,decide_eq_true
        ⟨child,path,unresolved,identity,test,needed,present.2⟩⟩)

theorem depth_grounded (known : AtDepth registry state depth producer) : Grounded registry state producer := by
  classical
  induction depth generalizing producer with
  | zero => exact .discharged _ known
  | succ depth ih =>
    rcases known with done | heads
    · exact .discharged _ done
    · let supports : Occurrence roles → Nat → GeneralNominalRecursiveInspection.Test → List (Occurrence roles) :=
        fun child identity test => if valid : Waiting state.current producer child ∧
          ¬ Discharged state.current child ∧ Need registry state child identity test then
            Classical.choose (heads child valid.1 valid.2.1 identity test valid.2.2) else []
      refine .provisional producer supports ?_ ?_
      · intro child path unresolved identity test needed
        dsimp only [supports]
        rw [dite_eq_left ⟨path,unresolved,needed⟩]
        exact (Classical.choose_spec (heads child path unresolved identity test needed)).1
      · intro child path unresolved identity test needed dependency member
        dsimp only [supports] at member
        rw [dite_eq_left ⟨path,unresolved,needed⟩] at member
        exact ih ((Classical.choose_spec (heads child path unresolved identity test needed)).2 dependency member)

theorem grounded_iff_depth : Grounded registry state producer ↔ ∃ depth, AtDepth registry state depth producer :=
  ⟨grounded_depth,fun ⟨_,known⟩ => depth_grounded known⟩

/-- A single depth suffices for all grounded producers recorded at this state.
Both the pool and this bound may change at the next installation. -/
theorem snapshot_bound (registry : Registry) (state : Tracked roles) :
    ∃ depth, ∀ producer ∈ dependencyPool state, Grounded registry state producer → AtDepth registry state depth producer := by
  apply finite_bound (dependencyPool state) (fun depth producer => Grounded registry state producer → AtDepth registry state depth producer)
  · intro first last le producer prior grounded
    exact depth_mono le (prior grounded)
  · intro producer _
    classical
    by_cases grounded : Grounded registry state producer
    · obtain ⟨depth,known⟩ := grounded_depth grounded
      exact ⟨depth,fun _ => known⟩
    · exact ⟨0,fun impossible => False.elim (grounded impossible)⟩

end Yulang.GeneralNominalDownstreamDepth
