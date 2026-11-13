import Yulang.GeneralNominalPointCycleInspection

/-! The existing K2 predicates miss this actual cycle: neither wrapper zero
nor the inspected lower bound three lies on the journal graph's cycle. -/
namespace Yulang.GeneralNominalPointCycleBounds
open GeneralNominalPointCycleSource GeneralNominalPointCycleInspection
open CommonNominalFullCarrier

private theorem variant_not_nominal (tag name : Nat) (payload : Ty) (arguments : List Argument) :
    ¬ Subtype (variant tag payload) (nominal name arguments) := by
  intro below
  exact (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (below 0) 0
    ⟨fun _ => .bottom,fun _ => []⟩ (.nominalHead name arguments.length) ⟨rfl,by simp⟩

private theorem nominal_not_bottom (name : Nat) (arguments : List Argument) :
    ¬ Subtype (nominal name arguments) .bottom := by
  intro below
  exact (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (below 0) 0
    ⟨fun _ => .bottom,fun _ => []⟩ (.base .int) trivial

private theorem variant_not_bottom (tag : Nat) (payload : Ty) :
    ¬ Subtype (variant tag payload) .bottom := by
  intro below
  exact (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (below 0) 0
    ⟨fun _ => .bottom,fun _ => []⟩ (.base .int) trivial

private theorem top_not_variant (tag : Nat) (payload : Ty) :
    ¬ Subtype .top (variant tag payload) := by
  intro below
  exact (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (below 0) 0
    ⟨fun _ => .bottom,fun _ => [.variant tag]⟩ (.role 0) (by exact List.mem_singleton_self _)

private theorem mu_not_nominal (name : Nat) (arguments : List Argument) :
    ¬ Subtype mu (nominal name arguments) :=
  fun below => variant_not_nominal 0 name mu arguments (subtype_trans mu_equation.2 below)

private theorem mu_not_lower : ¬ Equivalent mu (variant 0 .bottom) := by
  intro equal
  have below := (common_variant_iff 0 mu .bottom).mp (subtype_trans mu_equation.2 equal.1)
  exact variant_not_bottom 0 mu (subtype_trans mu_equation.2 below)

private theorem source_bound (identity : Nat)
    (member : identity ∈ GeneralNominalState.sources (state true)) : identity < 7 := by
  simp only [GeneralNominalState.sources,state,base,List.mem_append,List.mem_ofFn,List.not_mem_nil,
    List.flatMap_nil,or_false] at member
  rcases member with ⟨slot,rfl⟩ | ⟨slot,rfl⟩ <;> exact slot.isLt

private theorem argument_payload (first name index : Nat) (actual : Ty)
    (same : (model first).1 = box mu)
    (seen : GeneralNominalProjections.Observes model (.argument (.source first) name index) (.inl actual)) :
    Equivalent mu actual := by
  cases seen with
  | argument source equal found =>
    cases source
    rw [same] at equal
    have invariant := (nominal_regular_invariant_exact _ _ _ _).mp equal.1
    have size := invariant.2.1
    obtain ⟨bound,_⟩ := List.getElem?_eq_some_iff.mp found
    have zero : index = 0 := by simp only [List.length_cons,List.length_nil] at size; omega
    subst index
    exact invariant.2.2 0 _ _ rfl found

private theorem argument_target (first last : Nat) (bound : first < 7)
    (argument : GeneralNominalFeedbackK2.Argument refreshed.current first last) :
    Equivalent mu (model last).1 := by
  obtain ⟨name,index,observed⟩ := argument
  obtain ⟨actual,seen,equal⟩ := observed model refreshed_models
  have cases : first = 0 ∨ first = 1 ∨ first = 2 ∨ first = 3 ∨ first = 4 ∨ first = 5 ∨ first = 6 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have payload := argument_payload 0 name index actual rfl seen
    exact ⟨subtype_trans payload.1 equal.1,subtype_trans equal.2 payload.2⟩
  · have payload := argument_payload 1 name index actual rfl seen
    exact ⟨subtype_trans payload.1 equal.1,subtype_trans equal.2 payload.2⟩
  all_goals
    cases seen with
    | argument source compared found =>
      cases source
      first
      | exact False.elim (mu_not_nominal _ _ compared.1)
      | exact False.elim (variant_not_nominal _ _ _ _ compared.1)
      | exact False.elim (nominal_not_bottom _ _ compared.2)
      | exact False.elim (GeneralNominalTopObservation.top_not_nominal _ _ compared.1)

private theorem structural_targets (parent child : Fin 7) (edge : GeneralSourceK2.Child view parent child) :
    child = 2 ∨ child = 5 ∨ child = 6 := by
  obtain ⟨kind,children,head,index,same⟩ := edge
  change views parent = _ at head
  unfold views at head
  repeat first
    | split at head
    | (cases head; simp_all)
  cases head

private theorem target_not_zero_or_three (child : Fin 7)
    (target : child = 2 ∨ child = 5 ∨ child = 6)
    (equal : Equivalent (model child.val).1 (model last).1) (lastAt : last = 0 ∨ last = 3) : False := by
  rcases target with rfl | rfl | rfl <;> rcases lastAt with rfl | rfl
  · exact mu_not_nominal _ _ equal.1
  · exact mu_not_lower equal
  · exact nominal_not_bottom _ _ equal.2
  · exact variant_not_bottom _ _ equal.2
  · exact GeneralNominalTopObservation.top_not_nominal _ _ equal.1
  · exact top_not_variant _ _ equal.1

theorem edge_avoids_inspected (first last : Nat)
    (edge : GeneralNominalFeedbackK2.Edge refreshed.current first last) : last ≠ 0 ∧ last ≠ 3 := by
  have reject (position : last = 0 ∨ last = 3) : False := by
    rcases edge.2.2 with ⟨parent,child,structural,_,equal⟩ | argument
    · exact target_not_zero_or_three child (structural_targets parent child structural)
        (equal model refreshed_models) position
    · have equal := argument_target first last (source_bound first edge.1) argument
      rcases position with rfl | rfl
      · exact mu_not_nominal _ _ equal.1
      · exact mu_not_lower equal
  exact ⟨fun same => reject (Or.inl same),fun same => reject (Or.inr same)⟩

theorem feedback_off_cycle (identity : Nat) (position : identity = 0 ∨ identity = 3) :
    ¬ GeneralNominalFeedbackK2.Cycle refreshed.current identity := by
  have noEdge (first : Nat) : ¬ GeneralNominalFeedbackK2.Edge refreshed.current first identity := by
    intro edge
    have avoided := edge_avoids_inspected first identity edge
    rcases position with same | same
    · exact avoided.1 same
    · exact avoided.2 same
  have backwards (first last : Nat) (path : GeneralNominalFeedbackK2.Path refreshed.current first last) :
      last = identity → first = identity := by
    induction path with
    | nil => exact id
    | cons edge path ih =>
      intro final
      have target := ih final
      subst target
      exact False.elim (noEdge _ edge)
  rintro ⟨next,edge,path⟩
  have same := backwards next identity path rfl
  subst next
  exact noEdge identity edge

theorem raw_edge_feedback (first last : Fin 7)
    (edge : GeneralNominalMixedRecurrence.Edge (state true) first last) :
    GeneralNominalFeedbackK2.Edge refreshed.current first.val last.val := by
  refine ⟨source_member true first,source_member true last,?_⟩
  rcases edge with structural | argument
  · exact Or.inl ⟨first,last,structural,GeneralNominalFeedbackK2.equal_refl _ _,
      GeneralNominalFeedbackK2.equal_refl _ _⟩
  · exact Or.inr (GeneralNominalFeedbackK2.actual_argument refreshed.current first last argument)

theorem raw_path_feedback (first last : Fin 7)
    (path : GeneralNominalMixedRecurrence.Path (state true) first last) :
    GeneralNominalFeedbackK2.Path refreshed.current first.val last.val := by
  exact GeneralNominalMixedRecurrence.Path.rec
    (motive := fun first last _ => GeneralNominalFeedbackK2.Path refreshed.current first.val last.val)
    (fun _ => .nil _) (fun edge _ ih => .cons (raw_edge_feedback _ _ edge) ih) path

theorem raw_off_cycle (slot : Fin 7) (position : slot.val = 0 ∨ slot.val = 3) :
    ¬ GeneralNominalCycleK2.RecursAt (state true) slot := by
  intro cycle
  obtain ⟨next,edge,path⟩ := GeneralNominalCycleK2.recurs_cycle _ _ cycle
  exact feedback_off_cycle slot.val position ⟨next.val,raw_edge_feedback _ _ edge,raw_path_feedback _ _ path⟩

theorem not_rootK2 : ¬ GeneralNominalFeedbackK2.RootK2 refreshed.current root := by
  rintro (⟨_,_,index,slot,same,cycle⟩ | ⟨_,_,index,cycle,_⟩)
  · exact raw_off_cycle slot (Or.inl same) cycle
  · exact feedback_off_cycle 0 (Or.inl rfl) cycle

theorem arguments_exact : GeneralNominalRecursiveCandidates.arguments (context true) root = some [(0,0)] := by
  decide +kernel

theorem not_candidateK2 : ¬ GeneralNominalFeedbackK2.CandidateK2 registry refreshed.current root := by
  rintro (⟨_,d,member,_,_,_,bounds,located,visited,present,cycle⟩ |
    ⟨_,d,member,_,_,_,bounds,located,visited,present,cycle,_⟩)
  all_goals
    have decl := List.mem_singleton.mp member
    subst d
    have boundsEq : bounds = ([(0,0)] : List (Fin 7 × Fin 7)) := Option.some.inj (located.symm.trans arguments_exact)
    subst bounds
    change visited ∈ oldReport.inspected at present
    rw [old_inspected] at present
  · rcases List.mem_cons.mp present with same | rest
    · cases same; exact raw_off_cycle 0 (Or.inl rfl) cycle
    · cases List.mem_singleton.mp rest; exact raw_off_cycle 3 (Or.inr rfl) cycle
  · rcases List.mem_cons.mp present with same | rest
    · cases same; exact feedback_off_cycle 0 (Or.inl rfl) cycle
    · cases List.mem_singleton.mp rest; exact feedback_off_cycle 3 (Or.inr rfl) cycle

end Yulang.GeneralNominalPointCycleBounds
