import Yulang.GeneralDictionaryEqualityOrder

/-! A spanning-representative equality subphase: at most one novel equality
per source-list entry, rather than scanning all ordered pairs. The existence
proof uses classical semantic decisions; it is not an executable solver. -/
namespace Yulang.GeneralDictionaryEqualityLinearCompletion
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalFeedbackSteps GeneralDictionaryEqualityObservations
open GeneralDictionaryEqualityStepBound
variable {roles : Roles.RoleDecls}

private theorem raw_refl (state : State roles) (a : Nat) : RawEqual state a a :=
  fun _ _ => ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩
private theorem raw_symm {state : State roles} {a b : Nat} (h : RawEqual state a b) : RawEqual state b a :=
  fun m valid => ⟨(h m valid).2,(h m valid).1⟩
private theorem raw_trans {state : State roles} {a b c : Nat}
    (h : RawEqual state a b) (g : RawEqual state b c) : RawEqual state a c := by
  intro m valid
  exact ⟨CommonNominalFullCarrier.subtype_trans (h m valid).1 (g m valid).1,
    CommonNominalFullCarrier.subtype_trans (g m valid).2 (h m valid).2⟩
private theorem equal_via {state : State roles} {a b c : Nat}
    (h : GeneralNominalFeedbackK2.Equal state a b)
    (g : GeneralNominalFeedbackK2.Equal state a c) : GeneralNominalFeedbackK2.Equal state b c := by
  intro m valid
  exact ⟨CommonNominalFullCarrier.subtype_trans (h m valid).2 (g m valid).1,
    CommonNominalFullCarrier.subtype_trans (g m valid).2 (h m valid).1⟩

theorem Counted.snoc {registry : Registry} {root : Occurrence roles} {n before middle after}
    (path : Counted registry root n before middle)
    (step : GeneralNominalSupportSteps.Step registry root middle after) :
    Counted registry root (n+1) before after := by
  induction path with
  | refl => exact .cons step (.refl _)
  | cons first _ ih => exact .cons first (ih step)

/-- The property refers to the ORIGINAL semantic equality; Equates then
identifies it with the endpoint theory. Repeated names are harmless. -/
theorem complete_list_linear (registry : Registry) (root : Occurrence roles)
    (names : List Nat) (before : GeneralNominalSupport.Tracked roles)
    (registered : ∀ a ∈ names, a ∈ GeneralNominalState.sources before.current.context.state) :
    ∃ after n, Counted registry root n before after ∧ n ≤ names.length ∧
      (names ≠ [] → n < names.length) ∧ Equates before.current after.current ∧
      ∀ a ∈ names, ∀ b ∈ names,
        GeneralNominalFeedbackK2.Equal before.current a b → RawEqual after.current a b := by
  classical
  induction names with
  | nil => exact ⟨before,0,.refl _,Nat.le_refl _,(fun h => False.elim (h rfl)),.refl _,by simp⟩
  | cons a names ih =>
    obtain ⟨middle,n,path,bound,strict,cert,tail⟩ := ih (fun x hx => registered x (by simp [hx]))
    have close (after : GeneralNominalSupport.Tracked roles)
        (tailDone : ∀ x ∈ names, ∀ y ∈ names,
          GeneralNominalFeedbackK2.Equal before.current x y → RawEqual after.current x y)
        (headDone : ∀ y ∈ names, GeneralNominalFeedbackK2.Equal before.current a y → RawEqual after.current a y) :
        ∀ x ∈ a :: names, ∀ y ∈ a :: names,
          GeneralNominalFeedbackK2.Equal before.current x y → RawEqual after.current x y := by
      intro x hx y hy eq
      by_cases xa : x = a
      · subst x
        by_cases ya : y = a
        · subst y; exact raw_refl _ _
        · exact headDone y ((List.mem_cons.mp hy).resolve_left ya) eq
      · have hxTail := (List.mem_cons.mp hx).resolve_left xa
        by_cases ya : y = a
        · subst y
          exact raw_symm (headDone x hxTail (fun m valid => ⟨(eq m valid).2,(eq m valid).1⟩))
        · exact tailDone x hxTail y ((List.mem_cons.mp hy).resolve_left ya) eq
    by_cases representative : ∃ b ∈ names, GeneralNominalFeedbackK2.Equal before.current a b
    · obtain ⟨b,member,equal⟩ := representative
      have eqMiddle := (GeneralDictionaryEqualityOrder.semantic_equal_iff cert a b).mpr equal
      by_cases raw : RawEqual middle.current a b
      · refine ⟨middle,n,path,Nat.le_trans bound (by simp),(fun _ => Nat.lt_succ_of_le bound),cert,close middle tail ?_⟩
        intro y hy eq
        exact raw_trans raw (tail b member y hy (equal_via equal eq))
      · let after : GeneralNominalSupport.Tracked roles := {middle with current := equate middle.current a b}
        have one := (GeneralDictionaryEqualityStepBound.Equates.sources cert a).mpr (registered a (by simp))
        have two := (GeneralDictionaryEqualityStepBound.Equates.sources cert b).mpr (registered b (by simp [member]))
        have step : GeneralNominalSupportSteps.Step registry root middle after :=
          ⟨root,.root,.administrative root _ (.equate root a b one two eqMiddle raw)⟩
        have newCert : Equates middle.current after.current := .tail (.refl _) a b one two eqMiddle
        have tailDone : ∀ x ∈ names, ∀ y ∈ names,
            GeneralNominalFeedbackK2.Equal before.current x y → RawEqual after.current x y := by
          intro x hx y hy eq m valid
          exact tail x hx y hy eq m (GeneralDictionaryEqualityStepBound.Equates.raw_models newCert m valid)
        refine ⟨after,n+1,Counted.snoc path step,by simpa using Nat.succ_le_succ bound,
          (fun _ => by
            have nonempty : names ≠ [] := by intro empty; rw [empty] at member; cases member
            exact Nat.succ_lt_succ (strict nonempty)),cert.trans newCert,
          close after tailDone ?_⟩
        intro y hy eq
        exact raw_trans (equate_feedback middle.current a b) (tailDone b member y hy (equal_via equal eq))
    · refine ⟨middle,n,path,Nat.le_trans bound (by simp),(fun _ => Nat.lt_succ_of_le bound),cert,close middle tail ?_⟩
      intro y hy equal
      exact False.elim (representative ⟨y,hy,equal⟩)

/-- Every tracked journal has an actual equality-complete subphase of at most
N transitions, where N counts current source-list entries. Both the old
Models and all Joint/Evidence observations are retained by its certificate. -/
theorem complete_sources_linear (registry : Registry) (root : Occurrence roles)
    (before : GeneralNominalSupport.Tracked roles) :
    ∃ after n, Counted registry root n before after ∧
      n ≤ (GeneralNominalState.sources before.current.context.state).length ∧
      Equates before.current after.current ∧
      GeneralDictionaryFiniteEqualityCompletion.EqualityComplete after.current := by
  obtain ⟨after,n,path,bound,_,cert,done⟩ := complete_list_linear registry root
    (GeneralNominalState.sources before.current.context.state) before (fun _ h => h)
  refine ⟨after,n,path,bound,cert,?_⟩
  intro a one b two equal
  exact done a ((GeneralDictionaryEqualityStepBound.Equates.sources cert a).mp one)
    b ((GeneralDictionaryEqualityStepBound.Equates.sources cert b).mp two)
    ((GeneralDictionaryEqualityOrder.semantic_equal_iff cert a b).mp equal)

/-- A nonempty list needs at most N-1 equalities: its first representative
requires no edge. The empty-list case has zero steps (Nat subtraction). -/
theorem complete_sources_spanning_bound (registry : Registry) (root : Occurrence roles)
    (before : GeneralNominalSupport.Tracked roles) :
    ∃ after n, Counted registry root n before after ∧
      n ≤ (GeneralNominalState.sources before.current.context.state).length - 1 ∧
      Equates before.current after.current ∧
      GeneralDictionaryFiniteEqualityCompletion.EqualityComplete after.current := by
  let names := GeneralNominalState.sources before.current.context.state
  obtain ⟨after,n,path,bound,strict,cert,done⟩ := complete_list_linear registry root names before (fun _ h => h)
  refine ⟨after,n,path,?_,cert,?_⟩
  · change n ≤ names.length - 1
    by_cases empty : names = []
    · simp only [empty,List.length_nil] at bound ⊢
      exact bound
    · have less := strict empty
      omega
  · intro a one b two equal
    exact done a ((GeneralDictionaryEqualityStepBound.Equates.sources cert a).mp one)
      b ((GeneralDictionaryEqualityStepBound.Equates.sources cert b).mp two)
      ((GeneralDictionaryEqualityOrder.semantic_equal_iff cert a b).mp equal)

end Yulang.GeneralDictionaryEqualityLinearCompletion
