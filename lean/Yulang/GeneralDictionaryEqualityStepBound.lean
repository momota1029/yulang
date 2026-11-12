import Yulang.GeneralDictionaryFiniteEqualityCompletion

/-! A quantitative bound for the equality-only subphase, not a bound on full
support execution. Classical semantic tests are not claimed executable. -/
namespace Yulang.GeneralDictionaryEqualityStepBound
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalFeedbackSteps GeneralDictionaryEqualityObservations
variable {roles : Roles.RoleDecls}

/-- Count actual support transitions; skipped raw equalities cost zero. -/
inductive Counted (registry : Registry) (root : Occurrence roles) :
    Nat → GeneralNominalSupport.Tracked roles → GeneralNominalSupport.Tracked roles → Prop where
  | refl (state) : Counted registry root 0 state state
  | cons {before middle after n} : GeneralNominalSupportSteps.Step registry root before middle →
      Counted registry root n middle after → Counted registry root (n+1) before after

theorem Counted.steps {registry : Registry} {root : Occurrence roles} {n before after}
    (path : Counted registry root n before after) :
    B4Target.Steps (GeneralNominalSupportSteps.Step registry root) before after := by
  have append {a b c} (first : B4Target.Steps (GeneralNominalSupportSteps.Step registry root) a b)
      (last : B4Target.Steps (GeneralNominalSupportSteps.Step registry root) b c) :
      B4Target.Steps (GeneralNominalSupportSteps.Step registry root) a c := by
    induction last with
    | refl => exact first
    | tail _ step ih => exact .tail ih step
  induction path with
  | refl => exact .refl
  | cons step _ ih => exact append (.tail .refl step) ih

theorem Equates.sources {before after : State roles} (path : Equates before after) (source : Nat) :
    source ∈ GeneralNominalState.sources after.context.state ↔
    source ∈ GeneralNominalState.sources before.context.state := by
  induction path with
  | refl => rfl
  | tail _ a b one two _ ih =>
    exact (GeneralDictionaryJointEquality.sources_equate _ a b source one two).trans ih

theorem Equates.raw_models {before after : State roles} (path : Equates before after)
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models after.context.state model) :
    GeneralNominalState.Models before.context.state model := by
  induction path with
  | refl => exact valid
  | tail _ _ _ _ _ _ ih => exact ih ((GeneralNominalState.extend_models _ _ _ model).mp valid).1

/-- At most one actual transition per listed pair, including repeated pairs. -/
theorem complete_list_bounded (registry : Registry) (root : Occurrence roles)
    (pairs : List (Nat × Nat)) (before : GeneralNominalSupport.Tracked roles)
    (sources : ∀ p ∈ pairs, p.1 ∈ GeneralNominalState.sources before.current.context.state ∧
      p.2 ∈ GeneralNominalState.sources before.current.context.state)
    (equal : ∀ p ∈ pairs, GeneralNominalFeedbackK2.Equal before.current p.1 p.2) :
    ∃ after n, Counted registry root n before after ∧ n ≤ pairs.length ∧
      Equates before.current after.current ∧ ∀ p ∈ pairs, RawEqual after.current p.1 p.2 := by
  classical
  induction pairs generalizing before with
  | nil => exact ⟨before,0,.refl _,Nat.le_refl _,.refl _,by simp⟩
  | cons p ps ih =>
    have one := (sources p (by simp)).1
    have two := (sources p (by simp)).2
    have eq := equal p (by simp)
    by_cases raw : RawEqual before.current p.1 p.2
    · obtain ⟨after,n,path,bound,cert,done⟩ := ih before
        (fun q h => sources q (by simp [h])) (fun q h => equal q (by simp [h]))
      refine ⟨after,n,path,by simpa using Nat.le_trans bound (Nat.le_succ ps.length),cert,?_⟩
      intro q member
      rcases List.mem_cons.mp member with rfl | member
      · exact fun m valid => raw m (Equates.raw_models cert m valid)
      · exact done q member
    · let next : GeneralNominalSupport.Tracked roles :=
        {before with current := equate before.current p.1 p.2}
      have step : GeneralNominalSupportSteps.Step registry root before next :=
        ⟨root,.root,.administrative root _ (.equate root p.1 p.2 one two eq raw)⟩
      have cert : Equates before.current next.current := .tail (.refl _) p.1 p.2 one two eq
      obtain ⟨after,n,path,bound,tail,done⟩ := ih next
        (fun q h => ⟨(Equates.sources cert q.1).mpr (sources q (by simp [h])).1,
          (Equates.sources cert q.2).mpr (sources q (by simp [h])).2⟩)
        (fun q h m valid => equal q (by simp [h]) m ((cert.models m).mp valid))
      refine ⟨after,n+1,.cons step path,by simpa using Nat.succ_le_succ bound,cert.trans tail,?_⟩
      intro q member
      rcases List.mem_cons.mp member with rfl | member
      · exact fun m valid => equate_feedback before.current q.1 q.2 m (Equates.raw_models tail m valid)
      · exact done q member

/-- A journal with N source-list entries admits an equality-complete endpoint
in at most N² real support steps. Duplicates only overestimate this bound.
This is NOT a complexity bound for deciding semantic Equal or full execution. -/
theorem complete_sources_quadratic (registry : Registry) (root : Occurrence roles)
    (before : GeneralNominalSupport.Tracked roles) :
    ∃ after n, Counted registry root n before after ∧
      n ≤ (GeneralNominalState.sources before.current.context.state).length ^ 2 ∧
      Equates before.current after.current ∧
      GeneralDictionaryFiniteEqualityCompletion.EqualityComplete after.current := by
  classical
  let sources := GeneralNominalState.sources before.current.context.state
  let product := sources.flatMap (fun a => sources.map (fun b => (a,b)))
  let pairs := product.filter (fun p => decide (GeneralNominalFeedbackK2.Equal before.current p.1 p.2))
  have member (p : Nat × Nat) : p ∈ pairs ↔
      p.1 ∈ sources ∧ p.2 ∈ sources ∧ GeneralNominalFeedbackK2.Equal before.current p.1 p.2 := by
    rcases p with ⟨a,b⟩
    simp [pairs,product,List.mem_flatMap,List.mem_map,Prod.mk.injEq,and_assoc]
  have product_length (xs ys : List Nat) :
      (xs.flatMap (fun a => ys.map (fun b => (a,b)))).length = xs.length * ys.length := by
    induction xs with
    | nil => simp
    | cons a xs ih => simp [List.flatMap_cons,ih,Nat.succ_mul,Nat.add_comm]
  obtain ⟨after,n,path,bound,cert,done⟩ := complete_list_bounded registry root pairs before
    (fun p h => ⟨((member p).mp h).1,((member p).mp h).2.1⟩)
    (fun p h => ((member p).mp h).2.2)
  refine ⟨after,n,path,?_,cert,?_⟩
  · have filtered : pairs.length ≤ product.length := List.length_filter_le _ _
    have size : product.length = sources.length ^ 2 := by
      simpa [product,Nat.pow_succ,Nat.pow_zero] using product_length sources sources
    exact size ▸ (Nat.le_trans bound filtered)
  · intro first one last two equal
    apply done (first,last)
    apply (member _).mpr
    exact ⟨(Equates.sources cert first).mp one,(Equates.sources cert last).mp two,
      fun model valid => equal model ((cert.models model).mpr valid)⟩

end Yulang.GeneralDictionaryEqualityStepBound
