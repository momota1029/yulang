import Yulang.GeneralNominalJournalPermutation

/-! Journal model equivalence and the retained observation core preserve the
actual source graph, including recovery of equal interval endpoints. -/
namespace Yulang.GeneralNominalJournalPermutation.Related
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
variable {roles : Roles.RoleDecls} {first last : State roles}

theorem argument (same : Related first last) (one two : Nat) :
    GeneralNominalFeedbackK2.Argument first one two ↔ GeneralNominalFeedbackK2.Argument last one two := by
  simp only [GeneralNominalFeedbackK2.Argument,same.models]

theorem structural (same : Related first last) (a b : Nat) :
    GeneralNominalFeedbackK2.Structural first a b ↔ GeneralNominalFeedbackK2.Structural last a b := by
  rcases first with ⟨one,packets,sites,edges,aliases⟩
  rcases last with ⟨two,otherPackets,otherSites,otherEdges,otherAliases⟩
  obtain ⟨allocated,reserved,contextEq,_,_⟩ := same.context.replace_form
  dsimp at contextEq
  subst two
  simp only [GeneralNominalFeedbackK2.Structural,same.equal,Metadata.replace,
    GeneralNominalMetadataEquivalence.replace]

theorem edge (same : Related first last) (one two : Nat) :
    GeneralNominalFeedbackK2.Edge first one two ↔ GeneralNominalFeedbackK2.Edge last one two := by
  simp only [GeneralNominalFeedbackK2.Edge,GeneralNominalMetadataEquivalence.sources same.context.state,
    same.structural,same.argument]

theorem path (same : Related first last) (one two : Nat) :
    GeneralNominalFeedbackK2.Path first one two ↔ GeneralNominalFeedbackK2.Path last one two := by
  have forward : ∀ {a b : State roles}, Related a b → ∀ {one two},
      GeneralNominalFeedbackK2.Path a one two → GeneralNominalFeedbackK2.Path b one two := by
    intro a b same one two path
    induction path with
    | nil => exact .nil _
    | cons edge _ ih => exact .cons ((same.edge _ _).mp edge) ih
  exact ⟨forward same,forward same.symm⟩

theorem cycle (same : Related first last) (source : Nat) :
    GeneralNominalFeedbackK2.Cycle first source ↔ GeneralNominalFeedbackK2.Cycle last source := by
  simp only [GeneralNominalFeedbackK2.Cycle,same.edge,same.path]

theorem recursAt (same : Related first last) (source : Nat) :
    GeneralNominalFeedbackK2.RecursAt first source ↔ GeneralNominalFeedbackK2.RecursAt last source := by
  simp only [GeneralNominalFeedbackK2.RecursAt,same.cycle,same.models]

theorem recover (same : Related first last) (site : GeneralNominalDemandMerging.Site roles) :
    GeneralNominalFeedbackSites.recover first site = GeneralNominalFeedbackSites.recover last site := by
  have origins : GeneralNominalFeedbackSites.recoverOrigin first site =
      GeneralNominalFeedbackSites.recoverOrigin last site := by
    funext index
    unfold GeneralNominalFeedbackSites.recoverOrigin
    split
    · rfl
    · have guard := same.equal (site.occurrence.demand.arguments index).1 (site.occurrence.demand.arguments index).2
      by_cases equal : GeneralNominalFeedbackSites.EndpointEqual first (site.occurrence.demand.arguments index)
      · simp only [equal,guard.mp equal,ite_true]
      · have other : ¬ GeneralNominalFeedbackSites.EndpointEqual last (site.occurrence.demand.arguments index) :=
          fun valid => equal (guard.mpr valid)
        simp only [equal,other,ite_false]
  unfold GeneralNominalFeedbackSites.recover
  congr 1
  exact congrArg List.ofFn origins

theorem sameInputs (same : Related first last) (a b : GeneralNominalDemandMerging.Site roles) :
    GeneralNominalFeedbackSites.SameInputs first a b ↔ GeneralNominalFeedbackSites.SameInputs last a b := by
  unfold GeneralNominalFeedbackSites.SameInputs
  rw [same.recover,same.recover]
  have models := funext (fun model => propext (same.models model))
  rw [models]

theorem committed (same : Related first last) (pair : PacketPair packet other) :
    GeneralNominalFeedbackSteps.Committed first packet ↔ GeneralNominalFeedbackSteps.Committed last other := by
  unfold GeneralNominalFeedbackSteps.Committed GeneralNominalCycleSteps.Committed
  simp only [same.models,pair.holds,pair.children,pair.site,same.edges]

end Yulang.GeneralNominalJournalPermutation.Related
