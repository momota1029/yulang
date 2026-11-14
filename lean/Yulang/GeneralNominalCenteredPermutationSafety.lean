import Yulang.GeneralNominalCenteredPermutationPlans
import Yulang.GeneralNominalCenteredPermutationApplicability

set_option backward.isDefEq.respectTransparency false

/-! The centered graph and trusted observation judgements are invariant under
one shared ledger pairing, in both directions. -/
namespace Yulang.GeneralNominalCenteredPermutationSafety
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralNominalLedgerPermutation (All₂)
open GeneralNominalCenteredLedgerPermutation
variable {roles : Roles.RoleDecls}
variable {relation : GeneralNominalSaturationState.Packet roles → GeneralNominalSaturationState.Packet roles → Prop}
variable {left right : State roles}

theorem plan_symm (pair : PlanPair relation a b) : PlanPair (fun p q => relation q p) b a :=
  ⟨pair.packet,pair.input.symm,fun m => (pair.inputs m).symm,fun m => (pair.outputs m).symm,
    fun m => (pair.equations m).symm,fun e => (pair.tests e).symm⟩

theorem symm (same : Related relation left right) : Related (fun p q => relation q p) right left := by
  refine ⟨same.erased.symm,fun site => (same.sites site).symm,?_,same.roots.symm⟩
  have swap : ∀ {xs ys}, All₂ (PlanPair relation) xs ys → All₂ (PlanPair (fun p q => relation q p)) ys xs := by
    intro xs ys pairs
    induction pairs with
    | nil => exact .nil
    | cons pair rest ih => exact .cons (plan_symm pair) ih
  exact swap same.plans

theorem graph_tests (same : Related relation left right) (entry) :
    entry ∈ (graph left).tests ↔ entry ∈ (graph right).tests := by
  constructor
  · intro member
    obtain ⟨plan,recorded,member⟩ := List.mem_flatMap.mp member
    obtain ⟨other,present,pair⟩ := GeneralNominalLedgerPermutation.all₂_left same.plans recorded
    exact List.mem_flatMap.mpr ⟨other,present,(pair.tests entry).mp member⟩
  · intro member
    obtain ⟨plan,recorded,member⟩ := List.mem_flatMap.mp member
    obtain ⟨other,present,pair⟩ := GeneralNominalLedgerPermutation.all₂_right same.plans recorded
    exact List.mem_flatMap.mpr ⟨other,present,(pair.tests entry).mpr member⟩

theorem graph_recorded (same : Related relation left right) (a b) :
    GeneralNominalCenteredGraph.Recorded (graph left) a b ↔ GeneralNominalCenteredGraph.Recorded (graph right) a b := by
  constructor
  · intro edge
    cases edge with
    | structural shape index member => exact .structural _ shape index ((graph_tests same _).mp member)
    | nominal name arity index member => exact .nominal _ name arity index ((graph_tests same _).mp member)
  · intro edge
    cases edge with
    | structural shape index member => exact .structural _ shape index ((graph_tests same _).mpr member)
    | nominal name arity index member => exact .nominal _ name arity index ((graph_tests same _).mpr member)

theorem graph_edge (same : Related relation left right) (a b) :
    GeneralNominalCenteredGraph.Edge (graph left) a b ↔ GeneralNominalCenteredGraph.Edge (graph right) a b := by
  have equal : ∀ a b, GeneralNominalCenteredGraph.Equal (graph left) a b ↔
      GeneralNominalCenteredGraph.Equal (graph right) a b := by
    intro a b
    simp only [GeneralNominalCenteredGraph.Equal,graph,same.models]
  simp only [GeneralNominalCenteredGraph.Edge,graph_recorded same,equal]

theorem graph_path (same : Related relation left right) (a b) :
    GeneralNominalCenteredGraph.Path (graph left) a b ↔ GeneralNominalCenteredGraph.Path (graph right) a b := by
  have forward : ∀ {xs ys : State roles}, Related relation xs ys → ∀ a b,
      GeneralNominalCenteredGraph.Path (graph xs) a b → GeneralNominalCenteredGraph.Path (graph ys) a b := by
    intro xs ys same a b path
    induction path with
    | nil => exact .nil _
    | cons edge _ ih => exact .cons ((graph_edge same _ _).mp edge) ih
  constructor
  · exact forward same a b
  · intro path
    induction path with
    | nil => exact .nil _
    | cons edge _ ih => exact .cons ((graph_edge same _ _).mpr edge) ih

theorem cyclic (same : Related relation left right) (origin) : Cyclic left origin ↔ Cyclic right origin := by
  have actual : GeneralNominalActualInspectionSteps.Cyclic left.erased.current origin ↔
      GeneralNominalActualInspectionSteps.Cyclic right.erased.current origin := by
    simp only [GeneralNominalActualInspectionSteps.Cyclic,GeneralNominalActualInspectionSteps.Represents,
      GeneralNominalDemandMerging.SameOrigin,same.erased.current.models,same.erased.current.recursAt]
  exact or_congr actual (by
    simp only [GeneralNominalCenteredGraph.Cyclic,graph_edge same,graph_path same]
    exact and_congr Iff.rfl (exists_congr (fun model => same.models model)))

theorem root_cycle (same : Related relation left right) (root : Occurrence roles) : RootCycle left root ↔ RootCycle right root := by
  simp only [RootCycle,same.sites,cyclic same]

theorem safe_metadata (same : Related relation left right) (plan : Plan roles) (allocated reserved) :
    Safe left plan ↔ Safe right (GeneralNominalCenteredPermutationPlans.metadata plan allocated reserved) := by
  unfold Safe
  rw [GeneralNominalCenteredPermutationPlans.inspection]
  simp only [GeneralNominalReportMetadata.report,cyclic same]

theorem head (same : GeneralNominalJournalPermutation.ContextPair one two) (identity test observation) :
    GeneralNominalSupport.Head one.state identity test observation ↔
      GeneralNominalSupport.Head two.state identity test observation := by
  obtain ⟨allocated,reserved,rfl,_,_⟩ := same.replace_form
  exact (GeneralNominalMetadataInspection.head one.state allocated reserved identity test observation).symm

theorem justified_forward (same : Related relation left right) (identity test)
    (valid : GeneralNominalCenteredSupport.HeadJustified left.erased left.sourceSites left.plans identity test) :
    GeneralNominalCenteredSupport.HeadJustified right.erased right.sourceSites right.plans identity test := by
  obtain ⟨facts,trusted,snapshot,observation,seen,sound⟩ := valid
  obtain ⟨other,paired,trusted⟩ := same.trusted trusted
  exact ⟨other,trusted,snapshot,observation,seen,fun model valid => sound model ((same.facts_models paired model).mpr valid)⟩

theorem justified (same : Related relation left right) (identity test) :
    GeneralNominalCenteredSupport.HeadJustified left.erased left.sourceSites left.plans identity test ↔
      GeneralNominalCenteredSupport.HeadJustified right.erased right.sourceSites right.plans identity test :=
  ⟨justified_forward same identity test,justified_forward (symm same) identity test⟩

theorem ready (same : Related relation left right) (identity) :
    GeneralNominalCenteredSupport.ReadyAt left.erased left.sourceSites left.plans identity ↔
      GeneralNominalCenteredSupport.ReadyAt right.erased right.sourceSites right.plans identity := by
  simp only [GeneralNominalCenteredSupport.ReadyAt,justified same,head same.erased.current.context]

end Yulang.GeneralNominalCenteredPermutationSafety
