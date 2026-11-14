import Yulang.GeneralNominalCenteredAdministrativePermutation

set_option backward.isDefEq.respectTransparency false

/-! Registry permutations preserve downstream needs, including all certified
observation views. Their well-founded value justifications retain each support. -/
namespace Yulang.GeneralNominalJournalPermutation.ContextPair
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSupport

theorem inspection (same : ContextPair first last) (pair : GeneralRegistryReordering.DeclarationReorders a b)
    (focus : Occurrence roles) (bounds : List (GeneralNominalInspection.Bounds first.state))
    (located : GeneralNominalRecursiveCandidates.arguments first focus = some bounds)
    (slot : Fin first.state.base.slots)
    (visited : slot ∈ readsMany first.state (GeneralNominalInspection.queries first.state first.interpretation a) bounds) :
    ∃ target : List (GeneralNominalInspection.Bounds last.state), ∃ next : Fin last.state.base.slots,
      GeneralNominalRecursiveCandidates.arguments last focus = some target ∧
      next ∈ readsMany last.state (GeneralNominalInspection.queries last.state last.interpretation b) target ∧
      last.state.base.source next = first.state.base.source slot := by
  obtain ⟨allocated,reserved,rfl,_,_⟩ := same.replace_form
  refine ⟨bounds,slot,located,?_,rfl⟩
  rw [GeneralNominalMetadataInspection.queries,GeneralNominalMetadataInspection.readsMany]
  simpa only [GeneralNominalInspection.queries,Declaration.normalHead,pair.head] using visited
end Yulang.GeneralNominalJournalPermutation.ContextPair

namespace Yulang.GeneralNominalLedgerPermutation.Related
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState GeneralNominalSupport
variable {roles : Roles.RoleDecls} {relation : Packet roles → Packet roles → Prop} {first last : Tracked roles}

theorem downstream_need_forward (same : Related relation first last) (order : GeneralRegistryReordering.Reorders r s)
    (needed : GeneralNominalDownstreamSupport.Need r first focus identity test) :
    GeneralNominalDownstreamSupport.Need s last focus identity test := by
  cases needed with
  | input index test available => exact .input index test ((same.available _ _).mp available)
  | inspection observed view declaration member role bounds located slot visited test available =>
    obtain ⟨other,path,pair⟩ := same.current.view view
    obtain ⟨next,present,moved⟩ := GeneralRegistryReordering.reorders_visible order declaration member
    obtain ⟨bounds,slot,located,visited,source⟩ := pair.context.inspection moved focus bounds located slot visited
    have available := (same.available _ _).mp available
    rw [← source] at available ⊢
    exact .inspection other path next present (moved.role.symm.trans role) bounds located slot visited test available

theorem downstream_need (same : Related relation first last) (order : GeneralRegistryReordering.Reorders r s)
    (focus identity test) : GeneralNominalDownstreamSupport.Need r first focus identity test ↔
      GeneralNominalDownstreamSupport.Need s last focus identity test :=
  ⟨same.downstream_need_forward order,same.symm.downstream_need_forward (GeneralRegistryChildOrder.reorders_symm order)⟩

theorem proper_waiting (same : Related relation first last) (producer focus) :
    GeneralNominalValueSupport.ProperWaiting first.current producer focus ↔ GeneralNominalValueSupport.ProperWaiting last.current producer focus := by
  simp only [GeneralNominalValueSupport.ProperWaiting,same.current.waiting,same.current.edges,same.current.discharged]

theorem value_need_forward (same : Related relation first last) (order : GeneralRegistryReordering.Reorders r s)
    (needed : GeneralNominalValueSupport.Need r first producer focus identity test) :
    GeneralNominalValueSupport.Need s last producer focus identity test := by
  cases needed with
  | head old => exact .head (same.downstream_need_forward order old)
  | value proper observed view index path test available =>
    obtain ⟨other,view,pair⟩ := same.current.view view
    exact .value ((same.proper_waiting _ _).mp proper) other view index ((pair.path _ _).mp path) test ((same.available _ _).mp available)
  | retained proper observed view site member focus position origin recorded source realizes path test available =>
    obtain ⟨other,view,pair⟩ := same.current.view view
    have models := funext (fun model => propext (pair.models model))
    exact .retained ((same.proper_waiting _ _).mp proper) other view site (pair.sites ▸ member) focus position origin recorded
      source (by unfold GeneralNominalValueSupport.Realizes; rw [← models]; exact realizes) ((pair.path _ _).mp path) test ((same.available _ _).mp available)

theorem value_need (same : Related relation first last) (order : GeneralRegistryReordering.Reorders r s)
    (producer focus identity test) : GeneralNominalValueSupport.Need r first producer focus identity test ↔
      GeneralNominalValueSupport.Need s last producer focus identity test :=
  ⟨same.value_need_forward order,same.symm.value_need_forward (GeneralRegistryChildOrder.reorders_symm order)⟩

theorem grounded_forward (same : Related relation first last) (order : GeneralRegistryReordering.Reorders r s)
    (grounded : GeneralNominalValueSupport.Grounded r first producer) : GeneralNominalValueSupport.Grounded s last producer := by
  induction grounded with
  | discharged producer done => exact .discharged producer ((same.current.discharged producer).mp done)
  | provisional producer supports heads dependencies ih =>
    refine .provisional producer supports ?_ ?_
    · intro child path unresolved identity test needed
      exact (same.head_supported _ _ _).mp (heads child ((same.current.waiting _ _).mpr path)
        (fun done => unresolved ((same.current.discharged _).mp done)) identity test ((same.value_need order _ _ _ _).mpr needed))
    · intro child path unresolved identity test needed dependency member
      exact ih child ((same.current.waiting _ _).mpr path) (fun done => unresolved ((same.current.discharged _).mp done))
        identity test ((same.value_need order _ _ _ _).mpr needed) dependency member

theorem grounded (same : Related relation first last) (order : GeneralRegistryReordering.Reorders r s) (producer) :
    GeneralNominalValueSupport.Grounded r first producer ↔ GeneralNominalValueSupport.Grounded s last producer :=
  ⟨same.grounded_forward order,same.symm.grounded_forward (GeneralRegistryChildOrder.reorders_symm order)⟩

theorem supported (same : Related relation first last) (order : GeneralRegistryReordering.Reorders r s) (support) :
    GeneralNominalValueSupport.Supported r first support ↔ GeneralNominalValueSupport.Supported s last support := by
  simp only [GeneralNominalValueSupport.Supported,same.grounded order]

end Yulang.GeneralNominalLedgerPermutation.Related
