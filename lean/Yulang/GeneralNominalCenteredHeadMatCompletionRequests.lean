import Yulang.GeneralNominalCenteredHeadMatCanonicalClosure

set_option backward.isDefEq.respectTransparency false

/-! Canonical invocation identities determine output request identities even
when input descriptors are revised. Installing child sites does not merge them
with an existing class. Revisited children carry the same requests. -/
namespace Yulang.GeneralNominalCenteredHeadMatCompletionRequests
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal
open GeneralNominalCenteredHeadMatStepHistory (Built)
variable {roles : Roles.RoleDecls}

def outputs (seed invocation : Nat) (declaration : Declaration) (clause : Clause) : List GeneralSourceState.Output :=
  clause.outputs.map fun equation => ⟨equation.name,
    GeneralDeclarationDemands.outputTarget declaration
      ⟨fun _ => (0,0),fun name => GeneralNominalIdentities.source seed (invocation,declaration.id,2,name,0)⟩
      (fun name => GeneralNominalIdentities.source seed (invocation,declaration.id,5,name,0)) equation⟩

def Formed (registry : Registry) (seed : Nat) (root focus : Occurrence roles) : Prop :=
  focus = root ∨ ∃ parent declaration, declaration ∈ registry.declarations ∧
    ∃ clause ∈ declaration.requirements, root.identity ≤ parent ∧
      focus.identity = GeneralNominalIdentities.source seed (parent,declaration.id,6,clause.id,0) ∧
      focus.demand.outputs = outputs seed parent declaration clause

theorem formed_above (formed : Formed registry seed root focus) : root.identity ≤ focus.identity := by
  rcases formed with rfl | ⟨parent,declaration,_,clause,_,lower,equal,_⟩
  · exact Nat.le_refl _
  · have bound := GeneralNominalIdentities.source_above_invocation seed (parent,declaration.id,6,clause.id,0)
    change parent < _ at bound
    omega

private theorem unique_key (key : α → Nat) (xs : List α) (unique : (xs.map key).Nodup)
    (one : a ∈ xs) (two : b ∈ xs) (equal : key a = key b) : a = b := by
  induction xs with
  | nil => cases one
  | cons head rest ih =>
      have pair := List.nodup_cons.mp unique
      rcases List.mem_cons.mp one with rfl | member
      · rcases List.mem_cons.mp two with rfl | member
        · rfl
        · exact False.elim (pair.1 (List.mem_map.mpr ⟨b,member,equal.symm⟩))
      · rcases List.mem_cons.mp two with rfl | other
        · exact False.elim (pair.1 (List.mem_map.mpr ⟨a,member,equal⟩))
        · exact ih pair.2 member other

theorem same_outputs (checked : Checked registry) (one : Formed registry seed root first)
    (two : Formed registry seed root last) (same : first.identity = last.identity) :
    first.demand.outputs = last.demand.outputs := by
  rcases one with rfl | ⟨parent,a,visibleA,clauseA,memberA,lowerA,idA,outputsA⟩
  · rcases two with rfl | ⟨parent,b,_,clauseB,_,lowerB,idB,_⟩
    · rfl
    · have above := GeneralNominalIdentities.source_above_invocation seed (parent,b.id,6,clauseB.id,0)
      change parent < _ at above
      omega
  · rcases two with rfl | ⟨other,b,visibleB,clauseB,memberB,lowerB,idB,outputsB⟩
    · have above := GeneralNominalIdentities.source_above_invocation seed (parent,a.id,6,clauseA.id,0)
      change parent < _ at above
      omega
    · have keys := (GeneralNominalIdentities.source_identity seed _ _).mp (idA.symm.trans (same.trans idB))
      have declarations : a = b := GeneralDictionaryEmissionPlans.declaration_key_unique registry checked a b
        visibleA visibleB (congrArg (fun key : GeneralNominalIdentities.Origin => key.2.1) keys)
      subst b
      have clauses : clauseA = clauseB := unique_key Clause.id a.requirements (checked.2 a visibleA).identified.1 memberA memberB
        (congrArg (fun key : GeneralNominalIdentities.Origin => key.2.2.2.1) keys)
      have parents := congrArg (fun key : GeneralNominalIdentities.Origin => key.1) keys
      change parent = other at parents
      rw [outputsA,outputsB,parents,clauses]

def Present (state : GeneralNominalCenteredSteps.State roles) (identity : Nat) : Prop :=
  ∃ site ∈ state.erased.current.sites, site.occurrence.identity = identity

structure Invariant (registry : Registry) (seed : Nat) (root : Occurrence roles)
    (state : GeneralNominalCenteredSteps.State roles) : Prop where
  raw : ∀ site ∈ state.erased.current.sites, Formed registry seed root site.occurrence
  centers : ∀ site ∈ state.sites, Formed registry seed root site.occurrence
  registered : ∀ site ∈ state.sites, Present state site.occurrence.identity
  aliases : ∀ pair ∈ state.erased.current.aliases, Present state pair.1 ∧ Present state pair.2
  seed_eq : state.erased.current.context.state.seed = seed

set_option linter.unusedSimpArgs false in
theorem emitted_formed (valid : Invariant registry seed root state)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state plan.packet.site.occurrence plan.packet.declaration.id plan)
    (member : site ∈ plan.emitted) : Formed registry seed root site.occurrence := by
  obtain ⟨clause,_,rfl⟩ := List.mem_map.mp member
  refine Or.inr ⟨plan.packet.site.occurrence.identity,plan.packet.declaration,frame.visible,
    clause.val,clause.property,formed_above (valid.raw _ frame.raw_recorded),?_,?_⟩
  · change GeneralNominalIdentities.source plan.packet.context.state.seed _ = _
    rw [frame.context_eq,valid.seed_eq]
    rfl
  · change clause.val.outputs.map _ = _
    unfold outputs
    apply List.map_congr_left
    intro equation _
    congr 1
    unfold GeneralDeclarationDemands.outputTarget
    cases GeneralDeclarationPatterns.normalize equation.rhs <;>
      simp only [GeneralNominalFeedbackSites.frame,GeneralNominalAllocation.frame,
        GeneralNominalAllocation.capture,GeneralNominalAllocation.allocation,GeneralNominalAllocation.source,
        GeneralNominalAllocation.origin,frame.context_eq,valid.seed_eq]

theorem installed_invariant (valid : Invariant registry seed root state)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state plan.packet.site.occurrence plan.packet.declaration.id plan) :
    Invariant registry seed root (installCore state plan) := by
  have present : ∀ identity, Present state identity → Present (installCore state plan) identity := by
    rintro identity ⟨site,member,same⟩
    exact ⟨site,List.mem_append_left _ member,same⟩
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro site member
    rcases List.mem_append.mp member with old | new
    · exact valid.raw site old
    · obtain ⟨center,emittedMember,rfl⟩ := List.mem_map.mp new
      exact emitted_formed valid frame emittedMember
  · intro site member
    exact (List.mem_append.mp member).elim (valid.centers site) (emitted_formed valid frame)
  · intro site member
    rcases List.mem_append.mp member with old | new
    · exact present _ (valid.registered site old)
    · exact ⟨site.observed,List.mem_append_right _ (List.mem_map.mpr ⟨site,new,rfl⟩),rfl⟩
  · intro pair member
    exact ⟨present _ (valid.aliases pair member).1,present _ (valid.aliases pair member).2⟩
  · change plan.packet.context.state.seed = seed
    rw [frame.context_eq,valid.seed_eq]

theorem invariant (built : Built registry context root state) : Invariant registry context.state.seed root state.core := by
  induction built with
  | initial =>
      refine ⟨?_,?_,?_,?_,rfl⟩
      · intro site member; cases List.mem_singleton.mp member; exact Or.inl rfl
      · intro site member; cases List.mem_singleton.mp member; exact Or.inl rfl
      · intro site member; cases List.mem_singleton.mp member
        exact ⟨GeneralNominalDemandMerging.pointSite root,List.mem_singleton_self _,rfl⟩
      · intro pair member; cases member
  | install _ effect snapshot registryEq ih =>
      exact installed_invariant ih (snapshot ▸ registryEq ▸ effect.frame)
  | merge _ one two _ ih =>
      refine ⟨ih.raw,ih.centers,ih.registered,?_,ih.seed_eq⟩
      intro pair member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨ih.registered _ one,ih.registered _ two⟩
      · exact ih.aliases pair member
  | context _ _ seed _ ih => exact ⟨ih.raw,ih.centers,ih.registered,ih.aliases,seed.trans ih.seed_eq⟩

theorem alias_present (valid : Invariant registry seed root state)
    (alias : GeneralNominalSaturationState.Alias state.erased.current first last)
    (present : Present state first) : Present state last := by
  have pair : first = last ∨ (Present state first ∧ Present state last) := by
    clear present
    induction alias with
    | refl => exact Or.inl rfl
    | edge member => exact Or.inr (valid.aliases _ member)
    | symm _ ih => exact ih.elim (fun equal => Or.inl equal.symm) (fun pair => Or.inr ⟨pair.2,pair.1⟩)
    | trans _ _ one two =>
        rcases one with rfl | one
        · exact two
        · rcases two with rfl | two
          · exact Or.inr one
          · exact Or.inr ⟨one.1,two.2⟩
  exact pair.elim (fun same => same ▸ present) And.right

theorem alias_same {one two : GeneralNominalSaturationState.State roles} (same : one.aliases = two.aliases)
    (first last : Nat) : GeneralNominalSaturationState.Alias one first last ↔ GeneralNominalSaturationState.Alias two first last := by
  have forward {one two : GeneralNominalSaturationState.State roles} (same : one.aliases = two.aliases)
      {first last} (alias : GeneralNominalSaturationState.Alias one first last) : GeneralNominalSaturationState.Alias two first last := by
    induction alias with
    | refl => exact .refl _
    | edge member => exact .edge (same ▸ member)
    | symm _ ih => exact .symm ih
    | trans _ _ one two => exact .trans one two
  exact ⟨forward same,forward same.symm⟩

theorem install_requests (checked : Checked registry) (valid : Invariant registry seed root state)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state plan.packet.site.occurrence plan.packet.declaration.id plan)
    (present : Present state focus.identity) (output) :
    output ∈ GeneralNominalCenteredHeadOutputs.requests (installCore state plan) focus ↔
      output ∈ GeneralNominalCenteredHeadOutputs.requests state focus := by
  have aliases : ∀ a b, GeneralNominalSaturationState.Alias (installCore state plan).erased.current a b ↔
      GeneralNominalSaturationState.Alias state.erased.current a b := alias_same rfl
  simp only [GeneralNominalCenteredHeadOutputs.mem_requests_iff,aliases]
  constructor
  · rintro ⟨site,member,alias,within⟩
    rcases List.mem_append.mp member with old | new
    · exact ⟨site,old,alias,within⟩
    · obtain ⟨center,emittedMember,rfl⟩ := List.mem_map.mp new
      obtain ⟨old,recorded,same⟩ := alias_present valid alias present
      have requests := same_outputs checked (valid.raw _ recorded) (emitted_formed valid frame emittedMember) same
      exact ⟨old,recorded,same.symm ▸ alias,requests.symm ▸ within⟩
  · rintro ⟨site,member,alias,within⟩
    exact ⟨site,List.mem_append_left _ member,alias,within⟩

end Yulang.GeneralNominalCenteredHeadMatCompletionRequests
