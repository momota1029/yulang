import Yulang.GeneralNominalCenteredHeadMatStepJournal

set_option backward.isDefEq.respectTransparency false

/-! Invocation identity determines the role, even when descriptor revisions
give different demand records. Alias classes consequently retain only output
requests declared by their common role. -/
namespace Yulang.GeneralNominalCenteredHeadMatStepRoles
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal (State installCore)
variable {roles : Roles.RoleDecls}

def Origin (registry : Registry) (seed : Nat) (root focus : Occurrence roles) : Prop :=
  focus = root ∨ ∃ parent declaration, declaration ∈ registry.declarations ∧
    ∃ clause ∈ declaration.requirements, root.identity ≤ parent ∧
      focus.identity = GeneralNominalIdentities.source seed
        (GeneralNominalAllocation.origin parent declaration.id 6 clause.id 0) ∧ focus.demand.role = clause.role

theorem origin_above (origin : Origin registry seed root focus) : root.identity ≤ focus.identity := by
  rcases origin with rfl | ⟨parent,declaration,_,clause,_,lower,equal,_⟩
  · exact Nat.le_refl _
  · have bound := GeneralNominalIdentities.source_above_invocation seed
      (GeneralNominalAllocation.origin parent declaration.id 6 clause.id 0)
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

theorem origin_role (checked : Checked registry) (one : Origin registry seed root first)
    (two : Origin registry seed root last) (same : first.identity = last.identity) :
    first.demand.role = last.demand.role := by
  rcases one with rfl | ⟨parent,a,visibleA,clauseA,memberA,lowerA,idA,roleA⟩
  · rcases two with rfl | ⟨parent,b,visibleB,clauseB,memberB,lowerB,idB,roleB⟩
    · rfl
    · have above := GeneralNominalIdentities.source_above_invocation seed
        (GeneralNominalAllocation.origin parent b.id 6 clauseB.id 0)
      change parent < _ at above
      omega
  · rcases two with rfl | ⟨other,b,visibleB,clauseB,memberB,lowerB,idB,roleB⟩
    · have above := GeneralNominalIdentities.source_above_invocation seed
        (GeneralNominalAllocation.origin parent a.id 6 clauseA.id 0)
      change parent < _ at above
      omega
    · have keys := (GeneralNominalIdentities.source_identity seed _ _).mp (idA.symm.trans (same.trans idB))
      have declarations : a = b := GeneralDictionaryEmissionPlans.declaration_key_unique registry checked a b
        visibleA visibleB (congrArg (fun key : GeneralNominalIdentities.Origin => key.2.1) keys)
      subst b
      have clauses : clauseA = clauseB := unique_key Clause.id a.requirements
        (checked.2 a visibleA).identified.1 memberA memberB
        (congrArg (fun key : GeneralNominalIdentities.Origin => key.2.2.2.1) keys)
      exact roleA.trans (clauses ▸ roleB.symm)

noncomputable def color (registry : Registry) (seed : Nat) (root : Occurrence roles) (identity : Nat) : Nat := by
  classical
  exact if present : ∃ focus, Origin registry seed root focus ∧ focus.identity = identity then
    (Classical.choose present).demand.role else 0

theorem color_of_origin (checked : Checked registry) (origin : Origin registry seed root focus) :
    color registry seed root focus.identity = focus.demand.role := by
  classical
  unfold color
  rw [dite_eq_left ⟨focus,origin,rfl⟩]
  exact origin_role checked (Classical.choose_spec (show ∃ actual, Origin registry seed root actual ∧
    actual.identity = focus.identity from ⟨focus,origin,rfl⟩)).1 origin
    (Classical.choose_spec (show ∃ actual, Origin registry seed root actual ∧
      actual.identity = focus.identity from ⟨focus,origin,rfl⟩)).2

structure Invariant (registry : Registry) (seed : Nat) (root : Occurrence roles)
    (state : GeneralNominalCenteredSteps.State roles) : Prop where
  raw : ∀ site ∈ state.erased.current.sites, Origin registry seed root site.occurrence
  centers : ∀ site ∈ state.sites, Origin registry seed root site.occurrence
  aliases : ∀ pair ∈ state.erased.current.aliases, color registry seed root pair.1 = color registry seed root pair.2
  seed_eq : state.erased.current.context.state.seed = seed

theorem alias_color (valid : Invariant registry seed root state)
    (alias : GeneralNominalSaturationState.Alias state.erased.current first last) :
    color registry seed root first = color registry seed root last := by
  induction alias with
  | refl => rfl
  | edge present => exact valid.aliases _ present
  | symm _ ih => exact ih.symm
  | trans _ _ one two => exact one.trans two

theorem requests_declared (checked : Checked registry) (valid : Invariant registry seed root state)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state focus key plan) :
    GeneralNominalCenteredHeadDefaultSchemas.RequestsDeclared state focus plan := by
  intro output member
  obtain ⟨site,present,alias,within⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp member
  have focusOrigin : Origin registry seed root focus := frame.occurrence_eq ▸ valid.raw _ frame.raw_recorded
  have colors := alias_color valid alias
  rw [color_of_origin checked focusOrigin,color_of_origin checked (valid.raw _ present)] at colors
  have declared := site.occurrence.demand.declared output within
  simpa only [frame.role_eq,colors] using declared

theorem initial (context : GeneralNominalCandidates.Context) (root : Occurrence roles) :
    Invariant registry context.state.seed root (GeneralNominalCenteredSteps.initial context root) := by
  refine ⟨?_,?_,?_,rfl⟩
  · intro site member; cases List.mem_singleton.mp member; exact Or.inl rfl
  · intro site member; cases List.mem_singleton.mp member; exact Or.inl rfl
  · intro pair member; cases member

theorem emitted_origin (valid : Invariant registry seed root state)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state plan.packet.site.occurrence plan.packet.declaration.id plan)
    (member : site ∈ plan.emitted) : Origin registry seed root site.occurrence := by
  obtain ⟨clause,_,rfl⟩ := List.mem_map.mp member
  refine Or.inr ⟨plan.packet.site.occurrence.identity,plan.packet.declaration,frame.visible,
    clause.val,clause.property,origin_above (valid.raw _ frame.raw_recorded),?_,rfl⟩
  change GeneralNominalIdentities.source plan.packet.context.state.seed _ = _
  rw [frame.context_eq,valid.seed_eq]
  rfl

theorem install (valid : Invariant registry seed root state)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state plan.packet.site.occurrence plan.packet.declaration.id plan) :
    Invariant registry seed root (installCore state plan) := by
  refine ⟨?_,?_,valid.aliases,?_⟩
  · intro site member
    rcases List.mem_append.mp member with old | new
    · exact valid.raw site old
    · obtain ⟨center,present,rfl⟩ := List.mem_map.mp new
      exact emitted_origin valid frame present
  · intro site member
    exact (List.mem_append.mp member).elim (valid.centers site) (emitted_origin valid frame)
  · change plan.packet.context.state.seed = seed
    rw [frame.context_eq,valid.seed_eq]

theorem merge (checked : Checked registry) (valid : Invariant registry seed root state)
    (one : first ∈ state.sites) (two : last ∈ state.sites)
    (same : first.occurrence.demand.role = last.occurrence.demand.role) :
    Invariant registry seed root
      (GeneralNominalCenteredSteps.administrative state
        (GeneralNominalSaturationState.merge state.erased.current first.observed last.observed)) := by
  refine ⟨valid.raw,valid.centers,?_,valid.seed_eq⟩
  intro pair member
  rcases List.mem_cons.mp member with rfl | present
  · change color registry seed root first.occurrence.identity = color registry seed root last.occurrence.identity
    rw [color_of_origin checked (valid.centers first one),color_of_origin checked (valid.centers last two)]
    exact same
  · exact valid.aliases pair present

end Yulang.GeneralNominalCenteredHeadMatStepRoles
