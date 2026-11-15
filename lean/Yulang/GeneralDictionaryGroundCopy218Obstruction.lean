import Yulang.GeneralDictionaryGroundCopy218Reobserve
import Yulang.GeneralDictionaryTopLevelSharing217

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralDictionaryGroundCopy218Obstruction
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters CommonNominalFullCarrier
open GeneralDictionaryGroundCopy218Source GeneralDictionaryGroundCopy218Install
open GeneralDictionaryGroundCopy218Reobserve
open GeneralNominalCenteredHeadMatStepJournal
open GeneralNominalRecursiveInspection GeneralNominalOriginTerms
open GeneralDictionaryTopLevelSharing217 (firstCenter secondCenter)
open GeneralNominalSaturationState (Alias Generated)
open GeneralNominalCommonBridge (Assignment)

abbrev leafDeclaration := GeneralNominalCenteredHeadAllocEncoding.declaration leaf

def stage (atoms : List (PresenceNormalForm.Atom Nat)) : State roles :=
  { reobserved with core := { reobserved.core with erased := { reobserved.core.erased with current :=
    { reobserved.core.erased.current with context :=
      ⟨{ reobserved.core.erased.current.context.state with ordinary := atoms },context.interpretation⟩ } } } }

abbrev initialAtoms := reobserved.core.erased.current.context.state.ordinary

theorem stage_initial : stage initialAtoms = reobserved := rfl

theorem sites_exact (atoms) : (stage atoms).core.sites = [plan.input,childSite] := rfl
theorem raw_sites_exact (atoms) : (stage atoms).core.erased.current.sites =
    [GeneralNominalDemandMerging.pointSite root,childSite.observed] := rfl
theorem plans_exact (atoms) : (stage atoms).core.plans = [plan] := rfl
theorem effects_exact (atoms) : (stage atoms).effects = [effect] := rfl
theorem aliases_empty (atoms) : (stage atoms).core.erased.current.aliases = [] := rfl
theorem edges_exact (atoms) : (stage atoms).core.erased.current.edges = [(root,childSite.occurrence)] := by
  change [] ++ packet.children.map (fun c => (root,c)) = _
  rw [show packet.children = children from rfl,children_exact]
  rfl

theorem model_if_atoms (atoms)
    (held : PresenceNormalForm.All CommonNominalFullCarrier.model model atoms) : Models (stage atoms) model := by
  refine ⟨⟨reobserved_model.1.1,reobserved_model.1.2.1,held⟩,
    reobserved_model.2.1,reobserved_model.2.2.1,reobserved_model.2.2.2.1,reobserved_model.2.2.2.2.1,?_⟩
  intro prior member
  have pair := reobserved_model.2.2.2.2.2 prior member
  exact ⟨pair.1,GeneralNominalCenteredHeadMatEffects.restrict
    (GeneralNominalCenteredHeadStepEffects.requests_subset_of_sites_aliases
      (before := (stage atoms).core) (after := reobserved.core)
      (fun _ h => h) (fun _ h => h)) pair.2⟩

theorem atoms_initial : PresenceNormalForm.All CommonNominalFullCarrier.model model initialAtoms :=
  reobserved_model.1.2.2

theorem stage_old_models {atoms} {given : Assignment} (held : Models (stage atoms) given) : Models reobserved given := by
  have packetHeld := held.2.2.2.2.1 plan (List.mem_singleton_self _)
  have ordinary := (GeneralNominalCenteredHeadMatStepPackets.private_models packetHeld).2.2
  refine ⟨⟨held.1.1,held.1.2.1,ordinary⟩,held.2.1,held.2.2.1,held.2.2.2.1,held.2.2.2.2.1,?_⟩
  intro prior member
  have pair := held.2.2.2.2.2 prior member
  exact ⟨pair.1,GeneralNominalCenteredHeadMatEffects.restrict
    (GeneralNominalCenteredHeadStepEffects.requests_subset_of_sites_aliases
      (before := reobserved.core) (after := (stage atoms).core)
      (fun _ h => h) (fun _ h => h)) pair.2⟩

theorem child_first : firstCenter childSite = plan.binder 0 := by
  simp [firstCenter,child_centers,List.ofFn_succ]
theorem child_second : secondCenter childSite = plan.binder 1 := by
  simp [secondCenter,child_centers,List.ofFn_succ]

theorem centers_different (given : Assignment)
    (held : GeneralNominalCenteredHeadMatStepPackets.Holds plan given) :
    ¬ Same given (.source (firstCenter childSite)) (.source (secondCenter childSite)) := by
  rw [child_first,child_second]
  intro same
  have schema := (GeneralNominalCenteredHeadMatStepPackets.head_equations held).2.2
  rw [head_schema] at schema
  have left := schema.2 ⟨0,.nominal (.source 6) 5 0,.actual⟩ (List.mem_cons_self)
  have right := schema.2 ⟨1,.nominal (.source 6) 5 1,.actual⟩
    (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  change Same given (.nominal (.source 6) 5 0) (.source (plan.binder 0)) at left
  change Same given (.nominal (.source 6) 5 1) (.source (plan.binder 1)) at right
  have rootEqual := root_fixed given held.1
  have firstSeen : Observes given (.nominal (.source 6) 5 0) GeneralDictionaryLooseVariant217.first :=
    .nominal (.source 6) rootEqual rfl
  have secondSeen : Observes given (.nominal (.source 6) 5 1) GeneralDictionaryLooseVariant217.second :=
    .nominal (.source 6) rootEqual rfl
  have a := left.2.2 _ _ firstSeen (.source _)
  have b := right.2.2 _ _ secondSeen (.source _)
  have middle := same.2.2 _ _ (.source _) (.source _)
  exact GeneralDictionaryLooseVariant217.unequal
    ⟨subtype_trans a.1 (subtype_trans middle.1 b.2),subtype_trans b.1 (subtype_trans middle.2 a.2)⟩

theorem key_leaf (visible : d ∈ registry.declarations) (key : d.id = 1) : d = leafDeclaration := by
  rcases List.mem_cons.mp visible with rfl | member
  · cases key
  · exact List.mem_singleton.mp member

theorem leaf_queries (current : GeneralNominalCandidates.Context) :
    GeneralNominalInspection.queries current.state current.interpretation leafDeclaration = [.variables [0],.variables [0]] := by
  simp [GeneralNominalInspection.queries,GeneralDeclarations.Declaration.normalHead,
    GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
    GeneralNominalInspection.translate,leafDeclaration,GeneralNominalCenteredHeadAllocEncoding.declaration]

theorem impossible_of_sites (state : State roles)
    (sites : state.core.sites = [plan.input,childSite]) (recorded : plan ∈ state.core.plans)
    (given : Assignment) (held : Models state given) :
    GeneralDictionarySharingObstruction217.Impossible registry state.core given childSite.occurrence 1 := by
  apply GeneralDictionaryTopLevelSharing217.impossible registry state given childSite.occurrence 1 0
  · intro declaration visible key
    cases key_leaf visible key
    exact leaf_queries _
  · intro site member equal
    rw [sites] at member
    rcases List.mem_cons.mp member with rfl | member
    · have mismatch := congrArg (fun o : Occurrence roles => o.demand.role) equal
      cases mismatch
    · cases List.mem_singleton.mp member
      exact centers_different given (held.2.2.2.2.1 plan recorded)

theorem impossible {atoms} (given : Assignment) (held : Models (stage atoms) given) :
    GeneralDictionarySharingObstruction217.Impossible registry (stage atoms).core given childSite.occurrence 1 :=
  impossible_of_sites (stage atoms) (sites_exact atoms) (List.mem_singleton_self _) given held

theorem no_output_conflict (atoms) :
    ¬ GeneralNominalCenteredHeadMatStepLocal.OutputConflict registry (stage atoms) childSite.occurrence 1 :=
  GeneralDictionarySharingObstruction217.no_output_conflict (fun given held => impossible given held)

theorem no_evidence {atoms} (given : Assignment) (held : Models (stage atoms) given) (dictionaries) :
    ¬ GeneralDictionaryTotalEvidence206.Evidence registry (stage atoms).core given childSite.occurrence (.node 1 dictionaries) :=
  GeneralDictionarySharingObstruction217.no_evidence (impossible given held) dictionaries

theorem generated_child (atoms) : Generated (stage atoms).core.erased.current root childSite.occurrence :=
  .child .root (edges_exact atoms ▸ List.mem_singleton_self _)

theorem aliases_identity {atoms a b} (related : Alias (stage atoms).core.erased.current a b) : a = b := by
  induction related with
  | refl => rfl
  | edge member => cases member
  | symm _ ih => exact ih.symm
  | trans _ _ one two => exact one.trans two

theorem child_id_above : root.identity < childSite.occurrence.identity :=
  GeneralNominalIdentities.source_above_invocation snapshot.seed (root.identity,0,6,0,0)

theorem generated_from_child_only {atoms focus}
    (generated : Generated (stage atoms).core.erased.current childSite.occurrence focus) : focus = childSite.occurrence := by
  induction generated with
  | root => rfl
  | child prior member ih =>
    rw [edges_exact] at member
    have pair := List.mem_singleton.mp member
    have parent := congrArg Prod.fst pair
    have impossible : root.identity = childSite.occurrence.identity := congrArg Occurrence.identity (parent.symm.trans ih)
    have less := child_id_above
    omega
  | alias prior one two related ih =>
    rw [raw_sites_exact] at one two
    have same := aliases_identity related
    rcases List.mem_cons.mp one with rfl | one
    · have impossible : root.identity = childSite.occurrence.identity := congrArg Occurrence.identity ih
      have less := child_id_above
      omega
    · cases List.mem_singleton.mp one
      rcases List.mem_cons.mp two with rfl | two
      · have less := child_id_above
        change childSite.occurrence.identity = root.identity at same
        omega
      · cases List.mem_singleton.mp two; rfl

theorem merges_closed {atoms first last}
    (one : first ∈ (stage atoms).core.sites) (two : last ∈ (stage atoms).core.sites)
    (same : SameInputs models first last) :
    Alias (stage atoms).core.erased.current first.occurrence.identity last.occurrence.identity := by
  rw [sites_exact] at one two
  simp only [List.mem_cons,List.not_mem_nil,or_false] at one two
  rcases one with rfl | rfl <;> rcases two with rfl | rfl
  · exact .refl _
  · have impossible := same.1; cases impossible
  · have impossible := same.1; cases impossible
  · exact .refl _


theorem role_leaf (visible : d ∈ registry.declarations) (role : d.role = 1) : d = leafDeclaration := by
  rcases List.mem_cons.mp visible with rfl | member
  · cases role
  · exact List.mem_singleton.mp member

theorem no_install {atoms} (candidate : Effect roles)
    (focus : candidate.plan.packet.site.occurrence = childSite.occurrence) :
    ¬ GeneralDictionaryDefaultKernel208.Installable registry (stage atoms) candidate := by
  intro enabled
  obtain ⟨given,valid,held,_⟩ := enabled.common
  have frame : GeneralNominalCenteredHeadOutputs.Frame registry (stage atoms).core
      childSite.occurrence candidate.plan.packet.declaration.id candidate.plan := by
    rw [← focus,← enabled.registry_eq,← enabled.snapshot_eq]
    exact candidate.frame
  have declarationEq := role_leaf frame.visible frame.role_eq
  have key : candidate.plan.packet.declaration.id = 1 := congrArg GeneralDeclarations.Declaration.id declarationEq
  exact impossible given valid candidate.plan (key ▸ frame)
    (GeneralDictionarySharingObstruction217.packet_agreement candidate.plan given held)

theorem generated_from_root_only {atoms focus}
    (generated : Generated (stage atoms).core.erased.current root focus) :
    focus = root ∨ focus = childSite.occurrence := by
  induction generated with
  | root => exact Or.inl rfl
  | child prior member ih =>
    rw [edges_exact] at member
    have pair := List.mem_singleton.mp member
    exact Or.inr (congrArg Prod.snd pair)
  | alias prior one two related ih =>
    rw [raw_sites_exact] at two
    rcases List.mem_cons.mp two with rfl | two
    · exact Or.inl rfl
    · cases List.mem_singleton.mp two; exact Or.inr rfl

end Yulang.GeneralDictionaryGroundCopy218Obstruction
