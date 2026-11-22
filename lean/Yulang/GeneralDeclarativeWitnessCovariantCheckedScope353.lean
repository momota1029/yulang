import Yulang.GeneralDeclarativeWitnessCovariantCompiler353
import Yulang.GeneralDeclarativeWitnessCovariantWrittenFixture353

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessCovariantCheckedScope353
open GeneralDeclarativeWitnessCovariantOrigin353 (Problem Wire)
open GeneralDeclarativeWitnessCovariantCompiler353 (Prepared declarations)
open GeneralDeclarativeWitnessProblem349 (splitAnd declared_iff)
open GeneralDeclarativeWitnessCovariantDescent353 (legal descent_sound)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralSourceMetadataBundle291 (registry)
open GeneralSourceMetadataBareBundle291 (forget preserves_input)
open GeneralSourceMetadataRoles291 (Valid)
open GeneralDeclarationPatterns (Smaller StableSmaller)

theorem checked_fields {p : Problem} {w : Wire} (a : Prepared p w) :
    forget a.anchor.metadataProof.source = p.metadata.sourceInput ∧
    Valid a.anchor.metadataProof.source.roles ∧
    a.decl ∈ (registry a.anchor.metadataProof.source).declarations ∧
    a.decl.role = p.demand.role ∧
    (∀ d ∈ (registry a.anchor.metadataProof.source).declarations, d.role = p.demand.role → d = a.decl) ∧
    Declared (registry a.anchor.metadataProof.source) p.demand ∧
    (∀ child ∈ a.decl.requirements, Smaller a.decl.head child.arguments ∧ StableSmaller a.decl.head child.arguments) := by
  obtain ⟨source,roles⟩ := preserves_input _ _ a.anchor.metadataProof.assembled
  have member : a.decl ∈ declarations a.anchor := a.only.symm ▸ List.mem_cons_self
  obtain ⟨occurs,correct⟩ := List.mem_filter.mp member
  have reqs := (splitAnd (splitAnd (splitAnd a.good).2).2).2
  refine ⟨source,roles,occurs,beq_iff_eq.mp correct,?_,(declared_iff ..).mp a.declaredRoot,?_⟩
  · intro d ins role
    have needed : d ∈ declarations a.anchor := List.mem_filter.mpr ⟨ins,beq_iff_eq.mpr role⟩
    exact List.mem_singleton.mp (a.only ▸ needed)
  · intro child included
    exact descent_sound (List.all_eq_true.mp reqs child included)

open GeneralDeclarativeWitnessCovariantFixture353 (problem wire test)
open GeneralSourceMetadataRows291 (Source)

theorem boundary_on_same_source :
    (GeneralSourceMetadataBareBundle291.compile problem.metadata.sourceInput |>.map
      GeneralDeclarativeWitnessProblem349.covered) = some false := by decide +kernel

def incompatibleSnapshot : Source := ⟨.absent,[⟨0,some ⟨[.type],1⟩,.unclassified⟩]⟩

theorem stale_declaration_identity :
    test {problem with metadata := {problem.metadata with sourceInput :=
      {problem.metadata.sourceInput with snapshot := incompatibleSnapshot}}} wire = false := by decide +kernel

theorem duplicate_root_is_not_an_origin :
    test {problem with rows := problem.rows ++ problem.rows.take 1} wire = false := by decide +kernel

theorem missing_independent_payload_row :
    test {problem with stage := {problem.stage with equations := problem.stage.equations.take 2}} wire = false := by
  decide +kernel

end Yulang.GeneralDeclarativeWitnessCovariantCheckedScope353
