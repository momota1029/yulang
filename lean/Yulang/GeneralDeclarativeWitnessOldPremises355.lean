import Yulang.GeneralDeclarativeWitnessSpineFront355
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessOldPremises355
open GeneralDeclarativeWitnessTypedRangeWriter354 (Run)
open GeneralDeclarativeWitnessSpineNode355 (Node Step)
open GeneralDeclarativeWitnessCoverageBoundary355 (visible_selected_decl)
open GeneralDeclarativeWitnessRetainedCut355 (from_the_checked_head)
open GeneralDeclarativeWitnessNominalSpine355 (Checked)
open GeneralDeclarativeWitnessProblem349 (declared_iff)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeHead320 (State)
open GeneralDeclarations (Clause DeclarationChecked Registry)
open GeneralDeclarationPatterns (CountsCovered)
open GeneralSourceMetadataBundle291 (registry)

theorem real_requests_are_declared {p w} (r : Run p w) :
    Declared r.readFrom.ctx.registry p.demand := by
  have requests := (declared_iff _ _).mp r.readFrom.center.declaredRoot
  intro demand present
  exact requests demand present

/-- With a real emitted child, the retained joined syntax also fails the
old CountsCovered premise of DeclarationChecked; that is separate from
ordinary Coverage failing for the nominal constructor. -/
theorem old_selected_declaration_not_checked {p w} (r : Run p w)
    (nonleaf : r.children ≠ []) :
    ¬ DeclarationChecked r.readFrom.ctx.registry.constructors r.readFrom.ctx.registry.roles r.readFrom.center.decl := by
  intro old
  cases requirements : r.readFrom.center.decl.requirements with
  | nil =>
    apply nonleaf
    unfold Run.children GeneralDeclarativeEmissionForest322.children
    change r.readFrom.center.decl.requirements.map _ = []
    rw [requirements]
    rfl
  | cons c rest =>
    have inside : c ∈ r.readFrom.center.decl.requirements := by rw [requirements]; exact List.mem_cons_self
    have shape := (old.countsCovered c inside).1
    rw [from_the_checked_head r] at shape
    cases shape

theorem old_registry_not_checked_at_real_edge {s : State} {p : Node s} {a w} (edge : Step p a w) :
    ¬ GeneralDeclarations.Checked p.proof.compiled.readFrom.ctx.registry := by
  intro old
  have visible := visible_selected_decl p.proof.compiled.readFrom.center
  have impossible := old_selected_declaration_not_checked p.proof.compiled (by rw [edge.only]; simp)
  exact impossible (old.2 _ visible)

theorem requests_along_spine {s : State} {p : Node s} (read : Checked p) :
    ∀ n ∈ read.nodes,Declared n.proof.compiled.readFrom.ctx.registry n.input.demand :=
  fun n _ => real_requests_are_declared n.proof.compiled

end Yulang.GeneralDeclarativeWitnessOldPremises355
