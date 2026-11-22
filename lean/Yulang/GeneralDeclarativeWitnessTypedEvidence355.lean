import Yulang.GeneralDeclarativeWitnessCoverageBoundary355
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessTypedEvidence355
open GeneralDeclarativeWitnessSpineNode355 (Node)
open GeneralDeclarativeWitnessNominalSpine355 (Checked NodeMeaning)
open GeneralDeclarativeWitnessNominalSpineWhole355 (Found)
open GeneralDeclarativeWitnessCovariantOrigin353 (Valuation)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWitnessCompiler350 (portNames)
open GeneralDeclarativeWitnessTypedReemit354 (Linked)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (Dictionary All₂)
open CommonNominalFullCarrier (Equivalent)

structure Local {s : State} (m : Assignment) (v : Valuation) (p : Node s) : Prop where
  readback : NodeMeaning m v p
  whole :
    ∀ name ∈ p.proof.compiled.readFrom.center.decl.inputNames,
      Equivalent (m ((portNames p.proof.compiled.readFrom.ctx p.proof.compiled.ports).input name).center).1
        (.union (m p.proof.compiled.readFrom.center.anchor.first.valueName).1
                (m p.proof.compiled.readFrom.center.anchor.last.valueName).1)

theorem all_input_binders_in_same_model {s : State} (p : Node s) (m : Assignment) (fit : Models s m)
    (v : Valuation) (readback : NodeMeaning m v p) : Local m v p := by
  refine ⟨readback,?_⟩
  intro n used
  have ok := p.proof.compiled.readFrom.center.good
  have lexical := (GeneralDeclarativeWitnessProblem349.splitAnd
    (GeneralDeclarativeWitnessProblem349.splitAnd ok).2).1
  have only := GeneralDeclarativeWitnessChecks349.output_only
    (GeneralDeclarativeWitnessProblem349.splitAnd lexical).2
  have input := GeneralPatternVariableProvenance.normalize_args_variables _ used
  have notOut : n ∉ p.proof.compiled.readFrom.center.decl.outputNames := fun h => only.1 n h input
  rw [GeneralDeclarativeWitnessRangeCut355.selected_center p.proof.compiled used notOut]
  exact GeneralDeclarativeWitnessCovariantOrigin353.whole_full p.proof.compiled.readFrom.center.anchor m
    (GeneralDeclarativeGrowth327.restrict
      ((GeneralDeclarativeWitnessLiteral349.preserves_iff ..).mp p.proof.kept) m fit)

/-- Ordered semantic evidence in the witnessed covariant carrier.
The declarative ordinary classifier and its coverage are unchanged. -/
inductive Evidence (s : State) (m : Assignment) (v : Valuation) : Demand → Dictionary → Prop where
  | node (p : Node s) (actual : Local m v p)
      (children : All₂ (Evidence s m v) p.proof.compiled.children entries) :
      Evidence s m v p.input.demand (.node p.name entries)

theorem compose {s : State} {p : Node s} (a : Checked p) (m : Assignment) (fit : Models s m)
    (v : Valuation) (known : ∀ n ∈ a.nodes,NodeMeaning m v n) :
    Evidence s m v p.input.demand a.dictionary := by
  induction a with
  | @leaf p empty =>
    refine .node p (all_input_binders_in_same_model p m fit v (known p List.mem_cons_self)) ?_
    rw [empty]
    exact .nil
  | @send p origin code edge tail ih =>
    refine .node p (all_input_binders_in_same_model p m fit v (known p List.mem_cons_self)) ?_
    rw [edge.only]
    have last := ih (fun n seen => known n (List.mem_cons_of_mem _ seen))
    exact .cons last .nil

theorem checked_tree_has_typed_evidence {i s w} {a : Linked i s w} {plan report}
    (seen : Found a plan report) (m : Assignment) (fit : Models s m) :
    ∃ v : Valuation,
      Evidence s m v a.child seen.node.dictionary ∧
      report.result = .selected (GeneralDeclarativeWitnessNominalSpineWhole355.selectedDictionary a seen.node) := by
  have sound := GeneralDeclarativeWitnessNominalSpineWhole355.sound seen m fit
  obtain ⟨v,rest⟩ := sound.2.2.2.2.2
  exact ⟨v,compose seen.node m fit v rest,sound.2.1⟩

end Yulang.GeneralDeclarativeWitnessTypedEvidence355
