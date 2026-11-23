import Yulang.GeneralDeclarativeI65Body367
import Yulang.GeneralDeclarativeAppliedClause327
import Yulang.GeneralDeclarativeEmissionOutputs322

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65
open GeneralDeclarativeWitnessCompiler350
  (Context Finished initial execute preparation portNames placed whereBatch fixedBatch
   printDemand print_injective map_injective fixed_targets)
open GeneralDeclarativeAppliedClause327 (prepared_exists compiled_frames)
open GeneralDeclarativeEmissionForest322 (Placement)
open GeneralDeclarativeEmissionOutputs322 (Direct)
open GeneralDeclarativeSourceEmission322 (Names demand useOutput)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralNominalCenteredHeadWFSource (Coverage)
open GeneralDeclarationPatterns (normalize)
open GeneralDeclarations (Declaration Clause Checked)
open GeneralDeclarativeEntailment320 (appendFacts)

/-- Produces the literal body rather than assuming a receipt exists.
This is the existing ordinary compiler's syntactic coverage cut:
it is not a conversion from generalized typed source coverage or
a proof that every arbitrary current state contains those writes. -/
theorem ordinary_fixed_inputs_produce_body (c : Context)
    (checked : Checked c.registry) (covered : Coverage c.registry c.interp)
    (visibleRow : c.decl ∈ c.registry.declarations)
    (sameRole : c.decl.role = c.demand.role)
    (actualDemand : Declared c.registry c.demand) :
    ∃ f : Finished, execute c = some f := by
  obtain ⟨prepared,ports,ran⟩ := prepared_exists (s := (initial c).state)
    covered visibleRow c.targets (initial c).captures c.keep
  obtain ⟨whereRows,rootRows,builtClauses,builtFixed,rest⟩ :=
    compiled_frames checked covered visibleRow sameRole actualDemand
      c.targets (initial c).captures c.keep ran
  have pre : preparation c = some (prepared,ports) := ran
  have clauses : whereBatch c ports = some whereRows := builtClauses
  have fixed : fixedBatch c ports = some rootRows := builtFixed
  exact ⟨⟨appendFacts prepared whereRows,rootRows,GeneralDeclarativeEmissionForest322.children c.decl (portNames c ports) (placed c ports)⟩,
    by simp [execute,pre,clauses,fixed]⟩

theorem exact_source_child_and_output_at {decl : Declaration} {names : Names} {p : Placement}
    {i j : Nat} {cl : Clause} {eqn : GeneralDeclarations.Equation}
    (atClause : decl.requirements[i]? = some cl) (atOutput : cl.outputs[j]? = some eqn) :
    ∃ d, (GeneralDeclarativeEmissionForest322.children decl names p)[i]? = some d ∧
      d.outputs[j]? = some (useOutput decl names (p.targets cl) eqn) := by
  refine ⟨demand decl cl names (p.compound cl) (p.targets cl),?_,?_⟩
  · simp only [GeneralDeclarativeEmissionForest322.children,List.getElem?_map,atClause,Option.map_some]
  · simp only [demand,List.getElem?_map,atOutput,Option.map_some]

theorem non_direct_source_output_uses_local_allocator (decl : Declaration) (names : Names)
    (allocate : Nat → Nat) (eqn : GeneralDeclarations.Equation) (other : ¬Direct decl eqn) :
    (useOutput decl names allocate eqn).target = allocate eqn.id := by
  cases pattern : normalize eqn.rhs with
  | var n =>
    have notOnOutput : n ∉ decl.outputNames := fun h => other ⟨n,pattern,h⟩
    simp [useOutput,GeneralDeclarationDemands.outputTarget,pattern,notOnOutput]
  | app | record | variant | join =>
    simp [useOutput,GeneralDeclarationDemands.outputTarget,pattern]

/-- Pointers cannot be inferred from equal models. Exact output
equality at one actual where row forces the exact target chosen by
the placement for that very written equation. -/
theorem same_literal_children_fix_non_direct_target {decl : Declaration}
    {n₁ n₂ : Names} {p₁ p₂ : Placement}
    {i j : Nat} {cl : Clause} {eqn : GeneralDeclarations.Equation}
    (atClause : decl.requirements[i]? = some cl) (atOutput : cl.outputs[j]? = some eqn)
    (notDirect : ¬Direct decl eqn)
    (same : GeneralDeclarativeEmissionForest322.children decl n₁ p₁ = GeneralDeclarativeEmissionForest322.children decl n₂ p₂) :
    p₁.targets cl eqn.id = p₂.targets cl eqn.id := by
  obtain ⟨d₁,a₁,b₁⟩ := exact_source_child_and_output_at (names := n₁) (p := p₁) atClause atOutput
  obtain ⟨d₂,a₂,b₂⟩ := exact_source_child_and_output_at (names := n₂) (p := p₂) atClause atOutput
  rw [same] at a₁
  have sameKid := Option.some.inj (a₁.symm.trans a₂)
  rw [sameKid] at b₁
  have outputEq := Option.some.inj (b₁.symm.trans b₂)
  calc
    p₁.targets cl eqn.id = (useOutput decl n₁ (p₁.targets cl) eqn).target :=
      (non_direct_source_output_uses_local_allocator decl n₁ (p₁.targets cl) eqn notDirect).symm
    _ = (useOutput decl n₂ (p₂.targets cl) eqn).target :=
      congrArg GeneralSourceState.Output.target outputEq
    _ = p₂.targets cl eqn.id :=
      non_direct_source_output_uses_local_allocator decl n₂ (p₂.targets cl) eqn notDirect

/-- With declaration, demand, and original captures fixed, changing an actual where
target changes the emitted literal child receipt. Both compiler runs
are constructed, not postulated. This does not assert that both
receipt results are already present in some arbitrary fixed state. -/
theorem same_source_distinct_allocators_change_emitted_children (c : Context)
    (checked : Checked c.registry) (covered : Coverage c.registry c.interp)
    (visibleRow : c.decl ∈ c.registry.declarations) (sameRole : c.decl.role = c.demand.role)
    (actualDemand : Declared c.registry c.demand)
    (updated : Clause → Nat → Nat)
    {i j : Nat} {cl : Clause} {eqn : GeneralDeclarations.Equation}
    (atClause : c.decl.requirements[i]? = some cl) (atOutput : cl.outputs[j]? = some eqn)
    (notDirect : ¬Direct c.decl eqn) (changed : c.targets cl eqn.id ≠ updated cl eqn.id) :
    ∃ a b : Finished, execute c = some a ∧ execute { c with targets := updated } = some b ∧ a.kids ≠ b.kids := by
  let alt : Context := { c with targets := updated }
  obtain ⟨a,executed⟩ := ordinary_fixed_inputs_produce_body c checked covered visibleRow sameRole actualDemand
  obtain ⟨b,executedAlt⟩ := ordinary_fixed_inputs_produce_body alt checked covered visibleRow sameRole actualDemand
  obtain ⟨_,portsA,_,kidsA⟩ := ran_body_has_literal_ports c executed
  obtain ⟨_,portsB,_,kidsB⟩ := ran_body_has_literal_ports alt executedAlt
  refine ⟨a,b,executed,executedAlt,?_⟩
  intro same
  have kids : GeneralDeclarativeEmissionForest322.children c.decl (portNames c portsA) (placed c portsA) =
      GeneralDeclarativeEmissionForest322.children c.decl (portNames alt portsB) (placed alt portsB) :=
    kidsA.symm.trans (same.trans kidsB)
  have sameAddr := same_literal_children_fix_non_direct_target atClause atOutput notDirect kids
  exact changed sameAddr

/-- A fixed root target list alone cannot certify its exact selected
body. The two syntactically produced bodies have equal root target
lists but different serialized child demands. -/
theorem fixed_root_targets_do_not_erase_literal_child_allocation (c : Context)
    (checked : Checked c.registry) (covered : Coverage c.registry c.interp)
    (visibleRow : c.decl ∈ c.registry.declarations) (sameRole : c.decl.role = c.demand.role)
    (actualDemand : Declared c.registry c.demand)
    (updated : Clause → Nat → Nat)
    {i j : Nat} {cl : Clause} {eqn : GeneralDeclarations.Equation}
    (atClause : c.decl.requirements[i]? = some cl) (atOutput : cl.outputs[j]? = some eqn)
    (notDirect : ¬Direct c.decl eqn) (changed : c.targets cl eqn.id ≠ updated cl eqn.id) :
    ∃ a b : Finished, execute c = some a ∧ execute {c with targets := updated} = some b ∧
      a.fixed.map GeneralDeclarativeHead320.Equation.left =
        b.fixed.map GeneralDeclarativeHead320.Equation.left ∧
      a.kids.map printDemand ≠ b.kids.map printDemand := by
  obtain ⟨a,b,left,right,distinct⟩ := same_source_distinct_allocators_change_emitted_children
    c checked covered visibleRow sameRole actualDemand updated atClause atOutput notDirect changed
  refine ⟨a,b,left,right,(fixed_targets left).trans (fixed_targets right).symm,?_⟩
  intro prints
  exact distinct (map_injective (fun same => print_injective same) prints)

end Yulang.GeneralDeclarativeI65
