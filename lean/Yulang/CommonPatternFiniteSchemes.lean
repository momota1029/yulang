import Yulang.CommonPatternSolvedExact
import Yulang.CommonPatternGenerationProvenance

/-! A finite solved boundary retaining every free computation slot. Packing
keeps arbitrary finite ambient environments, not only one closed result slot.
The syntax certificate is a formula invariant, never a parameter predicate. -/

namespace Yulang.CommonPatternFiniteSchemes

set_option backward.isDefEq.respectTransparency false

open Core.PresenceGeneration
open PresenceNormalForm (Atom Clause normalise All)
open CommonPresenceConstraintGraph (compile)
open CommonPatternGenerationProvenance (SafeFormula)
open Common (Row Ty Equivalent)

def packedName (locals free : Nat) : Fin locals ⊕ Fin free → Fin (locals + free)
  | .inl index => index.castAdd free
  | .inr index => index.natAdd locals

def pack (clause : Clause (Fin n)) : List (Atom (Fin (clause.locals + n))) :=
  clause.atoms.map (Atom.rename (packedName clause.locals n))

theorem pack_assignment (model : Model) (clause : Clause (Fin n))
    (localValues : Fin clause.locals → Comp model) (freeValues : Fin n → Comp model) :
    All model (Fin.addCases localValues freeValues) (pack clause) ↔ clause.Holds model freeValues localValues := by
  rw [pack, PresenceNormalForm.all_rename]
  have same : Fin.addCases localValues freeValues ∘ packedName clause.locals n = Sum.elim localValues freeValues := by
    funext name
    cases name <;> simp [packedName]
  rw [same]
  rfl

theorem pack_restrict (model : Model) (clause : Clause (Fin n))
    (values : Fin (clause.locals + n) → Comp model) :
    All model values (pack clause) ↔
      clause.Holds model (fun index => values (index.natAdd clause.locals))
        (fun index => values (index.castAdd n)) := by
  rw [pack, PresenceNormalForm.all_rename]
  have same : values ∘ packedName clause.locals n =
      Sum.elim (fun index => values (index.castAdd n)) (fun index => values (index.natAdd clause.locals)) := by
    funext name
    cases name <;> rfl
  rw [same]
  rfl

theorem packed_invariants {formula : Formula (Fin n)} (good : SafeFormula formula)
    (clause : Clause (Fin n)) (generated : clause ∈ normalise formula) :
    CommonPatternConstraintGrammar.GoodAtoms (pack clause) ∧
      PresenceSourceConstraintSupport.GoodAtoms (pack clause) ∧
      PresenceGeneratedWidth.WidthAtoms (pack clause) :=
  ⟨CommonPatternFormulaGrammar.GoodAtoms.rename
      (CommonPatternFormulaGrammar.good_normalise good.endpoints clause generated) _,
    (PresenceSourceConstraintSupport.good_normalise good.rows clause generated).rename _,
    (PresenceGeneratedWidth.guarded_normalise good.widths clause generated).rename _⟩

structure Scheme (free : Nat) where
  slots : Nat
  nodes : Nat
  solution : CommonBoundRefSolver.Scheme slots nodes
  freeValue : Fin free → Fin nodes
  freeRow : Fin free → Fin slots

abbrev Scheme.Parameters (scheme : Scheme n) := (Fin scheme.slots → Row) × scheme.solution.Parameters

def Scheme.instantiate (scheme : Scheme n) (parameters : scheme.Parameters) : Fin n → Comp Common.model :=
  fun index => (scheme.solution.instantiateValues parameters.1 parameters.2 (scheme.freeValue index),
    scheme.solution.instantiateRows parameters.1 (scheme.freeRow index))

theorem Scheme.parameters_nonempty (scheme : Scheme n) : Nonempty scheme.Parameters :=
  ⟨(fun _ => Common.rowEmpty), (fun _ => .bottom), (fun _ => .bottom)⟩

def ofClause (clause : Clause (Fin n))
    (solution : CommonBoundRefSolver.Scheme (clause.locals + n) (compile (pack clause)).size) : Scheme n where
  slots := clause.locals + n
  nodes := (compile (pack clause)).size
  solution := solution
  freeValue index := (compile (pack clause)).input (index.natAdd clause.locals)
  freeRow index := index.natAdd clause.locals

def solveClause (clause : Clause (Fin n)) : List (Scheme n) :=
  (CommonPatternSolvedConstraints.solveAll (compile (pack clause))).map (ofClause clause)

def infer (formula : Formula (Fin n)) : List (Scheme n) := (normalise formula).flatMap solveClause

/-- Every arbitrary parameter of every returned finite scheme satisfies the
actual formula, simultaneously at all free slots. No syntax certificate,
original model, residual condition, support or fuel is required here. -/
theorem all_parameter_holds (formula : Formula (Fin n)) (scheme : Scheme n)
    (returned : scheme ∈ infer formula) (parameters : scheme.Parameters) :
    formula.Holds Common.model (scheme.instantiate parameters) := by
  obtain ⟨clause, generated, member⟩ := List.mem_flatMap.mp returned
  obtain ⟨solution, solved, rfl⟩ := List.mem_map.mp member
  have models := CommonPatternSolvedConstraints.all_parameter_sound (pack clause) solution solved parameters.1 parameters.2
  have atoms := CommonPresenceConstraintGraph.compile_atoms_reflects (pack clause) _ _ models
  have held := (pack_restrict Common.model clause _).mp atoms
  apply (PresenceNormalForm.normalise_exact Common.model _ formula).mp
  exact ⟨clause, generated, _, held⟩

/-- All original free rows are recovered literally and all free values up to
Common demand equivalence. Every finite source slot remains shared. -/
theorem parameter_retraction (formula : Formula (Fin n)) (good : SafeFormula formula)
    (assignment : Fin n → Comp Common.model) (accepted : formula.Holds Common.model assignment) :
    ∃ scheme ∈ infer formula, ∃ parameters : scheme.Parameters,
      ∀ index, Equivalent (scheme.instantiate parameters index).1 (assignment index).1 ∧
        (scheme.instantiate parameters index).2 = (assignment index).2 := by
  obtain ⟨clause, generated, localValues, held⟩ :=
    (PresenceNormalForm.normalise_exact Common.model assignment formula).mpr accepted
  let packedValues : Fin (clause.locals + n) → Comp Common.model := Fin.addCases localValues assignment
  have packed := (pack_assignment Common.model clause localValues assignment).mpr held
  obtain ⟨nodes, models, readback⟩ := (CommonPresenceConstraintGraph.compile_atoms_exact (pack clause) packedValues).mp packed
  obtain ⟨endpoints, rows, widths⟩ := packed_invariants good clause generated
  obtain ⟨solution, solved, rowParameters, parameters, sameRows, sameValues⟩ :=
    (CommonPatternSolvedConstraints.compiled_models_exact (pack clause) rows endpoints widths _ _).mp models
  refine ⟨ofClause clause solution,
    List.mem_flatMap.mpr ⟨clause, generated, List.mem_map.mpr ⟨solution, solved, rfl⟩⟩,
    ⟨rowParameters, parameters⟩, ?_⟩
  intro index
  have valueSame := sameValues ((compile (pack clause)).input (index.natAdd clause.locals))
  have output := congrArg Prod.fst (congrFun readback (index.natAdd clause.locals))
  have rowSame := congrFun sameRows (index.natAdd clause.locals)
  constructor
  · change Equivalent _ (assignment index).1
    have outputSame : nodes ((compile (pack clause)).input (index.natAdd clause.locals)) = (assignment index).1 := by
      simpa only [CommonPresenceConstraintGraph.Compiled.readback, packedValues, Fin.addCases_right] using output
    rw [← outputSame]
    exact valueSame
  · simpa only [Scheme.instantiate, ofClause, packedValues, Fin.addCases_right] using rowSame

theorem infer_empty_iff (formula : Formula (Fin n)) (good : SafeFormula formula) :
    infer formula = [] ↔ ¬ ∃ assignment, formula.Holds Common.model assignment := by
  constructor
  · intro empty ⟨assignment, held⟩
    obtain ⟨scheme, returned, _⟩ := parameter_retraction formula good assignment held
    simp [empty] at returned
  · intro impossible
    cases found : infer formula with
    | nil => rfl
    | cons scheme rest =>
        have returned : scheme ∈ infer formula := by rw [found]; exact List.mem_cons_self
        obtain ⟨parameters⟩ := scheme.parameters_nonempty
        exact False.elim (impossible ⟨_, all_parameter_holds formula scheme returned parameters⟩)

end Yulang.CommonPatternFiniteSchemes
