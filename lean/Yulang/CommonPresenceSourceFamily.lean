import Yulang.CommonPresenceClauseFamily

/-!
# Source presence inference with only explicit subtype edges remaining

This finite algorithm consumes every actual closed source formula, normalizes
and packs its binders, constructs shared common equation nodes, and invokes
the simultaneous row/equation solver. Its parameters are arbitrary common
rows and values. Constructor equations and explicit row constraints have
been discharged; the scheme retains a finite list of subtype edges.

The principal theorem is deliberately named `residual_source_principal`:
`ResidualHolds` is a displayed conjunction of those remaining comparisons,
not `Typing`, a generated formula, or a hidden model certificate. Eliminating
these edges for all inputs is the missing full presence solver contract.
The public `Core.infer` is not introduced or redefined here.
-/

namespace Yulang.CommonPresenceSourceFamily

open Core.PresenceGeneration
open PresenceNormalForm (Atom Clause normalise)
open PresenceSourceConstraintSupport (GoodAtoms)
open CommonPresenceConstraintGraph
open CommonPresenceClauseFamily
open Common (Ty Row)
open Inference (Expr)

private theorem comp_trans {a b c : Comp Common.model}
    (first : Comp.le Common.model a b) (last : Comp.le Common.model b c) :
    Comp.le Common.model a c :=
  ⟨Common.subtype_trans first.1 last.1, Common.rowLe_trans first.2 last.2⟩

/-- Result subsumption for the independent common presence judgment. The
proof includes captured value schemes and prescribed signatures and does not
use generation or inference. -/
theorem typing_subsume {environment : List (Binding Common.model)} {expression : Expr}
    {result : Comp Common.model} (typed : Typing Common.model environment expression result) :
    ∀ target, Comp.le Common.model result target → Typing Common.model environment expression target := by
  induction typed using Typing.rec
    (motive_2 := fun binding result _ =>
      ∀ target, Comp.le Common.model result target → BindingTyping Common.model binding target) with
  | var found _ ih => exact fun target below => .var found (ih target below)
  | lit bounded => exact fun _ below => .lit (comp_trans bounded below)
  | lam body bounded _ => exact fun _ below => .lam body (comp_trans bounded below)
  | app function argument bounded _ _ => exact fun _ below => .app function argument (comp_trans bounded below)
  | letValue value definition _ _ body => exact fun target below => .letValue value definition (body target below)
  | letComputed definition body bounded _ _ =>
      exact fun _ below => .letComputed definition body (comp_trans bounded below)
  | branch condition yes no bounded _ _ _ =>
      exact fun _ below => .branch condition yes no (comp_trans bounded below)
  | pair left right bounded _ _ => exact fun _ below => .pair left right (comp_trans bounded below)
  | fst pair bounded _ => exact fun _ below => .fst pair (comp_trans bounded below)
  | snd pair bounded _ => exact fun _ below => .snd pair (comp_trans bounded below)
  | emptyRecord bounded => exact fun _ below => .emptyRecord (comp_trans bounded below)
  | record head tail shape bounded _ _ => exact fun _ below => .record head tail shape (comp_trans bounded below)
  | recordDefault source fallback shape bounded _ _ =>
      exact fun _ below => .recordDefault source fallback shape (comp_trans bounded below)
  | field record bounded _ => exact fun _ below => .field record (comp_trans bounded below)
  | variant payload bounded _ => exact fun _ below => .variant payload (comp_trans bounded below)
  | mono bounded target below => exact .mono (comp_trans bounded below)
  | poly _ row body target below =>
      exact .poly (body (Comp.pure Common.model target.1) ⟨below.1, Common.rowLe_refl _⟩)
        (Common.rowLe_trans row below.2)
  | signature bounded target below => exact .signature (comp_trans bounded below)

/-- Finite residual scheme data. Parameter counts, the common equation
family, output indices and remaining comparisons are all explicit syntax. -/
structure Scheme where
  rowParameters : Nat
  valueParameters : Nat
  equations : CommonRowTailInference.Scheme valueParameters 0 rowParameters
  edges : List (Fin valueParameters × Fin valueParameters)
  outputValue : Fin valueParameters
  outputRow : Fin rowParameters

def Scheme.instantiate (scheme : Scheme) (rows : Fin scheme.rowParameters → Row)
    (values : Fin scheme.valueParameters → Ty) : Comp Common.model :=
  ((scheme.equations.instantiateValues rows values) scheme.outputValue,
    (scheme.equations.instantiateRows rows) scheme.outputRow)

def Scheme.ResidualHolds (scheme : Scheme) (rows : Fin scheme.rowParameters → Row)
    (values : Fin scheme.valueParameters → Ty) : Prop :=
  EdgesHold scheme.edges (scheme.equations.instantiateValues rows values)

def ofClause (clause : Clause (Option Empty)) (good : GoodAtoms clause.pack) : Scheme where
  rowParameters := clause.locals + 1
  valueParameters := (compile clause.pack).size
  equations := family clause.pack good
  edges := (compile clause.pack).edges
  outputValue := (compile clause.pack).input (Fin.last clause.locals)
  outputRow := Fin.last clause.locals

/-- A finite source algorithm, with the original value-let alternatives and
captured slot identities. Row support is proved from each generated clause;
no caller-supplied checker or success premise is used. -/
def inferSource (expression : Expr) : List Scheme :=
  (normalise (principal ([] : SchemeEnv Empty) expression)).attach.map fun clause =>
    ofClause clause.val (PresenceSourceConstraintSupport.generated_row_shapes expression clause.val clause.property)

/-- Every original satisfying packed assignment is recovered by the actual
family. This eliminates all existential definition nodes while retaining the
independent remaining edge comparisons. -/
theorem clause_parameter_retraction (clause : Clause (Option Empty)) (good : GoodAtoms clause.pack)
    (assignment : Fin (clause.locals + 1) → Comp Common.model)
    (accepted : PresenceNormalForm.All Common.model assignment clause.pack) :
    ∃ rows : Fin (ofClause clause good).rowParameters → Row,
    ∃ values : Fin (ofClause clause good).valueParameters → Ty,
      (ofClause clause good).ResidualHolds rows values ∧
      Comp.le Common.model ((ofClause clause good).instantiate rows values)
        (assignment (Fin.last clause.locals)) := by
  obtain ⟨nodes, models, readback⟩ := (compile_atoms_exact clause.pack assignment).mp accepted
  have same := family_retracts clause.pack good (fun index => (assignment index).2) nodes models
  refine ⟨(fun index => (assignment index).2), nodes,
    (edgesHold_congr _ _ _ same.2).mpr models.2.1, ?_⟩
  constructor
  · have output := (same.2 ((compile clause.pack).input (Fin.last clause.locals))).1
    have equal := congrArg Prod.fst (congrFun readback (Fin.last clause.locals))
    change Common.Subtype _ (assignment (Fin.last clause.locals)).1
    rw [← equal]
    exact output
  · change Common.rowLe (((family clause.pack good).instantiateRows
      (fun index => (assignment index).2)) (Fin.last clause.locals)) _
    rw [same.1]
    exact Common.rowLe_refl _

theorem clause_instantiation_models (clause : Clause (Option Empty)) (good : GoodAtoms clause.pack)
    (rows : Fin (ofClause clause good).rowParameters → Row)
    (values : Fin (ofClause clause good).valueParameters → Ty)
    (residual : (ofClause clause good).ResidualHolds rows values) :
    (compile clause.pack).Models ((family clause.pack good).instantiateRows rows)
      ((family clause.pack good).instantiateValues rows values) := by
  have definitions := family_instantiates clause.pack good rows values
  exact ⟨definitions.2, residual, definitions.1⟩

/-- All closed source expressions, all result computations, and no support,
success or fuel premise. Only the explicitly displayed residual subtype edges
remain between this statement and the requested unconstrained principal family. -/
theorem residual_source_principal (expression : Expr) (result : Comp Common.model) :
    Typing Common.model [] expression result ↔
      ∃ scheme ∈ inferSource expression,
      ∃ rows : Fin scheme.rowParameters → Row,
      ∃ values : Fin scheme.valueParameters → Ty,
        scheme.ResidualHolds rows values ∧ Comp.le Common.model (scheme.instantiate rows values) result := by
  constructor
  · intro typed
    obtain ⟨clause, member, assignment, output, accepted⟩ :=
      (PresenceNormalForm.closed_source_exact Common.model expression result).mp typed
    let good := PresenceSourceConstraintSupport.generated_row_shapes expression clause member
    obtain ⟨rows, values, residual, bounded⟩ := clause_parameter_retraction clause good assignment accepted
    refine ⟨ofClause clause good, List.mem_map.mpr ⟨⟨clause, member⟩, by simp, rfl⟩,
      rows, values, residual, ?_⟩
    simpa only [output] using bounded
  · rintro ⟨scheme, member, rows, values, residual, bounded⟩
    obtain ⟨clause, _, rfl⟩ := List.mem_map.mp member
    let good := PresenceSourceConstraintSupport.generated_row_shapes expression clause.val clause.property
    have models := clause_instantiation_models clause.val good rows values residual
    have accepted := compile_atoms_reflects clause.val.pack _ _ models
    have typed : Typing Common.model [] expression ((ofClause clause.val good).instantiate rows values) := by
      apply (PresenceNormalForm.closed_source_exact Common.model expression _).mpr
      exact ⟨clause.val, clause.property, _, rfl, accepted⟩
    exact typing_subsume typed result bounded

/-- The Core generator's syntax check cannot introduce bad row shapes:
outside the fragment it generates false, and inside it uses the actual source
generator. This is a theorem of all Core terms, not a caller precondition. -/
theorem generated_core_row_shapes (expression : Core.Required.Term)
    (clause : Clause (Option Empty))
    (member : clause ∈ normalise (CoreRules.principalCore ([] : SchemeEnv Empty) expression)) :
    GoodAtoms clause.pack := by
  cases supported : Core.InferenceSyntax.supported expression with
  | false =>
      simp only [CoreRules.principalCore, CoreRules.generateCore, supported,
        Bool.false_eq_true, ↓reduceIte, normalise, List.not_mem_nil] at member
  | true =>
      apply PresenceSourceConstraintSupport.generated_row_shapes (CoreRules.decode expression) clause
      simpa only [CoreRules.principalCore, CoreRules.generateCore, supported, ↓reduceIte, principal]
        using member

def inferCore (expression : Core.Required.Term) : List Scheme :=
  (normalise (CoreRules.principalCore ([] : SchemeEnv Empty) expression)).attach.map fun clause =>
    ofClause clause.val (generated_core_row_shapes expression clause.val clause.property)

theorem core_typing_subsume (expression : Core.Required.Term) (result target : Comp Common.model)
    (typed : Core.Typing (CoreRules.model Common.model) [] expression result)
    (below : Comp.le Common.model result target) :
    Core.Typing (CoreRules.model Common.model) [] expression target := by
  have supported := CoreRules.typing_syntax typed
  have source : Typing Common.model [] (CoreRules.decode expression) result := CoreRules.reflected typed
  have changed := CoreRules.preserved (typing_subsume source target below)
  change CoreRules.Typing Common.model [] expression target
  simpa only [List.map_nil, CoreRules.embed, CoreRules.decode,
    Core.InferenceSyntax.embed_decode expression supported] using changed

/-- Actual normalization, binder packing, graph construction and simultaneous
equation solving are connected for every closed Core term and every result.
The displayed residual edges, and only those edges, still await full subtype
inspection/saturation before a public unconstrained `Core.infer` theorem. -/
theorem residual_core_principal (expression : Core.Required.Term) (result : Comp Common.model) :
    Core.Typing (CoreRules.model Common.model) [] expression result ↔
      ∃ scheme ∈ inferCore expression,
      ∃ rows : Fin scheme.rowParameters → Row,
      ∃ values : Fin scheme.valueParameters → Ty,
        scheme.ResidualHolds rows values ∧ Comp.le Common.model (scheme.instantiate rows values) result := by
  constructor
  · intro typed
    obtain ⟨clause, member, assignment, output, accepted⟩ :=
      (PresenceNormalForm.closed_core_exact Common.model expression result).mp typed
    let good := generated_core_row_shapes expression clause member
    obtain ⟨rows, values, residual, bounded⟩ := clause_parameter_retraction clause good assignment accepted
    refine ⟨ofClause clause good, List.mem_map.mpr ⟨⟨clause, member⟩, by simp, rfl⟩,
      rows, values, residual, ?_⟩
    simpa only [output] using bounded
  · rintro ⟨scheme, member, rows, values, residual, bounded⟩
    obtain ⟨clause, _, rfl⟩ := List.mem_map.mp member
    let good := generated_core_row_shapes expression clause.val clause.property
    have models := clause_instantiation_models clause.val good rows values residual
    have accepted := compile_atoms_reflects clause.val.pack _ _ models
    have typed : Core.Typing (CoreRules.model Common.model) [] expression
        ((ofClause clause.val good).instantiate rows values) := by
      apply (PresenceNormalForm.closed_core_exact Common.model expression _).mpr
      exact ⟨clause.val, clause.property, _, rfl, accepted⟩
    exact core_typing_subsume expression _ result typed bounded

end Yulang.CommonPresenceSourceFamily
