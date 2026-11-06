import Yulang.ConstraintProblems
import Yulang.TypeConstraintRowInstantiation

/-!
# Syntactic support of record-construction-free source inference

The supported source core excludes only record construction. It retains
lambda, application, both let branches, conditionals, pairs, projections,
field access, variants, and the empty record. A support certificate concerns
the representation of constraints, not whether their constructor checks pass.

The invariant permits outer unions on the left of type inequalities, keeps
record spines fixed, and keeps each arrow row and explicit row upper bound
a variable or empty row. It is stable under the actual generator's scheme
substitution, captured-name renaming, and existential clause packing.
-/

namespace Yulang.SourceConstraintSupport

open Inference ConstraintNormalForm

def RecordFree : Expr → Prop
  | .var _ | .lit _ | .emptyRecord => True
  | .lam body | .fst body | .snd body | .field _ body | .variant _ body => RecordFree body
  | .app left right | .letE left right | .pair left right => RecordFree left ∧ RecordFree right
  | .branch condition yes no => RecordFree condition ∧ RecordFree yes ∧ RecordFree no
  | .record _ _ _ => False

def simpleRow : RowTerm α → Bool
  | .var _ | .empty => true
  | .join _ _ => false

def simpleTy : TyTerm α → Bool
  | .var _ | .base _ | .bottom | .top | .emptyRecord => true
  | .union _ _ | .inter _ _ => false
  | .pair left right => simpleTy left && simpleTy right
  | .record _ value rest => ValueBoundElimination.recordSpine rest && simpleTy value && simpleTy rest
  | .variant _ payload => simpleTy payload
  | .arrow input inputRow output outputRow =>
      simpleTy input && simpleRow inputRow && simpleTy output && simpleRow outputRow

def lowerTy : TyTerm α → Bool
  | .union left right => lowerTy left && lowerTy right
  | term => simpleTy term

def GoodComp (term : CompTerm α) : Prop := simpleTy term.ty = true ∧ simpleRow term.row = true

def GoodFormula : Formula α → Prop
  | .top | .bot => True
  | .and left right | .or left right => GoodFormula left ∧ GoodFormula right
  | .tyLe left right => lowerTy left = true ∧ simpleTy right = true
  | .rowLe _ right => simpleRow right = true
  | .existsSlot formula => GoodFormula formula

def GoodEnv (schemes : SchemeEnv α) : Prop := ∀ scheme ∈ schemes, GoodFormula scheme

theorem simple_implies_lower {term : TyTerm α} (good : simpleTy term = true) : lowerTy term = true := by
  cases term with
  | union => cases good
  | _ => exact good

@[simp] theorem simpleRow_rename (rename : α → β) (term : RowTerm α) :
    simpleRow (term.rename rename) = simpleRow term := by cases term <;> rfl

@[simp] theorem recordSpine_rename (rename : α → β) (term : TyTerm α) :
    ValueBoundElimination.recordSpine (term.rename rename) = ValueBoundElimination.recordSpine term := by
  induction term <;> simp_all [TyTerm.rename, ValueBoundElimination.recordSpine]

@[simp] theorem simpleTy_rename (rename : α → β) (term : TyTerm α) :
    simpleTy (term.rename rename) = simpleTy term := by
  induction term <;> simp_all [TyTerm.rename, simpleTy]

@[simp] theorem lowerTy_rename (rename : α → β) (term : TyTerm α) :
    lowerTy (term.rename rename) = lowerTy term := by
  induction term <;> simp_all [TyTerm.rename, lowerTy, simpleTy]

theorem GoodComp.rename {term : CompTerm α} (good : GoodComp term) (rename : α → β) :
    GoodComp (term.rename rename) := by simpa [GoodComp, CompTerm.rename] using good

theorem good_var (index : α) : GoodComp (CompTerm.var index) := ⟨rfl, rfl⟩

theorem simpleRow_subst (subst : α → CompTerm β) (assignment : ∀ index, GoodComp (subst index))
    (term : RowTerm α) (good : simpleRow term = true) : simpleRow (term.subst subst) = true := by
  cases term with
  | var index => exact (assignment index).2
  | empty => rfl
  | join => cases good

theorem recordSpine_subst (subst : α → CompTerm β) (term : TyTerm α)
    (shape : ValueBoundElimination.recordSpine term = true) :
    ValueBoundElimination.recordSpine (term.subst subst) = true := by
  induction term with
  | emptyRecord => rfl
  | record _ _ rest _ ih => exact ih shape
  | _ => cases shape

theorem simpleTy_subst (subst : α → CompTerm β) (assignment : ∀ index, GoodComp (subst index))
    (term : TyTerm α) (good : simpleTy term = true) : simpleTy (term.subst subst) = true := by
  induction term with
  | var index => exact (assignment index).1
  | base | bottom | top | emptyRecord => rfl
  | union | inter => cases good
  | pair left right ihl ihr =>
      have checks := Bool.and_eq_true_iff.mp good
      exact Bool.and_eq_true_iff.mpr ⟨ihl checks.1, ihr checks.2⟩
  | variant label payload ih => exact ih good
  | record label head rest ihh ihr =>
      have checks : (ValueBoundElimination.recordSpine rest = true ∧ simpleTy head = true) ∧
          simpleTy rest = true := by simpa only [simpleTy, Bool.and_eq_true] using good
      simp only [TyTerm.subst, simpleTy, Bool.and_eq_true]
      exact ⟨⟨recordSpine_subst subst rest checks.1.1, ihh checks.1.2⟩, ihr checks.2⟩
  | arrow input inputRow output outputRow ihi iho =>
      have checks : ((simpleTy input = true ∧ simpleRow inputRow = true) ∧ simpleTy output = true) ∧
          simpleRow outputRow = true := by simpa only [simpleTy, Bool.and_eq_true] using good
      simp only [TyTerm.subst, simpleTy, Bool.and_eq_true]
      exact ⟨⟨⟨ihi checks.1.1.1, simpleRow_subst subst assignment inputRow checks.1.1.2⟩,
        iho checks.1.2⟩, simpleRow_subst subst assignment outputRow checks.2⟩

theorem lowerTy_subst (subst : α → CompTerm β) (assignment : ∀ index, GoodComp (subst index))
    (term : TyTerm α) (good : lowerTy term = true) : lowerTy (term.subst subst) = true := by
  induction term with
  | union left right ihl ihr =>
      have checks := Bool.and_eq_true_iff.mp good
      exact Bool.and_eq_true_iff.mpr ⟨ihl checks.1, ihr checks.2⟩
  | _ => exact simple_implies_lower (simpleTy_subst subst assignment _ good)

theorem GoodFormula.rename {formula : Formula α} (good : GoodFormula formula) (rename : α → β) :
    GoodFormula (formula.rename rename) := by
  induction formula generalizing β with
  | top | bot => trivial
  | and _ _ ihl ihr | or _ _ ihl ihr => exact ⟨ihl good.1 rename, ihr good.2 rename⟩
  | tyLe left right => simpa [GoodFormula, Formula.rename] using good
  | rowLe left right => simpa [GoodFormula, Formula.rename] using good
  | existsSlot formula ih => exact ih good (Option.map rename)

theorem GoodFormula.subst {formula : Formula α} (good : GoodFormula formula) (subst : α → CompTerm β)
    (assignment : ∀ index, GoodComp (subst index)) : GoodFormula (formula.subst subst) := by
  induction formula generalizing β with
  | top | bot => trivial
  | and _ _ ihl ihr | or _ _ ihl ihr =>
      exact ⟨ihl good.1 subst assignment, ihr good.2 subst assignment⟩
  | tyLe left right => exact ⟨lowerTy_subst subst assignment left good.1, simpleTy_subst subst assignment right good.2⟩
  | rowLe left right => exact simpleRow_subst subst assignment right good
  | existsSlot formula ih =>
      apply ih good (liftSubst subst)
      intro index
      cases index with
      | none => exact good_var _
      | some index => exact (assignment index).rename some

theorem GoodEnv.rename {schemes : SchemeEnv α} (good : GoodEnv schemes) (rename : α → β) :
    GoodEnv (schemes.rename rename) := by
  intro scheme member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  exact (good original present).rename (Option.map rename)

theorem GoodEnv.lift {schemes : SchemeEnv α} (good : GoodEnv schemes) : GoodEnv schemes.lift :=
  good.rename some

theorem GoodEnv.cons {schemes : SchemeEnv α} (good : GoodEnv schemes) {scheme : Scheme α}
    (head : GoodFormula scheme) : GoodEnv (scheme :: schemes) := by
  intro actual member
  rcases List.mem_cons.mp member with rfl | member
  · exact head
  · exact good actual member

theorem good_compLe {source target : CompTerm α}
    (left : lowerTy source.ty = true) (right : GoodComp target) : GoodFormula (Formula.compLe source target) :=
  ⟨⟨left, right.1⟩, right.2⟩

theorem good_mono {term : CompTerm α} (good : GoodComp term) : GoodFormula (Scheme.mono term) :=
  good_compLe (simple_implies_lower (good.rename some).1) (good_var none)

theorem GoodFormula.instantiate {scheme : Scheme α} (good : GoodFormula scheme)
    (output : CompTerm α) (accepted : GoodComp output) : GoodFormula (scheme.instantiate output) := by
  apply good.subst
  intro index
  cases index with
  | none => exact accepted
  | some index => exact good_var _

theorem good_lookup {schemes : SchemeEnv α} (good : GoodEnv schemes) (index : Nat)
    (output : CompTerm α) (accepted : GoodComp output) : GoodFormula (Scheme.lookup schemes index output) := by
  unfold Scheme.lookup
  cases found : schemes[index]? with
  | none => trivial
  | some scheme => exact (good scheme (List.mem_of_getElem? found)).instantiate output accepted

/-- The original generator preserves the support invariant for every good
captured environment and every good expected computation. Both branches of
a value let, including fresh scheme instantiations, are covered. -/
theorem good_generate (expression : Expr) (core : RecordFree expression)
    (schemes : SchemeEnv α) (environment : GoodEnv schemes)
    (output : CompTerm α) (accepted : GoodComp output) : GoodFormula (generate schemes expression output) := by
  induction expression generalizing α with
  | var index => exact good_lookup environment index output accepted
  | lit scalar => exact good_compLe rfl accepted
  | lam body ih =>
      exact ⟨ih core _ (environment.lift.lift.cons (good_mono (good_var _))) _ (good_var _),
        good_compLe rfl (accepted.rename _)⟩
  | app function argument ihf iha =>
      exact ⟨ihf core.1 _ environment.lift.lift.lift _ ⟨rfl, rfl⟩,
        iha core.2 _ environment.lift.lift.lift _ (good_var _), good_compLe rfl (accepted.rename _)⟩
  | letE definition body ihd ihb =>
      have generalized : GoodFormula (.and
          (generate schemes.lift definition (CompTerm.pure (.var none))) (.rowLe .empty (.var none))) :=
        ⟨ihd core.1 _ environment.lift _ ⟨rfl, rfl⟩, rfl⟩
      have monomorphic : GoodFormula (.existsSlot (.existsSlot (
          .and (generate (env₂ schemes) definition fresh₀)
            (.and (generate (Scheme.mono (CompTerm.pure fresh₀.ty) :: env₂ schemes) body fresh₁)
              (Formula.compLe ⟨fresh₁.ty, .join fresh₀.row fresh₁.row⟩ (lift₂ output)))))) :=
        ⟨ihd core.1 _ environment.lift.lift _ (good_var _),
          ihb core.2 _ (environment.lift.lift.cons (good_mono ⟨rfl, rfl⟩)) _ (good_var _),
          good_compLe rfl (accepted.rename _)⟩
      simp only [generate]
      split
      · exact ⟨⟨ihd core.1 _ environment.lift _ ⟨rfl, rfl⟩,
          ihb core.2 _ (environment.cons generalized) output accepted⟩,
          monomorphic⟩
      · exact monomorphic
  | branch condition yes no ihc ihy ihn =>
      exact ⟨ihc core.1 _ environment.lift.lift.lift _ ⟨rfl, rfl⟩,
        ihy core.2.1 _ environment.lift.lift.lift _ (good_var _),
        ihn core.2.2 _ environment.lift.lift.lift _ (good_var _), good_compLe rfl (accepted.rename _)⟩
  | pair left right ihl ihr =>
      exact ⟨ihl core.1 _ environment.lift.lift _ (good_var _),
        ihr core.2 _ environment.lift.lift _ (good_var _), good_compLe rfl (accepted.rename _)⟩
  | fst pair ih | snd pair ih =>
      exact ⟨ih core _ environment.lift.lift _ ⟨rfl, rfl⟩, good_compLe rfl (accepted.rename _)⟩
  | emptyRecord => exact good_compLe rfl accepted
  | record => cases core
  | field label record ih =>
      exact ⟨ih core _ environment.lift _ ⟨rfl, rfl⟩, good_compLe rfl (accepted.rename _)⟩
  | variant label payload ih =>
      exact ⟨ih core _ environment.lift _ (good_var _), good_compLe rfl (accepted.rename _)⟩

theorem good_principal (expression : Expr) (core : RecordFree expression)
    (schemes : SchemeEnv α) (environment : GoodEnv schemes) : GoodFormula (principal schemes expression) :=
  good_generate expression core schemes.lift environment.lift _ (good_var none)

def GoodAtom : Atom α → Prop
  | .tyLe left right => lowerTy left = true ∧ simpleTy right = true
  | .rowLe _ right => simpleRow right = true

def GoodAtoms (atoms : List (Atom α)) : Prop := ∀ atom ∈ atoms, GoodAtom atom

def GoodClause (clause : Clause α) : Prop := GoodAtoms clause.atoms

theorem GoodAtom.rename {atom : Atom α} (good : GoodAtom atom) (rename : α → β) :
    GoodAtom (atom.rename rename) := by cases atom <;> simpa [GoodAtom, Atom.rename] using good

theorem GoodAtoms.rename {atoms : List (Atom α)} (good : GoodAtoms atoms) (rename : α → β) :
    GoodAtoms (atoms.map (Atom.rename rename)) := by
  intro atom member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  exact (good original present).rename rename

theorem GoodAtoms.append {left right : List (Atom α)} (first : GoodAtoms left) (last : GoodAtoms right) :
    GoodAtoms (left ++ right) := by
  intro atom member
  exact (List.mem_append.mp member).elim (first atom) (last atom)

theorem good_empty : GoodClause (Clause.empty : Clause α) := by intro atom impossible; cases impossible

theorem good_singleton {atom : Atom α} (good : GoodAtom atom) : GoodClause (Clause.singleton atom) := by
  intro actual member
  have same := List.mem_singleton.mp member
  subst actual
  exact good.rename Sum.inr

theorem GoodClause.combine {left right : Clause α} (first : GoodClause left) (last : GoodClause right) :
    GoodClause (left.combine right) :=
  (first.rename (leftName left.locals right.locals)).append (last.rename (rightName left.locals right.locals))

theorem GoodClause.close {clause : Clause (Option α)} (good : GoodClause clause) : GoodClause clause.close :=
  good.rename (closeName clause.locals)

theorem good_normalise {formula : Formula α} (good : GoodFormula formula) :
    ∀ clause ∈ normalise formula, GoodClause clause := by
  induction formula with
  | top =>
      intro clause member
      have same := List.mem_singleton.mp member
      subst clause
      exact good_empty
  | bot => intro clause impossible; cases impossible
  | tyLe | rowLe =>
      intro clause member
      have same := List.mem_singleton.mp member
      subst clause
      exact good_singleton good
  | and left right ihl ihr =>
      intro clause member
      obtain ⟨first, present, member⟩ := List.mem_flatMap.mp member
      obtain ⟨last, inLast, rfl⟩ := List.mem_map.mp member
      exact (ihl good.1 first present).combine (ihr good.2 last inLast)
  | or left right ihl ihr =>
      intro clause member
      exact (List.mem_append.mp member).elim (ihl good.1 clause) (ihr good.2 clause)
  | existsSlot formula ih =>
      intro clause member
      obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
      exact (ih good original present).close

theorem good_pack {clause : Clause (Option Empty)} (good : GoodClause clause) : GoodAtoms clause.pack :=
  good.rename (resultName clause.locals)

/-! ## From syntactic invariants to the actual compiler and row stage -/

open TypeConstraintGraph

variable {n : Nat}

def ProblemSupported (problem : ConstraintProblems.Problem n) : Prop :=
  (∀ edge ∈ problem.types, lowerTy edge.1 = true ∧ simpleTy edge.2 = true) ∧
    ∀ row ∈ problem.rows, simpleRow row.2 = true

theorem good_split (atoms : List (Atom (Fin n))) (good : GoodAtoms atoms) :
    ProblemSupported (ConstraintProblems.split atoms) := by
  induction atoms with
  | nil => constructor <;> intro _ impossible <;> cases impossible
  | cons atom rest ih =>
      have first := good atom List.mem_cons_self
      have last := ih (fun atom member => good atom (List.mem_cons_of_mem _ member))
      cases atom with
      | tyLe left right =>
          refine ⟨?_, last.2⟩
          intro edge member
          rcases List.mem_cons.mp member with rfl | member
          · exact first
          · exact last.1 edge member
      | rowLe left right =>
          refine ⟨last.1, ?_⟩
          intro row member
          rcases List.mem_cons.mp member with rfl | member
          · exact first
          · exact last.2 row member

theorem simpleTy_rigid (term : TyTerm (Fin n)) (good : simpleTy term = true) : rigid term = true := by
  induction term with
  | var | base | bottom | top | emptyRecord => rfl
  | union | inter => cases good
  | pair left right ihl ihr =>
      have checks := Bool.and_eq_true_iff.mp good
      exact Bool.and_eq_true_iff.mpr ⟨ihl checks.1, ihr checks.2⟩
  | variant label payload ih => exact ih good
  | record label head rest ihh ihr =>
      have checks : (ValueBoundElimination.recordSpine rest = true ∧ simpleTy head = true) ∧
          simpleTy rest = true := by simpa only [simpleTy, Bool.and_eq_true] using good
      exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨checks.1.1, ihh checks.1.2⟩, ihr checks.2⟩
  | arrow input inputRow output outputRow ihi iho =>
      have checks : ((simpleTy input = true ∧ simpleRow inputRow = true) ∧ simpleTy output = true) ∧
          simpleRow outputRow = true := by simpa only [simpleTy, Bool.and_eq_true] using good
      exact Bool.and_eq_true_iff.mpr ⟨ihi checks.1.1.1, iho checks.1.2⟩

theorem simpleTy_subterms (term part : TyTerm (Fin n)) (good : simpleTy term = true)
    (member : part ∈ subterms term) : simpleTy part = true := by
  induction term with
  | var | base | bottom | top | emptyRecord =>
      have same := List.mem_singleton.mp member
      subst part
      exact good
  | union | inter => cases good
  | pair left right ihl ihr =>
      have checks := Bool.and_eq_true_iff.mp good
      rcases List.mem_cons.mp member with same | member
      · subst part; exact good
      · exact (List.mem_append.mp member).elim (ihl checks.1) (ihr checks.2)
  | arrow input inputRow output outputRow ihi iho =>
      have checks : ((simpleTy input = true ∧ simpleRow inputRow = true) ∧ simpleTy output = true) ∧
          simpleRow outputRow = true := by simpa only [simpleTy, Bool.and_eq_true] using good
      rcases List.mem_cons.mp member with same | member
      · subst part; exact good
      · exact (List.mem_append.mp member).elim (ihi checks.1.1.1) (iho checks.1.2)
  | record label head rest ihh ihr =>
      have checks : (ValueBoundElimination.recordSpine rest = true ∧ simpleTy head = true) ∧
          simpleTy rest = true := by simpa only [simpleTy, Bool.and_eq_true] using good
      rcases List.mem_cons.mp member with same | member
      · subst part; exact good
      · exact (List.mem_append.mp member).elim (ihh checks.1.2) (ihr checks.2)
  | variant label payload ih =>
      rcases List.mem_cons.mp member with same | member
      · subst part; exact good
      · exact ih good member

def SimpleProblem (problem : TypeConstraintGraph.Problem n) : Prop :=
  ∀ edge ∈ problem, simpleTy edge.1 = true ∧ simpleTy edge.2 = true

theorem SimpleProblem.append {left right : TypeConstraintGraph.Problem n}
    (first : SimpleProblem left) (last : SimpleProblem right) : SimpleProblem (left ++ right) := by
  intro edge member
  exact (List.mem_append.mp member).elim (first edge) (last edge)

theorem splitInequality_of_rigid (source target : TyTerm (Fin n))
    (first : rigid source = true) (last : rigid target = true) :
    splitInequality source target = some [(source, target)] := by
  rw [splitInequality.eq_def]
  split
  · cases first
  · cases last
  · simp [first, last]

theorem split_simple {source target : TyTerm (Fin n)}
    (first : simpleTy source = true) (last : simpleTy target = true) :
    ∃ normalized, splitInequality source target = some normalized ∧ SimpleProblem normalized := by
  refine ⟨[(source, target)], splitInequality_of_rigid source target (simpleTy_rigid source first)
    (simpleTy_rigid target last), ?_⟩
  intro edge member
  have same := List.mem_singleton.mp member
  subst edge
  exact ⟨first, last⟩

theorem split_lower {source target : TyTerm (Fin n)}
    (first : lowerTy source = true) (last : simpleTy target = true) :
    ∃ normalized, splitInequality source target = some normalized ∧ SimpleProblem normalized := by
  induction source with
  | union left right ihl ihr =>
      have checks := Bool.and_eq_true_iff.mp first
      obtain ⟨a, ha, ga⟩ := ihl checks.1
      obtain ⟨b, hb, gb⟩ := ihr checks.2
      refine ⟨a ++ b, ?_, ga.append gb⟩
      rw [splitInequality.eq_def]
      simp only [ha, hb, appendSome]
  | _ => exact split_simple first last

theorem splitProblem_good (problem : TypeConstraintGraph.Problem n)
    (good : ∀ edge ∈ problem, lowerTy edge.1 = true ∧ simpleTy edge.2 = true) :
    ∃ normalized, splitProblem problem = some normalized ∧ SimpleProblem normalized := by
  induction problem with
  | nil => exact ⟨[], rfl, by intro _ impossible; cases impossible⟩
  | cons edge rest ih =>
      obtain ⟨left, right⟩ := edge
      have first := good (left, right) List.mem_cons_self
      obtain ⟨a, ha, ga⟩ := split_lower first.1 first.2
      obtain ⟨b, hb, gb⟩ := ih (fun edge member => good edge (List.mem_cons_of_mem _ member))
      exact ⟨a ++ b, by simp only [splitProblem, ha, hb, appendSome], ga.append gb⟩

theorem collect_simple (problem : TypeConstraintGraph.Problem n) (valid : RigidProblem problem)
    (good : SimpleProblem problem) (term : TyTerm (Fin n)) (member : term ∈ (collect problem valid).terms) :
    simpleTy term = true := by
  have original := (mem_unique term (rawTerms problem)).mp member
  rcases List.mem_append.mp original with fromVars | fromProblem
  · obtain ⟨index, _, rfl⟩ := List.mem_map.mp fromVars
    rfl
  · obtain ⟨edge, present, fromEdge⟩ := List.mem_flatMap.mp fromProblem
    rcases List.mem_append.mp fromEdge with left | right
    · exact simpleTy_subterms _ _ (good edge present).1 left
    · exact simpleTy_subterms _ _ (good edge present).2 right

def simpleNodeRows : NestedValueSolver.Node size (RowTerm α) → Bool
  | .arrow _ inputRow _ outputRow => simpleRow inputRow && simpleRow outputRow
  | _ => true

theorem nodeOf_simpleRows (pool : Pool n) (term : TyTerm (Fin n)) (member : term ∈ pool.terms)
    (good : simpleTy term = true) :
    simpleNodeRows (nodeOf pool RowTerm.empty RowTerm.join RowTerm.var term member) = true := by
  cases term with
  | union | inter => cases good
  | arrow input inputRow output outputRow =>
      have checks : ((simpleTy input = true ∧ simpleRow inputRow = true) ∧ simpleTy output = true) ∧
          simpleRow outputRow = true := by simpa only [simpleTy, Bool.and_eq_true] using good
      simp only [nodeOf, simpleNodeRows, TypeConstraintRowInstantiation.rowEval_symbolic]
      exact Bool.and_eq_true_iff.mpr ⟨checks.1.1.2, checks.2⟩
  | _ => rfl

/-- Successful symbolic compilation and all row shapes follow from the
finite source syntax, before asking whether its constraints are consistent. -/
theorem problem_compiles (problem : ConstraintProblems.Problem n) (good : ProblemSupported problem) :
    ∃ compiled, TypeConstraintRowInstantiation.symbolicCompile problem.types = some compiled ∧
      (∀ node, simpleNodeRows (compiled.graph node) = true) := by
  obtain ⟨normalized, split, normalizedGood⟩ := splitProblem_good problem.types good.1
  let valid := splitProblem_some_rigid problem.types normalized split
  refine ⟨build RowTerm.empty RowTerm.join RowTerm.var normalized valid, ?_, ?_⟩
  · unfold TypeConstraintRowInstantiation.symbolicCompile compile
    split
    · rename_i missing
      rw [split] at missing
      cases missing
    · rename_i actual actualFound
      have same : actual = normalized := Option.some.inj (actualFound.symm.trans split)
      subst actual
      rfl
  · intro node
    exact nodeOf_simpleRows (collect normalized valid) _ _
      (collect_simple normalized valid normalizedGood _ ((collect normalized valid).at_mem node))

@[simp] theorem supportedConstraint_eq_simpleRow (row : RowFlowSchemes.Constraint n) :
    RowFlowSchemes.supportedConstraint row = simpleRow row.2 := by
  obtain ⟨left, right⟩ := row
  cases right <;> rfl

theorem inspect_rows_supported (source target : NestedValueSolver.Node size (RowTerm (Fin n)))
    (first : simpleNodeRows source = true) (last : simpleNodeRows target = true)
    (requirements : NestedValueSolver.Requirements size (RowTerm (Fin n)))
    (inspected : NestedValueSolver.inspect source target = some requirements) :
    RowFlowSchemes.supported requirements.rows = true := by
  cases source <;> cases target
  all_goals simp only [NestedValueSolver.inspect] at inspected
  all_goals try (cases inspected <;> rfl)
  case arrow.arrow a ea b eb c ec d ed =>
    have same := Option.some.inj inspected
    subst requirements
    have inputs := Bool.and_eq_true_iff.mp first
    have outputs := Bool.and_eq_true_iff.mp last
    simp only [RowFlowSchemes.supported, List.all_cons, List.all_nil,
      supportedConstraint_eq_simpleRow, Bool.and_true]
    exact Bool.and_eq_true_iff.mpr ⟨inputs.1, outputs.2⟩
  all_goals split at inspected <;> cases inspected <;> rfl

theorem rowRequirements_supported (graph : NestedRowRequirements.SymbolicGraph size n)
    (good : ∀ node, simpleNodeRows (graph node) = true) (cache : List (NestedValueSolver.Edge size)) :
    RowFlowSchemes.supported (NestedRowRequirements.rowRequirements graph cache) = true := by
  apply List.all_eq_true.mpr
  intro row member
  obtain ⟨edge, _, requirements, inspected, present⟩ :=
    (NestedRowRequirements.mem_rowRequirements graph cache row).mp member
  exact List.all_eq_true.mp (inspect_rows_supported (graph edge.1) (graph edge.2)
    (good edge.1) (good edge.2) requirements inspected) row present

theorem problem_rows_supported (problem : ConstraintProblems.Problem n) (good : ProblemSupported problem) :
    RowFlowSchemes.supported problem.rows = true := by
  apply List.all_eq_true.mpr
  intro row member
  simpa only [supportedConstraint_eq_simpleRow] using good.2 row member

/-- A represented problem may be rejected by its constructor checks, but it
cannot reach the unsupported-row branch after successful shape saturation. -/
theorem problem_rows_ne_unsupported (problem : ConstraintProblems.Problem n) (good : ProblemSupported problem)
    (compiled : Compiled n (RowTerm (Fin n)))
    (returned : TypeConstraintRowInstantiation.symbolicCompile problem.types = some compiled) :
    NestedRowRequirements.solveRows compiled.graph compiled.constraints problem.rows ≠ .unsupported := by
  obtain ⟨actual, found, graphGood⟩ := problem_compiles problem good
  have same : actual = compiled := Option.some.inj (found.symm.trans returned)
  subst actual
  intro unsupported
  obtain ⟨cache, _, rejectedRows⟩ :=
    (NestedRowRequirements.solveRows_unsupported_iff compiled.graph compiled.constraints problem.rows).mp unsupported
  have combined : RowFlowSchemes.supported (NestedRowRequirements.jointProblem problem.rows compiled.graph cache) = true := by
    simp only [NestedRowRequirements.jointProblem, RowFlowSchemes.supported, List.all_append]
    exact Bool.and_eq_true_iff.mpr ⟨problem_rows_supported problem good,
      rowRequirements_supported compiled.graph graphGood cache⟩
  have rejected := (RowFlowSchemes.solve_unsupported_iff _).mp rejectedRows
  rw [combined] at rejected
  cases rejected

/-- Every packed alternative of the original record-free generator satisfies
the syntactic compiler and row-flow support invariant. -/
theorem closed_clauses_supported (expression : Expr) (core : RecordFree expression)
    (clause : Clause (Option Empty)) (member : clause ∈ normalise (principal ([] : SchemeEnv Empty) expression)) :
    ProblemSupported (ConstraintProblems.split clause.pack) :=
  good_split clause.pack (good_pack (good_normalise (good_principal expression core []
    (by intro _ impossible; cases impossible)) clause member))

theorem closed_compiler_and_rows_supported (expression : Expr) (core : RecordFree expression)
    (clause : Clause (Option Empty)) (member : clause ∈ normalise (principal ([] : SchemeEnv Empty) expression)) :
    ∃ compiled, TypeConstraintRowInstantiation.symbolicCompile (ConstraintProblems.split clause.pack).types = some compiled ∧
      NestedRowRequirements.solveRows compiled.graph compiled.constraints
        (ConstraintProblems.split clause.pack).rows ≠ .unsupported := by
  have good := closed_clauses_supported expression core clause member
  obtain ⟨compiled, returned, _⟩ := problem_compiles _ good
  exact ⟨compiled, returned, problem_rows_ne_unsupported _ good compiled returned⟩

end Yulang.SourceConstraintSupport
