import Yulang.SourceConstraintSupport

/-!
# Polar preparation of constraints from the whole original source core

The original generator introduces a record extension only as a lower bound.
Its value and tail are ordinary computation slots. Upper record requirements
come from field selection and have fixed spines. This distinction survives
the actual scheme substitution, captured-name renaming, and both value-let
branches; it does not require the source expression to be RecordFree.

The executable preparation below splits only outer lower unions. It preserves
every original type and row assignment in any model where union is a join.
After preparation, an open record can occur only as an entire lower endpoint,
never as an upper endpoint or a proper constructor child. The tail term and
all its slot correlations are retained verbatim.

This is a representation theorem for the next solver layer. It neither proves
that the old fixed-spine compiler accepts these problems nor changes the
meaning of record extension to make field-demand propagation valid.
-/

namespace Yulang.RecordConstraintSupport

open Inference ConstraintNormalForm

/-- Demand types retain the existing finite-spine and simple-row grammar. -/
abbrev demandTy := @SourceConstraintSupport.simpleTy
abbrev simpleRow := @SourceConstraintSupport.simpleRow
abbrev GoodComp := @SourceConstraintSupport.GoodComp

/-- One lower constructor. Only its outer record extension may have an
unknown tail; its proper subterms remain demand types. -/
def sourceHead : TyTerm α → Bool
  | .record _ value rest => demandTy value && demandTy rest
  | term => demandTy term

/-- Outer unions are the only lattice terms emitted on the lower side. -/
def sourceTy : TyTerm α → Bool
  | .union left right => sourceTy left && sourceTy right
  | term => sourceHead term

def GoodFormula : Formula α → Prop
  | .top | .bot => True
  | .and left right | .or left right => GoodFormula left ∧ GoodFormula right
  | .tyLe left right => sourceTy left = true ∧ demandTy right = true
  | .rowLe _ right => simpleRow right = true
  | .existsSlot formula => GoodFormula formula

def GoodEnv (schemes : SchemeEnv α) : Prop := ∀ scheme ∈ schemes, GoodFormula scheme

theorem demand_implies_head {term : TyTerm α} (good : demandTy term = true) :
    sourceHead term = true := by
  cases term with
  | record label value rest =>
      have checks : (ValueBoundElimination.recordSpine rest = true ∧ demandTy value = true) ∧
          demandTy rest = true := by
        simpa only [demandTy, SourceConstraintSupport.simpleTy, Bool.and_eq_true] using good
      exact Bool.and_eq_true_iff.mpr ⟨checks.1.2, checks.2⟩
  | _ => exact good

theorem demand_implies_source {term : TyTerm α} (good : demandTy term = true) :
    sourceTy term = true := by
  cases term with
  | union => cases good
  | _ => exact demand_implies_head good

@[simp] theorem sourceHead_rename (rename : α → β) (term : TyTerm α) :
    sourceHead (term.rename rename) = sourceHead term := by
  cases term <;> simp [sourceHead, TyTerm.rename, demandTy,
    SourceConstraintSupport.simpleTy_rename, SourceConstraintSupport.simpleTy,
    SourceConstraintSupport.simpleRow_rename]

@[simp] theorem sourceTy_rename (rename : α → β) (term : TyTerm α) :
    sourceTy (term.rename rename) = sourceTy term := by
  induction term <;> simp_all [sourceTy, sourceHead, TyTerm.rename, demandTy,
    SourceConstraintSupport.simpleTy, SourceConstraintSupport.simpleTy_rename,
    SourceConstraintSupport.simpleRow_rename]

theorem sourceHead_subst (subst : α → CompTerm β) (assignment : ∀ index, GoodComp (subst index))
    (term : TyTerm α) (good : sourceHead term = true) :
    sourceHead (term.subst subst) = true := by
  cases term with
  | var index => exact demand_implies_head (assignment index).1
  | record label value rest =>
      have checks := Bool.and_eq_true_iff.mp good
      exact Bool.and_eq_true_iff.mpr
        ⟨SourceConstraintSupport.simpleTy_subst subst assignment value checks.1,
          SourceConstraintSupport.simpleTy_subst subst assignment rest checks.2⟩
  | _ =>
      exact demand_implies_head
        (SourceConstraintSupport.simpleTy_subst subst assignment _ good)

theorem sourceTy_subst (subst : α → CompTerm β) (assignment : ∀ index, GoodComp (subst index))
    (term : TyTerm α) (good : sourceTy term = true) : sourceTy (term.subst subst) = true := by
  induction term with
  | var index => exact demand_implies_source (assignment index).1
  | union left right ihl ihr =>
      have checks := Bool.and_eq_true_iff.mp good
      exact Bool.and_eq_true_iff.mpr ⟨ihl checks.1, ihr checks.2⟩
  | record label value rest =>
      exact sourceHead_subst subst assignment _ good
  | _ =>
      exact demand_implies_source
        (SourceConstraintSupport.simpleTy_subst subst assignment _ good)

theorem GoodFormula.rename {formula : Formula α} (good : GoodFormula formula) (rename : α → β) :
    GoodFormula (formula.rename rename) := by
  induction formula generalizing β with
  | top | bot => trivial
  | and _ _ ihl ihr | or _ _ ihl ihr => exact ⟨ihl good.1 rename, ihr good.2 rename⟩
  | tyLe left right =>
      simpa [GoodFormula, Formula.rename, demandTy] using good
  | rowLe left right =>
      simpa [GoodFormula, Formula.rename, simpleRow] using good
  | existsSlot formula ih => exact ih good (Option.map rename)

theorem GoodFormula.subst {formula : Formula α} (good : GoodFormula formula)
    (subst : α → CompTerm β) (assignment : ∀ index, GoodComp (subst index)) :
    GoodFormula (formula.subst subst) := by
  induction formula generalizing β with
  | top | bot => trivial
  | and _ _ ihl ihr | or _ _ ihl ihr =>
      exact ⟨ihl good.1 subst assignment, ihr good.2 subst assignment⟩
  | tyLe left right =>
      exact ⟨sourceTy_subst subst assignment left good.1,
        SourceConstraintSupport.simpleTy_subst subst assignment right good.2⟩
  | rowLe left right =>
      exact SourceConstraintSupport.simpleRow_subst subst assignment right good
  | existsSlot formula ih =>
      apply ih good (liftSubst subst)
      intro index
      cases index with
      | none => exact SourceConstraintSupport.good_var _
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
    (left : sourceTy source.ty = true) (right : GoodComp target) :
    GoodFormula (Formula.compLe source target) := ⟨⟨left, right.1⟩, right.2⟩

theorem good_mono {term : CompTerm α} (good : GoodComp term) : GoodFormula (Scheme.mono term) :=
  good_compLe (demand_implies_source (good.rename some).1) (SourceConstraintSupport.good_var none)

theorem GoodFormula.instantiate {scheme : Scheme α} (good : GoodFormula scheme)
    (output : CompTerm α) (accepted : GoodComp output) : GoodFormula (scheme.instantiate output) := by
  apply good.subst
  intro index
  cases index with
  | none => exact accepted
  | some index => exact SourceConstraintSupport.good_var _

theorem good_lookup {schemes : SchemeEnv α} (good : GoodEnv schemes) (index : Nat)
    (output : CompTerm α) (accepted : GoodComp output) : GoodFormula (Scheme.lookup schemes index output) := by
  unfold Scheme.lookup
  cases found : schemes[index]? with
  | none => trivial
  | some scheme => exact (good scheme (List.mem_of_getElem? found)).instantiate output accepted

/-- The original generator has this polar shape for every source expression,
every invariant captured environment, and every demand-shaped target. No
RecordFree restriction, successful run, or satisfiable assignment is assumed. -/
theorem good_generate (expression : Expr)
    (schemes : SchemeEnv α) (environment : GoodEnv schemes)
    (output : CompTerm α) (accepted : GoodComp output) : GoodFormula (generate schemes expression output) := by
  induction expression generalizing α with
  | var index => exact good_lookup environment index output accepted
  | lit scalar => exact good_compLe rfl accepted
  | lam body ih =>
      exact ⟨ih _ (environment.lift.lift.cons (good_mono (SourceConstraintSupport.good_var _))) _
        (SourceConstraintSupport.good_var _), good_compLe rfl (accepted.rename _)⟩
  | app function argument ihf iha =>
      exact ⟨ihf _ environment.lift.lift.lift _ ⟨rfl, rfl⟩,
        iha _ environment.lift.lift.lift _ (SourceConstraintSupport.good_var _),
        good_compLe rfl (accepted.rename _)⟩
  | letE definition body ihd ihb =>
      have generalized : GoodFormula (.and
          (generate schemes.lift definition (CompTerm.pure (.var none))) (.rowLe .empty (.var none))) :=
        ⟨ihd _ environment.lift _ ⟨rfl, rfl⟩, rfl⟩
      have monomorphic : GoodFormula (.existsSlot (.existsSlot (
          .and (generate (env₂ schemes) definition fresh₀)
            (.and (generate (Scheme.mono (CompTerm.pure fresh₀.ty) :: env₂ schemes) body fresh₁)
              (Formula.compLe ⟨fresh₁.ty, .join fresh₀.row fresh₁.row⟩ (lift₂ output)))))) :=
        ⟨ihd _ environment.lift.lift _ (SourceConstraintSupport.good_var _),
          ihb _ (environment.lift.lift.cons (good_mono ⟨rfl, rfl⟩)) _
            (SourceConstraintSupport.good_var _), good_compLe rfl (accepted.rename _)⟩
      simp only [generate]
      split
      · exact ⟨⟨ihd _ environment.lift _ ⟨rfl, rfl⟩,
          ihb _ (environment.cons generalized) output accepted⟩, monomorphic⟩
      · exact monomorphic
  | branch condition yes no ihc ihy ihn =>
      exact ⟨ihc _ environment.lift.lift.lift _ ⟨rfl, rfl⟩,
        ihy _ environment.lift.lift.lift _ (SourceConstraintSupport.good_var _),
        ihn _ environment.lift.lift.lift _ (SourceConstraintSupport.good_var _),
        good_compLe rfl (accepted.rename _)⟩
  | pair left right ihl ihr =>
      exact ⟨ihl _ environment.lift.lift _ (SourceConstraintSupport.good_var _),
        ihr _ environment.lift.lift _ (SourceConstraintSupport.good_var _),
        good_compLe rfl (accepted.rename _)⟩
  | fst pair ih | snd pair ih =>
      exact ⟨ih _ environment.lift.lift _ ⟨rfl, rfl⟩, good_compLe rfl (accepted.rename _)⟩
  | emptyRecord => exact good_compLe rfl accepted
  | record label value rest ihv ihr =>
      exact ⟨ihv _ environment.lift.lift _ (SourceConstraintSupport.good_var _),
        ihr _ environment.lift.lift _ (SourceConstraintSupport.good_var _),
        ⟨rfl, rfl⟩, good_compLe rfl (accepted.rename _)⟩
  | field label record ih =>
      exact ⟨ih _ environment.lift _ ⟨rfl, rfl⟩, good_compLe rfl (accepted.rename _)⟩
  | variant label payload ih =>
      exact ⟨ih _ environment.lift _ (SourceConstraintSupport.good_var _),
        good_compLe rfl (accepted.rename _)⟩

theorem good_principal (expression : Expr) (schemes : SchemeEnv α) (environment : GoodEnv schemes) :
    GoodFormula (principal schemes expression) :=
  good_generate expression schemes.lift environment.lift _ (SourceConstraintSupport.good_var none)

def GoodAtom : Atom α → Prop
  | .tyLe left right => sourceTy left = true ∧ demandTy right = true
  | .rowLe _ right => simpleRow right = true

def GoodAtoms (atoms : List (Atom α)) : Prop := ∀ atom ∈ atoms, GoodAtom atom
def GoodClause (clause : Clause α) : Prop := GoodAtoms clause.atoms

theorem GoodAtom.rename {atom : Atom α} (good : GoodAtom atom) (rename : α → β) :
    GoodAtom (atom.rename rename) := by
  cases atom <;> simpa [GoodAtom, Atom.rename, demandTy, simpleRow] using good

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

variable {n : Nat}

def ProblemPolar (problem : ConstraintProblems.Problem n) : Prop :=
  (∀ edge ∈ problem.types, sourceTy edge.1 = true ∧ demandTy edge.2 = true) ∧
    ∀ row ∈ problem.rows, simpleRow row.2 = true

theorem good_split (atoms : List (Atom (Fin n))) (good : GoodAtoms atoms) :
    ProblemPolar (ConstraintProblems.split atoms) := by
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

/-- Every original core expression yields polar clauses, including record
construction and both branches of every value-restricted let. -/
theorem closed_clauses_polar (expression : Expr) (clause : Clause (Option Empty))
    (member : clause ∈ normalise (principal ([] : SchemeEnv Empty) expression)) :
    ProblemPolar (ConstraintProblems.split clause.pack) :=
  good_split clause.pack (good_pack (good_normalise (good_principal expression []
    (by intro _ impossible; cases impossible)) clause member))

/-! ## Exact executable preparation, retaining the original tail terms -/

def flattenSource (source target : TyTerm α) : List (TyTerm α × TyTerm α) :=
  match source with
  | .union left right => flattenSource left target ++ flattenSource right target
  | source => [(source, target)]

def prepareTypes (problem : TypeConstraintGraph.Problem n) : TypeConstraintGraph.Problem n :=
  problem.flatMap fun edge => flattenSource edge.1 edge.2

def prepare (problem : ConstraintProblems.Problem n) : ConstraintProblems.Problem n :=
  ⟨prepareTypes problem.types, problem.rows⟩

def PreparedTypes (problem : TypeConstraintGraph.Problem n) : Prop :=
  ∀ edge ∈ problem, sourceHead edge.1 = true ∧ demandTy edge.2 = true

/-- Only the defining property of union is needed for this preparation. -/
def UnionIsJoin (model : Model) : Prop :=
  ∀ a b c, model.subTy (model.union a b) c ↔ model.subTy a c ∧ model.subTy b c

theorem flattenSource_polar (source target : TyTerm (Fin n))
    (first : sourceTy source = true) (last : demandTy target = true) :
    PreparedTypes (flattenSource source target) := by
  induction source with
  | union left right ihl ihr =>
      have checks := Bool.and_eq_true_iff.mp first
      intro edge member
      exact (List.mem_append.mp member).elim (ihl checks.1 edge) (ihr checks.2 edge)
  | _ =>
      intro edge member
      have same := List.mem_singleton.mp member
      subst edge
      exact ⟨first, last⟩

theorem prepare_polar (problem : ConstraintProblems.Problem n) (good : ProblemPolar problem) :
    PreparedTypes (prepare problem).types ∧
      ∀ row ∈ (prepare problem).rows, simpleRow row.2 = true := by
  refine ⟨?_, good.2⟩
  intro edge member
  obtain ⟨original, present, member⟩ := List.mem_flatMap.mp member
  exact flattenSource_polar _ _ (good.1 original present).1 (good.1 original present).2 edge member

theorem flattenSource_exact (model : Model) (unionIsJoin : UnionIsJoin model)
    (rows : Fin n → model.Row) (values : Fin n → model.Ty)
    (source target : TyTerm (Fin n)) :
    TypeConstraintGraph.Holds model rows values (flattenSource source target) ↔
      model.subTy (TypeConstraintGraph.evaluate model rows values source)
        (TypeConstraintGraph.evaluate model rows values target) := by
  induction source with
  | union left right ihl ihr =>
      rw [flattenSource, TypeConstraintGraph.holds_append, ihl, ihr]
      exact (unionIsJoin _ _ _).symm
  | _ => simp [flattenSource, TypeConstraintGraph.holds_cons]

/-- Preparation changes neither the value assignment nor its paired row
assignment; no record law or successful solver is a premise. -/
theorem prepare_exact (model : Model) (unionIsJoin : UnionIsJoin model)
    (problem : ConstraintProblems.Problem n) (values : Fin n → model.Ty) (rows : Fin n → model.Row) :
    (prepare problem).Holds model values rows ↔ problem.Holds model values rows := by
  unfold prepare ConstraintProblems.Problem.Holds
  apply and_congr_left
  intro _
  change TypeConstraintGraph.Holds model rows values (prepareTypes problem.types) ↔ _
  generalize problem.types = types
  induction types with
  | nil => rfl
  | cons edge rest ih =>
      change TypeConstraintGraph.Holds model rows values
        (flattenSource edge.1 edge.2 ++ prepareTypes rest) ↔ _
      rw [TypeConstraintGraph.holds_append, TypeConstraintGraph.holds_cons,
        flattenSource_exact model unionIsJoin rows values, ih]

theorem prepare_instances_exact (model : Model) (unionIsJoin : UnionIsJoin model)
    (problem : ConstraintProblems.Problem n) (output : Fin n) (target : Comp model) :
    (prepare problem).Instance model output target ↔ problem.Instance model output target := by
  unfold ConstraintProblems.Problem.Instance
  apply exists_congr
  intro values
  apply exists_congr
  intro rows
  exact and_congr_left (fun _ => prepare_exact model unionIsJoin problem values rows)

/-- The complete original source judgment is exactly the finite disjunction
of the prepared constraint problems. Their atoms still need to be solved;
this theorem does not claim a principal free-parameter scheme. -/
theorem closed_prepared_typing_exact (model : Model) (unionIsJoin : UnionIsJoin model)
    (tyRefl : ∀ type, model.subTy type type)
    (tyTrans : ∀ {a b c}, model.subTy a b → model.subTy b c → model.subTy a c)
    (rowRefl : ∀ row, model.subRow row row)
    (rowTrans : ∀ {a b c}, model.subRow a b → model.subRow b c → model.subRow a c)
    (expression : Expr) (target : Comp model) :
    Typing model [] expression target ↔
      ∃ clause ∈ normalise (principal ([] : SchemeEnv Empty) expression),
        (prepare (ConstraintProblems.split clause.pack)).Instance model (Fin.last clause.locals) target := by
  rw [ConstraintProblems.closed_source_problems_exact model tyRefl tyTrans rowRefl rowTrans expression target]
  apply exists_congr
  intro clause
  exact and_congr_right (fun _ => (prepare_instances_exact model unionIsJoin
    (ConstraintProblems.split clause.pack) (Fin.last clause.locals) target).symm)

/-! ## The new constructor never occurs in a negative endpoint or a child -/

def openRecord : TyTerm α → Bool
  | .record _ _ rest => !ValueBoundElimination.recordSpine rest
  | _ => false

theorem demand_not_open {term : TyTerm α} (good : demandTy term = true) : openRecord term = false := by
  cases term with
  | record label value rest =>
      have shape : ValueBoundElimination.recordSpine rest = true :=
        (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp good).1).1
      simp [openRecord, shape]
  | _ => rfl

/-- Every proper subterm of a prepared lower endpoint is already in the old
fixed-spine grammar. Only the whole lower endpoint can need extension. -/
theorem sourceHead_proper_subterm (source part : TyTerm (Fin n))
    (good : sourceHead source = true) (member : part ∈ TypeConstraintGraph.subterms source)
    (different : part ≠ source) : demandTy part = true := by
  cases source with
  | record label value rest =>
      have checks := Bool.and_eq_true_iff.mp good
      rcases List.mem_cons.mp member with same | member
      · exact False.elim (different same)
      · exact (List.mem_append.mp member).elim
          (SourceConstraintSupport.simpleTy_subterms value part checks.1)
          (SourceConstraintSupport.simpleTy_subterms rest part checks.2)
  | _ => exact SourceConstraintSupport.simpleTy_subterms _ part good member

theorem sourceHead_open_subterm (source part : TyTerm (Fin n))
    (good : sourceHead source = true) (member : part ∈ TypeConstraintGraph.subterms source)
    (opened : openRecord part = true) : part = source := by
  by_cases same : part = source
  · exact same
  · have absent := demand_not_open (sourceHead_proper_subterm source part good member same)
    rw [opened] at absent
    cases absent

theorem demand_no_open_subterm (target part : TyTerm (Fin n)) (good : demandTy target = true)
    (member : part ∈ TypeConstraintGraph.subterms target) : openRecord part = false :=
  demand_not_open (SourceConstraintSupport.simpleTy_subterms target part good member)

/-- All generated alternatives, including inconsistent ones, have the
finite preparation needed by an open-record lower-bound solver. -/
theorem closed_prepared_polar (expression : Expr) (clause : Clause (Option Empty))
    (member : clause ∈ normalise (principal ([] : SchemeEnv Empty) expression)) :
    PreparedTypes (prepare (ConstraintProblems.split clause.pack)).types ∧
      ∀ row ∈ (prepare (ConstraintProblems.split clause.pack)).rows, simpleRow row.2 = true :=
  prepare_polar _ (closed_clauses_polar expression clause member)

/-- In every prepared constraint, an open record node can appear only as
the entire lower endpoint. This is syntactic support, not satisfiability. -/
theorem closed_open_records_are_lower_roots (expression : Expr) (clause : Clause (Option Empty))
    (member : clause ∈ normalise (principal ([] : SchemeEnv Empty) expression))
    (edge : TyTerm (Fin (clause.locals + 1)) × TyTerm (Fin (clause.locals + 1)))
    (present : edge ∈ (prepare (ConstraintProblems.split clause.pack)).types) :
    (∀ part ∈ TypeConstraintGraph.subterms edge.1, openRecord part = true → part = edge.1) ∧
      ∀ part ∈ TypeConstraintGraph.subterms edge.2, openRecord part = false := by
  have shape := (closed_prepared_polar expression clause member).1 edge present
  exact ⟨fun part inside opened => sourceHead_open_subterm _ part shape.1 inside opened,
    fun part inside => demand_no_open_subterm _ part shape.2 inside⟩

end Yulang.RecordConstraintSupport
