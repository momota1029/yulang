import Yulang.RecordConstraintSupport

/-!
# Singleton record demands in the original full source core

The original generator introduces demanded records through field selection,
with exactly one field and an empty tail. The property is preserved through
captured-name renaming, arbitrary substitutions that preserve this grammar,
both let branches, normalization, packing, and the existing polar preparation.
No source constructor is excluded. Open record construction still retains its
complete head and tail slots on the lower side.

Arbitrary externally supplied schemes need the strengthened `GoodEnv` below:
the older finite-spine invariant also allows multi-field demands. For closed
source expressions the stronger environment premise is discharged from the
empty environment by the generator itself.
-/

namespace Yulang.SingletonRecordDemands

open Inference ConstraintNormalForm

abbrev simpleRow := @SourceConstraintSupport.simpleRow

def emptyTail : TyTerm α → Bool
  | .emptyRecord => true
  | _ => false

/-- Every demanded record spine has one field; nested payloads may themselves
contain singleton records, functions, pairs, variants, and unknown slots. -/
def demandTy : TyTerm α → Bool
  | .var _ | .base _ | .bottom | .top | .emptyRecord => true
  | .union _ _ | .inter _ _ => false
  | .pair left right => demandTy left && demandTy right
  | .record _ value rest => emptyTail rest && demandTy value
  | .variant _ payload => demandTy payload
  | .arrow input inputRow output outputRow =>
      demandTy input && simpleRow inputRow && demandTy output && simpleRow outputRow

@[simp] theorem emptyTail_iff (term : TyTerm α) : emptyTail term = true ↔ term = .emptyRecord := by
  cases term <;> simp [emptyTail]

@[simp] theorem demand_record_iff (label : Nat) (value rest : TyTerm α) :
    demandTy (.record label value rest) = true ↔ rest = .emptyRecord ∧ demandTy value = true := by
  simp only [demandTy, Bool.and_eq_true, emptyTail_iff]

@[simp] theorem emptyTail_rename (rename : α → β) (term : TyTerm α) :
    emptyTail (term.rename rename) = emptyTail term := by
  cases term <;> rfl

@[simp] theorem demandTy_rename (rename : α → β) (term : TyTerm α) :
    demandTy (term.rename rename) = demandTy term := by
  induction term <;> simp_all [demandTy, TyTerm.rename, simpleRow,
    SourceConstraintSupport.simpleRow_rename]

def GoodComp (term : CompTerm α) : Prop := demandTy term.ty = true ∧ simpleRow term.row = true

theorem GoodComp.rename {term : CompTerm α} (good : GoodComp term) (rename : α → β) :
    GoodComp (term.rename rename) := by
  simpa [GoodComp, CompTerm.rename, simpleRow] using good

theorem good_var (index : α) : GoodComp (CompTerm.var index) := ⟨rfl, rfl⟩

/-- This is a genuine strengthening of the existing rigid-demand grammar. -/
theorem demand_implies_old (term : TyTerm α) (good : demandTy term = true) :
    RecordConstraintSupport.demandTy term = true := by
  induction term with
  | var | base | bottom | top | emptyRecord => rfl
  | union | inter => cases good
  | pair left right ihl ihr =>
      have checks := Bool.and_eq_true_iff.mp good
      exact Bool.and_eq_true_iff.mpr ⟨ihl checks.1, ihr checks.2⟩
  | variant label payload ih => exact ih good
  | record label value rest ihv _ =>
      obtain ⟨rfl, head⟩ := (demand_record_iff label value rest).mp good
      simpa [RecordConstraintSupport.demandTy, SourceConstraintSupport.simpleTy,
        ValueBoundElimination.recordSpine] using ihv head
  | arrow input inputRow output outputRow ihi iho =>
      have checks : ((demandTy input = true ∧ simpleRow inputRow = true) ∧
          demandTy output = true) ∧ simpleRow outputRow = true := by
        simpa only [demandTy, Bool.and_eq_true] using good
      exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr
        ⟨Bool.and_eq_true_iff.mpr ⟨ihi checks.1.1.1, checks.1.1.2⟩, iho checks.1.2⟩, checks.2⟩

theorem GoodComp.implies_old {term : CompTerm α} (good : GoodComp term) :
    SourceConstraintSupport.GoodComp term := ⟨demand_implies_old _ good.1, good.2⟩

theorem demandTy_subst (subst : α → CompTerm β) (assignment : ∀ index, GoodComp (subst index))
    (term : TyTerm α) (good : demandTy term = true) : demandTy (term.subst subst) = true := by
  induction term with
  | var index => exact (assignment index).1
  | base | bottom | top | emptyRecord => rfl
  | union | inter => cases good
  | pair left right ihl ihr =>
      have checks := Bool.and_eq_true_iff.mp good
      exact Bool.and_eq_true_iff.mpr ⟨ihl checks.1, ihr checks.2⟩
  | variant label payload ih => exact ih good
  | record label value rest ihv _ =>
      obtain ⟨rfl, head⟩ := (demand_record_iff label value rest).mp good
      simpa only [TyTerm.subst, demand_record_iff, true_and] using ihv head
  | arrow input inputRow output outputRow ihi iho =>
      have checks : ((demandTy input = true ∧ simpleRow inputRow = true) ∧
          demandTy output = true) ∧ simpleRow outputRow = true := by
        simpa only [demandTy, Bool.and_eq_true] using good
      simp only [TyTerm.subst, demandTy, Bool.and_eq_true]
      exact ⟨⟨⟨ihi checks.1.1.1,
        SourceConstraintSupport.simpleRow_subst subst (fun index => (assignment index).implies_old)
          inputRow checks.1.1.2⟩, iho checks.1.2⟩,
        SourceConstraintSupport.simpleRow_subst subst (fun index => (assignment index).implies_old)
          outputRow checks.2⟩

/-- Only the outer lower record may carry a nonempty or unknown tail. -/
def sourceHead : TyTerm α → Bool
  | .record _ value rest => demandTy value && demandTy rest
  | term => demandTy term

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
      obtain ⟨rfl, head⟩ := (demand_record_iff label value rest).mp good
      simpa [sourceHead, demandTy] using head
  | _ => exact good

theorem demand_implies_source {term : TyTerm α} (good : demandTy term = true) :
    sourceTy term = true := by
  cases term with
  | union => cases good
  | _ => exact demand_implies_head good

@[simp] theorem sourceHead_rename (rename : α → β) (term : TyTerm α) :
    sourceHead (term.rename rename) = sourceHead term := by
  cases term <;> simp [sourceHead, TyTerm.rename, demandTy,
    demandTy_rename,
    SourceConstraintSupport.simpleRow_rename]

@[simp] theorem sourceTy_rename (rename : α → β) (term : TyTerm α) :
    sourceTy (term.rename rename) = sourceTy term := by
  induction term <;> simp_all [sourceTy, sourceHead, TyTerm.rename, demandTy,
    demandTy_rename,
    SourceConstraintSupport.simpleRow_rename]

theorem sourceHead_subst (subst : α → CompTerm β) (assignment : ∀ index, GoodComp (subst index))
    (term : TyTerm α) (good : sourceHead term = true) :
    sourceHead (term.subst subst) = true := by
  cases term with
  | var index => exact demand_implies_head (assignment index).1
  | record label value rest =>
      have checks := Bool.and_eq_true_iff.mp good
      exact Bool.and_eq_true_iff.mpr
        ⟨demandTy_subst subst assignment value checks.1,
          demandTy_subst subst assignment rest checks.2⟩
  | _ =>
      exact demand_implies_head
        (demandTy_subst subst assignment _ good)

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
        (demandTy_subst subst assignment _ good)

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
        demandTy_subst subst assignment right good.2⟩
  | rowLe left right =>
      exact SourceConstraintSupport.simpleRow_subst subst
        (fun index => (assignment index).implies_old) right good
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
    (left : sourceTy source.ty = true) (right : GoodComp target) :
    GoodFormula (Formula.compLe source target) := ⟨⟨left, right.1⟩, right.2⟩

theorem good_mono {term : CompTerm α} (good : GoodComp term) : GoodFormula (Scheme.mono term) :=
  good_compLe (demand_implies_source (good.rename some).1) (good_var none)

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
      exact ⟨ih _ (environment.lift.lift.cons (good_mono (good_var _))) _
        (good_var _), good_compLe rfl (accepted.rename _)⟩
  | app function argument ihf iha =>
      exact ⟨ihf _ environment.lift.lift.lift _ ⟨rfl, rfl⟩,
        iha _ environment.lift.lift.lift _ (good_var _),
        good_compLe rfl (accepted.rename _)⟩
  | letE definition body ihd ihb =>
      have generalized : GoodFormula (.and
          (generate schemes.lift definition (CompTerm.pure (.var none))) (.rowLe .empty (.var none))) :=
        ⟨ihd _ environment.lift _ ⟨rfl, rfl⟩, rfl⟩
      have monomorphic : GoodFormula (.existsSlot (.existsSlot (
          .and (generate (env₂ schemes) definition fresh₀)
            (.and (generate (Scheme.mono (CompTerm.pure fresh₀.ty) :: env₂ schemes) body fresh₁)
              (Formula.compLe ⟨fresh₁.ty, .join fresh₀.row fresh₁.row⟩ (lift₂ output)))))) :=
        ⟨ihd _ environment.lift.lift _ (good_var _),
          ihb _ (environment.lift.lift.cons (good_mono ⟨rfl, rfl⟩)) _
            (good_var _), good_compLe rfl (accepted.rename _)⟩
      simp only [generate]
      split
      · exact ⟨⟨ihd _ environment.lift _ ⟨rfl, rfl⟩,
          ihb _ (environment.cons generalized) output accepted⟩, monomorphic⟩
      · exact monomorphic
  | branch condition yes no ihc ihy ihn =>
      exact ⟨ihc _ environment.lift.lift.lift _ ⟨rfl, rfl⟩,
        ihy _ environment.lift.lift.lift _ (good_var _),
        ihn _ environment.lift.lift.lift _ (good_var _),
        good_compLe rfl (accepted.rename _)⟩
  | pair left right ihl ihr =>
      exact ⟨ihl _ environment.lift.lift _ (good_var _),
        ihr _ environment.lift.lift _ (good_var _),
        good_compLe rfl (accepted.rename _)⟩
  | fst pair ih | snd pair ih =>
      exact ⟨ih _ environment.lift.lift _ ⟨rfl, rfl⟩, good_compLe rfl (accepted.rename _)⟩
  | emptyRecord => exact good_compLe rfl accepted
  | record label value rest ihv ihr =>
      exact ⟨ihv _ environment.lift.lift _ (good_var _),
        ihr _ environment.lift.lift _ (good_var _),
        ⟨rfl, rfl⟩, good_compLe rfl (accepted.rename _)⟩
  | field label record ih =>
      exact ⟨ih _ environment.lift _ ⟨rfl, rfl⟩, good_compLe rfl (accepted.rename _)⟩
  | variant label payload ih =>
      exact ⟨ih _ environment.lift _ (good_var _),
        good_compLe rfl (accepted.rename _)⟩

theorem good_principal (expression : Expr) (schemes : SchemeEnv α) (environment : GoodEnv schemes) :
    GoodFormula (principal schemes expression) :=
  good_generate expression schemes.lift environment.lift _ (good_var none)

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


/-! ## The actual preparation preserves singleton demands -/

def PreparedTypes (problem : TypeConstraintGraph.Problem n) : Prop :=
  ∀ edge ∈ problem, sourceHead edge.1 = true ∧ demandTy edge.2 = true

theorem flattenSource_polar (source target : TyTerm (Fin n))
    (first : sourceTy source = true) (last : demandTy target = true) :
    PreparedTypes (RecordConstraintSupport.flattenSource source target) := by
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
    PreparedTypes (RecordConstraintSupport.prepare problem).types ∧
      ∀ row ∈ (RecordConstraintSupport.prepare problem).rows, simpleRow row.2 = true := by
  refine ⟨?_, good.2⟩
  intro edge member
  obtain ⟨original, present, member⟩ := List.mem_flatMap.mp member
  exact flattenSource_polar _ _ (good.1 original present).1 (good.1 original present).2 edge member

/-- This statement has no fragment, typing, or successful-inference premise. -/
theorem closed_prepared_polar (expression : Expr) (clause : Clause (Option Empty))
    (member : clause ∈ normalise (principal ([] : SchemeEnv Empty) expression)) :
    PreparedTypes (RecordConstraintSupport.prepare (ConstraintProblems.split clause.pack)).types ∧
      ∀ row ∈ (RecordConstraintSupport.prepare (ConstraintProblems.split clause.pack)).rows,
        simpleRow row.2 = true :=
  prepare_polar _ (closed_clauses_polar expression clause member)

/-! ## Constructor children are demands too -/

theorem demandTy_subterms (term part : TyTerm (Fin n)) (good : demandTy term = true)
    (member : part ∈ TypeConstraintGraph.subterms term) : demandTy part = true := by
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
      have checks : ((demandTy input = true ∧ simpleRow inputRow = true) ∧
          demandTy output = true) ∧ simpleRow outputRow = true := by
        simpa only [demandTy, Bool.and_eq_true] using good
      rcases List.mem_cons.mp member with same | member
      · subst part; exact good
      · exact (List.mem_append.mp member).elim (ihi checks.1.1.1) (iho checks.1.2)
  | record label value rest ihv ihr =>
      have checks := (demand_record_iff label value rest).mp good
      have restGood : demandTy rest = true := by rw [checks.1]; rfl
      rcases List.mem_cons.mp member with same | member
      · subst part; exact good
      · exact (List.mem_append.mp member).elim (ihv checks.2) (ihr restGood)
  | variant label payload ih =>
      rcases List.mem_cons.mp member with same | member
      · subst part; exact good
      · exact ih good member

/-- All proper children of an open construction are singleton-demand types.
The construction's original tail is still retained, without replacing it. -/
theorem sourceHead_proper_subterm (source part : TyTerm (Fin n))
    (good : sourceHead source = true) (member : part ∈ TypeConstraintGraph.subterms source)
    (different : part ≠ source) : demandTy part = true := by
  cases source with
  | record label value rest =>
      have checks := Bool.and_eq_true_iff.mp good
      rcases List.mem_cons.mp member with same | member
      · exact False.elim (different same)
      · exact (List.mem_append.mp member).elim
          (demandTy_subterms value part checks.1) (demandTy_subterms rest part checks.2)
  | _ => exact demandTy_subterms _ part good member

theorem sourceHead_subterms (source part : TyTerm (Fin n))
    (good : sourceHead source = true) (inside : part ∈ TypeConstraintGraph.subterms source) :
    sourceHead part = true := by
  by_cases same : part = source
  · subst part; exact good
  · exact demand_implies_head (sourceHead_proper_subterm source part good inside same)

/-- Every syntactically rigid record demand is empty or a singleton. Unknown
slots remain unknown; this theorem puts no restriction on their assignments. -/
theorem demand_record_shape (term : TyTerm α) (good : demandTy term = true)
    (rigid : ValueBoundElimination.recordSpine term = true) :
    term = .emptyRecord ∨ ∃ label value, term = .record label value .emptyRecord ∧ demandTy value = true := by
  cases term with
  | emptyRecord => exact Or.inl rfl
  | record label value rest =>
      obtain ⟨rfl, head⟩ := (demand_record_iff label value rest).mp good
      exact Or.inr ⟨label, value, rfl, head⟩
  | _ => cases rigid

/-- The older external-scheme premise alone cannot imply singleton demands. -/
theorem older_grammar_allows_two_fields :
    RecordConstraintSupport.demandTy
      (.record 0 (.base .int) (.record 1 (.base .bool) .emptyRecord) : TyTerm Empty) = true ∧
    demandTy (.record 0 (.base .int) (.record 1 (.base .bool) .emptyRecord) : TyTerm Empty) = false :=
  ⟨rfl, rfl⟩

/-- A pre-existing scheme with a longer fixed spine satisfies the older
environment invariant, but a variable use still exposes that longer demand.
The strengthened scheme premise in `good_generate` is therefore necessary. -/
theorem older_goodEnv_insufficient :
    ∃ schemes : SchemeEnv Unit, RecordConstraintSupport.GoodEnv schemes ∧
      ¬ GoodFormula (generate schemes (.var 0) (CompTerm.var ())) := by
  refine ⟨[.tyLe .bottom (.record 0 (.base .int) (.record 1 (.base .bool) .emptyRecord))], ?_, ?_⟩
  · intro scheme member
    have same := List.mem_singleton.mp member
    subst scheme
    exact ⟨rfl, rfl⟩
  · change ¬ (true = true ∧ false = true)
    intro impossible
    cases impossible.2

end Yulang.SingletonRecordDemands
