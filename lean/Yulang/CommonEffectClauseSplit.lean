import Yulang.CommonEffectComputationSplit
import Yulang.CommonEffectClauseNormalisation
import Yulang.CommonEffectBoundTemplates

/-! Joint splitting of all computation witnesses in an actual finite clause.
Every original row identifier is retained in rigid endpoint arrow rows; all
local value witnesses are exposed to one shared flat-bound extraction. The
result is exact finite Formula syntax, retaining unsupported pure binders.
This is a satisfiability projection, not recovery of all internal valuations. -/
namespace Yulang.CommonEffectClauseSplit
open Common (Ty)
open Core.PresenceGeneration (CompTerm extend)
open CommonEffectRequestGeneration (Computation localEnv)
open CommonEffectFormula (Formula)
open CommonEffectClauses (Atom Clause)

variable {scopes : Nat}

def peel (count : Nat) : Fin (count + 1) ⊕ α → Fin count ⊕ Option α
  | .inl index => Fin.lastCases (.inr none) (fun index => .inl index) index
  | .inr name => .inr (some name)

def closeSlots : (count : Nat) → Formula scopes (Fin count ⊕ α) → Formula scopes α
  | 0, body => body.rename (Sum.elim Fin.elim0 id)
  | count + 1, body => .existsSlot (closeSlots count (body.rename (peel count)))

theorem peel_assignment (assignment : α → Computation) (values : Fin count → Computation) (fresh : Computation) :
    Sum.elim values (extend assignment fresh) ∘ peel count = Sum.elim (Fin.lastCases fresh values) assignment := by
  funext name
  cases name with
  | inl index => refine Fin.lastCases ?_ (fun index => ?_) index <;> simp [peel]
  | inr => rfl

theorem closeSlots_exact (count : Nat) (body : Formula scopes (Fin count ⊕ α)) (assignment : α → Computation) :
    (closeSlots count body).Holds assignment ↔ ∃ values : Fin count → Computation, body.Holds (Sum.elim values assignment) := by
  induction count generalizing α with
  | zero =>
    simp only [closeSlots, Formula.holds_rename]
    have zeroEnv (values : Fin 0 → Computation) : Sum.elim values assignment = assignment ∘ Sum.elim Fin.elim0 id := by
      funext name
      cases name with
      | inl index => exact Fin.elim0 index
      | inr name => rfl
    constructor
    · intro accepted
      exact ⟨Fin.elim0, by rw [zeroEnv]; exact accepted⟩
    · rintro ⟨values, accepted⟩
      rw [zeroEnv] at accepted
      exact accepted
  | succ count ih =>
    simp only [closeSlots, Formula.Holds, ih, Formula.holds_rename, peel_assignment]
    constructor
    · rintro ⟨fresh, values, accepted⟩
      exact ⟨Fin.lastCases fresh values, accepted⟩
    · rintro ⟨values, accepted⟩
      refine ⟨values (Fin.last count), (fun index => values index.castSucc), ?_⟩
      have same : Fin.lastCases (values (Fin.last count)) (fun index => values index.castSucc) = values := by
        funext index
        refine Fin.lastCases ?_ (fun _ => ?_) index <;> simp
      simpa only [same] using accepted

def atomFormula : Atom scopes α → Formula scopes α
  | .tyLe first last => .tyLe first last
  | .rowLe first last => .rowLe first (.fromPresence last)

theorem atom_exact (atom : Atom scopes α) (assignment : α → Computation) :
    (atomFormula atom).Holds assignment ↔ atom.Holds assignment := by
  cases atom <;> simp only [atomFormula, Formula.holds_tyLe, Formula.Holds,
    CommonEffectRequestGeneration.RowExpr.eval_fromPresence, Atom.Holds]

def matrix (clause : Clause scopes α) : Formula scopes (Fin clause.locals ⊕ α) :=
  CommonEffectUniversalArms.andAll (clause.atoms.map atomFormula)

theorem matrix_exact (clause : Clause scopes α) (assignment : Fin clause.locals ⊕ α → Computation) :
    (matrix clause).Holds assignment ↔ CommonEffectClauses.All assignment clause.atoms := by
  simp only [matrix, CommonEffectUniversalArms.andAll_exact, List.forall_mem_map, atom_exact, CommonEffectClauses.All]

def splitName : Fin count ⊕ α → CompTerm ((Fin count ⊕ α) ⊕ Fin count)
  | .inl index => ⟨.var (.inr index), .var (.inl (.inl index))⟩
  | .inr name => CompTerm.var (.inl (.inr name))

def split (clause : Clause scopes α) : Formula scopes ((Fin clause.locals ⊕ α) ⊕ Fin clause.locals) :=
  (matrix clause).subst splitName

theorem split_assignment (assignment : α → Computation) (values : Fin count → Computation) (types : Fin count → Ty) :
    (fun name => (splitName name).eval Common.model (localEnv (Sum.elim values assignment) types)) =
      Sum.elim (fun index => (types index, (values index).2)) assignment := by
  funext name
  cases name <;> rfl

theorem split_exact (clause : Clause scopes α) (assignment : α → Computation)
    (values : Fin clause.locals → Computation) (types : Fin clause.locals → Ty) :
    (split clause).Holds (localEnv (Sum.elim values assignment) types) ↔
      clause.Holds assignment (fun index => (types index, (values index).2)) := by
  rw [split, Formula.holds_subst, split_assignment]
  exact matrix_exact clause _

theorem clause_split_exact (clause : Clause scopes α) (assignment : α → Computation) :
    clause.Satisfiable assignment ↔ ∃ values : Fin clause.locals → Computation, ∃ types : Fin clause.locals → Ty,
      (split clause).Holds (localEnv (Sum.elim values assignment) types) := by
  constructor
  · rintro ⟨values, accepted⟩
    exact ⟨values, (fun index => (values index).1), (split_exact clause assignment values _).mpr accepted⟩
  · rintro ⟨values, types, accepted⟩
    exact ⟨(fun index => (types index, (values index).2)), (split_exact clause assignment values types).mp accepted⟩

def projectClause (clause : Clause scopes α) : Formula scopes α :=
  closeSlots clause.locals (CommonEffectBoundExtraction.eraseExists clause.locals
    (CommonEffectConstructorNormalisation.normalise (split clause)))

theorem projectClause_exact (clause : Clause scopes α) (assignment : α → Computation) :
    (projectClause clause).Holds assignment ↔ clause.Satisfiable assignment := by
  rw [projectClause, closeSlots_exact, clause_split_exact]
  apply exists_congr
  intro values
  exact (CommonEffectBoundExtraction.eraseExists_exact _ _).trans
    (exists_congr (fun types => CommonEffectConstructorNormalisation.normalise_exact (split clause) _))

def projectClauses : List (Clause scopes α) → Formula scopes α
  | [] => .core .bot
  | clause :: rest => .or (projectClause clause) (projectClauses rest)

theorem projectClauses_exact (clauses : List (Clause scopes α)) (assignment : α → Computation) :
    (projectClauses clauses).Holds assignment ↔ CommonEffectClauseNormalisation.Satisfiable assignment clauses := by
  induction clauses with
  | nil => simp [projectClauses, Formula.Holds, Core.PresenceGeneration.Formula.Holds, CommonEffectClauseNormalisation.Satisfiable]
  | cons clause rest ih =>
    simp only [projectClauses, Formula.Holds, projectClause_exact, ih,
      CommonEffectClauseNormalisation.Satisfiable, List.mem_cons, exists_eq_or_imp]

def closeMatrix (formula : Formula scopes α) : Formula scopes α :=
  match CommonEffectClauseNormalisation.normalise formula with
  | none => formula
  | some clauses => projectClauses clauses

theorem closeMatrix_exact (formula : Formula scopes α) (assignment : α → Computation) :
    (closeMatrix formula).Holds assignment ↔ formula.Holds assignment := by
  cases found : CommonEffectClauseNormalisation.normalise formula with
  | none => simp only [closeMatrix, found]
  | some clauses =>
    simp only [closeMatrix, found, projectClauses_exact]
    exact CommonEffectClauseNormalisation.normalise_exact formula clauses found assignment

/-- Traverses every original universal scope. A remaining universal never
moves across a captured computation witness or a neighboring scope. -/
def prepare : Formula scopes α → Formula scopes α
  | .core body => closeMatrix (.core body)
  | .rowLe first last => closeMatrix (.rowLe first last)
  | .and first last => closeMatrix (.and (prepare first) (prepare last))
  | .or first last => closeMatrix (.or (prepare first) (prepare last))
  | .existsSlot body => closeMatrix (.existsSlot (prepare body))
  | .existsTypes count body => closeMatrix (.existsTypes count (prepare body))
  | .forallTypes count body => .forallTypes count (prepare body)

theorem prepare_exact (formula : Formula scopes α) (assignment : α → Computation) :
    (prepare formula).Holds assignment ↔ formula.Holds assignment := by
  induction formula with
  | core | rowLe => exact closeMatrix_exact _ assignment
  | and first last iha ihb => exact (closeMatrix_exact _ assignment).trans (and_congr (iha assignment) (ihb assignment))
  | or first last iha ihb => exact (closeMatrix_exact _ assignment).trans (or_congr (iha assignment) (ihb assignment))
  | existsSlot body ih => exact (closeMatrix_exact _ assignment).trans (exists_congr (fun value => ih _))
  | existsTypes count body ih => exact (closeMatrix_exact _ assignment).trans (exists_congr (fun types => ih _))
  | forallTypes count body ih => exact forall_congr' (fun types => ih _)

end Yulang.CommonEffectClauseSplit
