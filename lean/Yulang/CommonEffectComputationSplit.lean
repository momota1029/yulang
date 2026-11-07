import Yulang.CommonEffectBoundExtraction

/-! Exact separation of a computation existential into its arbitrary row and
a pure type existential. The old row slot is retained literally. This is a
truth-preserving projection; arbitrary eliminated witness valuations are not
claimed recovered by the canonical templates used in later preprocessing. -/
namespace Yulang.CommonEffectComputationSplit
open Common (Ty Row)
open Core.PresenceGeneration (CompTerm extend)
open CommonEffectRequestGeneration (Computation localEnv)
open CommonEffectFormula (Formula)

variable {scopes : Nat}

def splitName : Option α → CompTerm (Option α ⊕ Fin 1)
  | none => ⟨.var (.inr 0), .var (.inl none)⟩
  | some name => CompTerm.var (.inl (some name))

def split (body : Formula scopes (Option α)) : Formula scopes (Option α ⊕ Fin 1) :=
  body.subst splitName

theorem split_assignment (assignment : α → Computation) (fresh : Computation) (types : Fin 1 → Ty) :
    (fun name => (splitName name).eval Common.model (localEnv (extend assignment fresh) types)) =
      extend assignment (types 0, fresh.2) := by
  funext name
  cases name <;> rfl

theorem split_exact (body : Formula scopes (Option α)) (assignment : α → Computation)
    (fresh : Computation) (types : Fin 1 → Ty) :
    (split body).Holds (localEnv (extend assignment fresh) types) ↔ body.Holds (extend assignment (types 0, fresh.2)) := by
  simp only [split, Formula.holds_subst, split_assignment]

theorem split_fresh_type_irrelevant (body : Formula scopes (Option α)) (assignment : α → Computation)
    (first last : Computation) (sameRow : first.2 = last.2) (types : Fin 1 → Ty) :
    (split body).Holds (localEnv (extend assignment first) types) ↔
      (split body).Holds (localEnv (extend assignment last) types) := by
  rw [split_exact, split_exact, sameRow]

/-- Both sides allow arbitrary Common rows, including infinite sets and
all signed coordinate lengths. Outer captures are identical on both sides. -/
theorem exists_split_exact (body : Formula scopes (Option α)) (assignment : α → Computation) :
    (Formula.existsSlot (.existsTypes 1 (split body))).Holds assignment ↔ (Formula.existsSlot body).Holds assignment := by
  change (∃ fresh, ∃ types, _) ↔ ∃ fresh, _
  constructor
  · rintro ⟨fresh, types, accepted⟩
    exact ⟨(types 0, fresh.2), (split_exact body assignment fresh types).mp accepted⟩
  · rintro ⟨fresh, accepted⟩
    exact ⟨fresh, (fun _ => fresh.1), (split_exact body assignment fresh (fun _ => fresh.1)).mpr accepted⟩

/-- One real projection step: the new pure type binder is removed only when
the actual finite flat-bound extractor succeeds. Its row slot stays scoped. -/
def projectSlot (body : Formula scopes (Option α)) : Formula scopes α :=
  .existsSlot (CommonEffectBoundExtraction.eraseExists 1 (split body))

theorem projectSlot_exact (body : Formula scopes (Option α)) (assignment : α → Computation) :
    (projectSlot body).Holds assignment ↔ (Formula.existsSlot body).Holds assignment := by
  apply Iff.trans ?_ (exists_split_exact body assignment)
  exact exists_congr (fun fresh => CommonEffectBoundExtraction.eraseExists_exact (split body) (extend assignment fresh))

def project : Formula scopes α → Formula scopes α
  | .core body => .core body
  | .rowLe first last => .rowLe first last
  | .and first last => .and (project first) (project last)
  | .or first last => .or (project first) (project last)
  | .existsSlot body => projectSlot (project body)
  | .existsTypes count body => .existsTypes count (project body)
  | .forallTypes count body => .forallTypes count (project body)

theorem project_exact (formula : Formula scopes α) (assignment : α → Computation) :
    (project formula).Holds assignment ↔ formula.Holds assignment := by
  induction formula with
  | core | rowLe => rfl
  | and first last iha ihb => exact and_congr (iha assignment) (ihb assignment)
  | or first last iha ihb => exact or_congr (iha assignment) (ihb assignment)
  | existsSlot body ih => exact (projectSlot_exact (project body) assignment).trans (exists_congr (fun value => ih _))
  | existsTypes count body ih => exact exists_congr (fun types => ih _)
  | forallTypes count body ih => exact forall_congr' (fun types => ih _)

end Yulang.CommonEffectComputationSplit
