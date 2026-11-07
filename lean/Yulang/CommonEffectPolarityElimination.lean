import Yulang.CommonEffectPolarity

/-! A terminating finite search for syntactic local polarities, followed by
exact extremal elimination. Failure retains the universal syntax; it is not
reported as a solved scheme or shifted onto instantiation parameters. -/
namespace Yulang.CommonEffectPolarityElimination
open CommonEffectFormula
open CommonEffectRequestGeneration (Computation)
open CommonEffectPolarity

variable {scopes : Nat}

def prepend (bit : Bool) (tail : Fin count → Bool) : Fin (count + 1) → Bool := Fin.cases bit tail

def directionsList : (count : Nat) → List (Fin count → Bool)
  | 0 => [Fin.elim0]
  | count + 1 => (directionsList count).flatMap fun tail =>
      [prepend false tail, prepend true tail]

theorem directionsList_complete (directions : Fin count → Bool) : directions ∈ directionsList count := by
  induction count with
  | zero =>
    have same : directions = Fin.elim0 := by funext index; exact Fin.elim0 index
    simp [directionsList, same]
  | succ count ih =>
    let tail : Fin count → Bool := fun index => directions index.succ
    have member := ih tail
    have same : prepend (directions 0) tail = directions := by
      funext index
      exact Fin.cases rfl (fun _ => rfl) index
    apply List.mem_flatMap.mpr
    refine ⟨tail, member, ?_⟩
    have bit : prepend (directions 0) tail ∈ [prepend false tail, prepend true tail] := by
      cases directions 0 <;> simp
    exact same ▸ bit

def select (formula : Formula scopes (α ⊕ Fin count)) : Option (Fin count → Bool) :=
  (directionsList count).find? (fun directions => goodFormula (localsOrientation directions) formula)

theorem select_sound (formula : Formula scopes (α ⊕ Fin count)) (directions : Fin count → Bool)
    (selected : select formula = some directions) :
    goodFormula (localsOrientation directions) formula = true :=
  List.find?_some (p := fun chosen => goodFormula (localsOrientation chosen) formula) selected

theorem select_complete (formula : Formula scopes (α ⊕ Fin count)) :
    (select formula).isSome = true ↔
      ∃ directions : Fin count → Bool, goodFormula (localsOrientation directions) formula = true := by
  simp only [select, List.find?_isSome]
  exact ⟨fun ⟨directions, _, good⟩ => ⟨directions, good⟩,
    fun ⟨directions, good⟩ => ⟨directions, directionsList_complete directions, good⟩⟩

def eraseForall (formula : Formula scopes (α ⊕ Fin count)) : Formula scopes α :=
  match select formula with
  | none => .forallTypes count formula
  | some directions => formula.subst (extremalSubstitution directions)

theorem eraseForall_exact (formula : Formula scopes (α ⊕ Fin count)) (assignment : α → Computation) :
    (eraseForall formula).Holds assignment ↔ (Formula.forallTypes count formula).Holds assignment := by
  cases selected : select formula with
  | none => simp only [eraseForall, selected]
  | some directions =>
    simp only [eraseForall, selected]
    exact forall_extremal_exact formula directions (select_sound formula directions selected) assignment

def eliminate : Formula scopes α → Formula scopes α
  | .core body => .core body
  | .rowLe first last => .rowLe first last
  | .and first last => .and (eliminate first) (eliminate last)
  | .or first last => .or (eliminate first) (eliminate last)
  | .existsSlot body => .existsSlot (eliminate body)
  | .existsTypes count body => .existsTypes count (eliminate body)
  | .forallTypes _ body => eraseForall (eliminate body)

/-- Every finite formula and assignment, including nested coupled existential
value/row witnesses. The pass has no semantic success premise. -/
theorem eliminate_exact (formula : Formula scopes α) (assignment : α → Computation) :
    (eliminate formula).Holds assignment ↔ formula.Holds assignment := by
  induction formula with
  | core | rowLe => rfl
  | and a b iha ihb => exact and_congr (iha assignment) (ihb assignment)
  | or a b iha ihb => exact or_congr (iha assignment) (ihb assignment)
  | existsSlot body ih => exact exists_congr (fun value => ih _)
  | existsTypes count body ih => exact exists_congr (fun types => ih _)
  | forallTypes count body ih =>
    exact (eraseForall_exact (eliminate body) assignment).trans (forall_congr' (fun types => ih _))

theorem selected_binder_removed (formula : Formula scopes (α ⊕ Fin count))
    (directions : Fin count → Bool) (selected : select formula = some directions) :
    CommonEffectRowQuantifiers.typeBinders (eraseForall formula) =
      CommonEffectRowQuantifiers.typeBinders formula := by
  simp only [eraseForall, selected, CommonEffectRowQuantifiers.typeBinders_subst]
end Yulang.CommonEffectPolarityElimination
