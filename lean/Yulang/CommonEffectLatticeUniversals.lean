import Yulang.CommonEffectBoundTemplates
import Yulang.CommonEffectPolarityElimination

/-! Complete corner elimination for conjunctive lattice-polynomial local
type comparisons, including mixed local polarities. Captured whole types are
fixed leaves. Locals below other constructors stay unsupported. Corners are
the actual finite Boolean tuple list, not a universal parameter condition. -/
namespace Yulang.CommonEffectLatticeUniversals
open Common (Ty Row)
open Core.PresenceGeneration (TyTerm)
open CommonEffectRequestGeneration (Computation localEnv)
open CommonEffectFormula (Formula)
open CommonEffectPolarity (extremalTypes extremalSubstitution)
open CommonEffectPolarityElimination (directionsList directionsList_complete)

variable {scopes count : Nat}

def Read (depth rank : Nat) (environment : CommonFinite.Environment Row) (observation : CommonFinite.Observation Row) (type : Ty) : Prop :=
  CommonFinite.ProbeAt Common.rowLe rank environment (Common.observeTy depth type) observation

theorem read_union (depth rank : Nat) (environment : CommonFinite.Environment Row) (observation : CommonFinite.Observation Row) (first last : Ty) :
    Read depth rank environment observation (.union first last) ↔
      Read depth rank environment observation first ∧ Read depth rank environment observation last :=
  CommonFinite.probeAt_union rank _ _ observation

theorem read_inter (depth rank : Nat) (environment : CommonFinite.Environment Row) (observation : CommonFinite.Observation Row) (first last : Ty) :
    Read depth rank environment observation (.inter first last) ↔
      Read depth rank environment observation first ∨ Read depth rank environment observation last :=
  CommonFinite.probeAt_inter rank _ _ observation

theorem read_bottom (depth rank : Nat) (environment : CommonFinite.Environment Row) (observation : CommonFinite.Observation Row) :
    Read depth rank environment observation .bottom := CommonFinite.probeAt_bottom rank observation

theorem read_top_implies (depth rank : Nat) (environment : CommonFinite.Environment Row) (observation : CommonFinite.Observation Row) (type : Ty) :
    Read depth rank environment observation .top → Read depth rank environment observation type :=
  (CommonFinite.producerLe_iff_probe _ _).mp (CommonEffectTypeNormalisation.subtype_top type depth) rank environment observation

def lattice : TyTerm (α ⊕ Fin count) → Bool
  | .var _ => true
  | .union first last | .inter first last => lattice first && lattice last
  | term => CommonEffectBoundExtraction.rigid term

theorem term_read_congr (term : TyTerm (α ⊕ Fin count)) (good : lattice term = true)
    (assignment : α → Computation) (first last : Fin count → Ty)
    (depth rank : Nat) (environment : CommonFinite.Environment Row) (observation : CommonFinite.Observation Row)
    (same : ∀ index, Read depth rank environment observation (first index) ↔ Read depth rank environment observation (last index)) :
    Read depth rank environment observation (term.eval Common.model (localEnv assignment first)) ↔
      Read depth rank environment observation (term.eval Common.model (localEnv assignment last)) := by
  induction term with
  | var name =>
    cases name with
    | inl name => rfl
    | inr index => exact same index
  | union a b iha ihb =>
    have both := Bool.and_eq_true_iff.mp good
    exact (read_union depth rank environment observation _ _).trans
      ((and_congr (iha both.1) (ihb both.2)).trans (read_union depth rank environment observation _ _).symm)
  | inter a b iha ihb =>
    have both := Bool.and_eq_true_iff.mp good
    exact (read_inter depth rank environment observation _ _).trans
      ((or_congr (iha both.1) (ihb both.2)).trans (read_inter depth rank environment observation _ _).symm)
  | _ =>
    rw [CommonEffectBoundExtraction.rigid_value_irrelevant _ assignment first last good]

/-- This classical choice occurs only in the proof for ONE observation.
The algorithm below enumerates every Boolean tuple without inspecting types. -/
theorem corner_read (types : Fin count → Ty) (depth rank : Nat) (environment : CommonFinite.Environment Row)
    (observation : CommonFinite.Observation Row) :
    ∃ directions : Fin count → Bool, ∀ index,
      Read depth rank environment observation (extremalTypes directions index) ↔ Read depth rank environment observation (types index) := by
  classical
  let directions : Fin count → Bool := fun index => if Read depth rank environment observation (types index) then true else false
  refine ⟨directions, ?_⟩
  intro index
  by_cases present : Read depth rank environment observation (types index)
  · have selected : directions index = true := ite_eq_left present
    simp only [extremalTypes, selected, ↓reduceIte]
    exact iff_of_true (read_bottom depth rank environment observation) present
  · have selected : directions index = false := ite_eq_right present
    simp only [extremalTypes, selected, Bool.false_eq_true, ↓reduceIte]
    exact iff_of_false (fun accepted => present (read_top_implies depth rank environment observation _ accepted)) present

theorem comparison_corners_exact (source target : TyTerm (α ⊕ Fin count))
    (sourceGood : lattice source = true) (targetGood : lattice target = true) (assignment : α → Computation) :
    (∀ directions : Fin count → Bool,
      Common.Subtype (source.eval Common.model (localEnv assignment (extremalTypes directions)))
        (target.eval Common.model (localEnv assignment (extremalTypes directions)))) ↔
    ∀ types : Fin count → Ty,
      Common.Subtype (source.eval Common.model (localEnv assignment types)) (target.eval Common.model (localEnv assignment types)) := by
  constructor
  · intro allCorners types depth
    apply (CommonFinite.producerLe_iff_probe _ _).mpr
    intro rank environment observation accepted
    obtain ⟨directions, same⟩ := corner_read types depth rank environment observation
    have sourceSame := term_read_congr source sourceGood assignment (extremalTypes directions) types depth rank environment observation same
    have targetSame := term_read_congr target targetGood assignment (extremalTypes directions) types depth rank environment observation same
    exact sourceSame.mp ((CommonFinite.producerLe_iff_probe _ _).mp (allCorners directions depth) rank environment observation (targetSame.mpr accepted))
  · intro allTypes directions
    exact allTypes (extremalTypes directions)

def goodCore : Core.PresenceGeneration.Formula (α ⊕ Fin count) → Bool
  | .top | .bot | .rowLe _ _ => true
  | .tyLe source target => lattice source && lattice target
  | .and first last => goodCore first && goodCore last
  | .or _ _ | .existsSlot _ => false

theorem core_corners_all (formula : Core.PresenceGeneration.Formula (α ⊕ Fin count)) (good : goodCore formula = true)
    (assignment : α → Computation)
    (corners : ∀ directions : Fin count → Bool, formula.Holds Common.model (localEnv assignment (extremalTypes directions))) :
    ∀ types : Fin count → Ty, formula.Holds Common.model (localEnv assignment types) := by
  cases formula with
  | top => intro _; trivial
  | bot => exact False.elim (corners (fun _ => false))
  | tyLe source target =>
    simp only [goodCore] at good
    have both := Bool.and_eq_true_iff.mp good
    exact (comparison_corners_exact source target both.1 both.2 assignment).mp corners
  | rowLe source target =>
    intro types
    have sameRows : ∀ name, (localEnv assignment types name).2 =
        (localEnv assignment (extremalTypes (fun _ => false)) name).2 := by intro name; cases name <;> rfl
    exact (Iff.of_eq (congr (congrArg Common.rowLe
      (CommonEffectRowQuantifiers.rowTerm_congr source _ _ sameRows))
      (CommonEffectRowQuantifiers.rowTerm_congr target _ _ sameRows))).mpr (corners (fun _ => false))
  | and first last =>
    simp only [goodCore] at good
    have both := Bool.and_eq_true_iff.mp good
    intro types
    exact ⟨core_corners_all first both.1 assignment (fun directions => (corners directions).1) types,
      core_corners_all last both.2 assignment (fun directions => (corners directions).2) types⟩
  | or | existsSlot => simp [goodCore] at good
termination_by sizeOf formula

def good : Formula scopes (α ⊕ Fin count) → Bool
  | .core body => goodCore body
  | .rowLe _ _ => true
  | .and first last => good first && good last
  | .or _ _ | .existsSlot _ | .existsTypes _ _ | .forallTypes _ _ => false

theorem corners_all (formula : Formula scopes (α ⊕ Fin count)) (checked : good formula = true)
    (assignment : α → Computation)
    (corners : ∀ directions : Fin count → Bool, formula.Holds (localEnv assignment (extremalTypes directions))) :
    ∀ types : Fin count → Ty, formula.Holds (localEnv assignment types) := by
  cases formula with
  | core body => exact core_corners_all body (by simpa only [good] using checked) assignment corners
  | rowLe source target =>
    intro types
    exact (CommonEffectRowQuantifiers.type_assignment_irrelevant (.rowLe source target) rfl assignment types).mpr
      (corners (fun _ => false))
  | and first last =>
    simp only [good] at checked
    have both := Bool.and_eq_true_iff.mp checked
    intro types
    exact ⟨corners_all first both.1 assignment (fun directions => (corners directions).1) types,
      corners_all last both.2 assignment (fun directions => (corners directions).2) types⟩
  | or | existsSlot | existsTypes | forallTypes => simp [good] at checked
termination_by sizeOf formula

def cornerFormula (formula : Formula scopes (α ⊕ Fin count)) : Formula scopes α :=
  CommonEffectUniversalArms.andAll ((directionsList count).map (fun directions => formula.subst (extremalSubstitution directions)))

theorem cornerFormula_exact (formula : Formula scopes (α ⊕ Fin count)) (checked : good formula = true)
    (assignment : α → Computation) :
    (cornerFormula formula).Holds assignment ↔ (Formula.forallTypes count formula).Holds assignment := by
  simp only [cornerFormula, CommonEffectUniversalArms.andAll_exact, List.forall_mem_map,
    Formula.holds_subst, CommonEffectPolarity.extremalSubstitution_eval, Formula.Holds]
  constructor
  · intro accepted
    exact corners_all formula checked assignment (fun directions => accepted directions (directionsList_complete directions))
  · intro accepted directions _
    exact accepted (extremalTypes directions)

def eraseForall (formula : Formula scopes (α ⊕ Fin count)) : Formula scopes α :=
  if good formula then cornerFormula formula else .forallTypes count formula

theorem eraseForall_exact (formula : Formula scopes (α ⊕ Fin count)) (assignment : α → Computation) :
    (eraseForall formula).Holds assignment ↔ (Formula.forallTypes count formula).Holds assignment := by
  cases checked : good formula with
  | false => simp only [eraseForall, checked, Bool.false_eq_true, ↓reduceIte]
  | true => simpa only [eraseForall, checked, ↓reduceIte] using cornerFormula_exact formula checked assignment

def eliminate : Formula scopes α → Formula scopes α
  | .core body => .core body
  | .rowLe first last => .rowLe first last
  | .and first last => .and (eliminate first) (eliminate last)
  | .or first last => .or (eliminate first) (eliminate last)
  | .existsSlot body => .existsSlot (eliminate body)
  | .existsTypes count body => .existsTypes count (eliminate body)
  | .forallTypes _ body => eraseForall (eliminate body)

theorem eliminate_exact (formula : Formula scopes α) (assignment : α → Computation) :
    (eliminate formula).Holds assignment ↔ formula.Holds assignment := by
  induction formula with
  | core | rowLe => rfl
  | and first last iha ihb => exact and_congr (iha assignment) (ihb assignment)
  | or first last iha ihb => exact or_congr (iha assignment) (ihb assignment)
  | existsSlot body ih => exact exists_congr (fun value => ih _)
  | existsTypes count body ih => exact exists_congr (fun types => ih _)
  | forallTypes count body ih => exact (eraseForall_exact (eliminate body) assignment).trans (forall_congr' (fun types => ih _))

end Yulang.CommonEffectLatticeUniversals
