import Yulang.GeneralPresenceConsumerSupport246
import Yulang.GeneralPresenceDefinitionRewrite244

/-! Constructive evaluation of a topologically ordered actual Presence block.
Later right-hand sides may read already written targets. Earlier right-hand
sides and targets cannot be changed by later writes. Only typed reads matter;
rows at every name are unchanged. A source ordering producer remains separate. -/
namespace Yulang.GeneralPresenceOrderedBlock247
open Core.PresenceGeneration PresenceNormalForm
open GeneralPresenceDefinitionRewrite244
open GeneralPresenceUsedSupport245 (typedReads)
variable {Name : Type} [DecidableEq Name]

def put (model : Model) (assignment : Name → Comp model) (target : Name)
    (value : model.Ty) (name : Name) : Comp model :=
  if name = target then (value,(assignment name).2) else assignment name

def solve (model : Model) : List (Entry Name) → (Name → Comp model) → Name → Comp model
  | [], assignment => assignment
  | entry :: rest, assignment =>
      solve model rest (put model assignment entry.1 (entry.2.eval model assignment))

def SafeOrder : List (Entry Name) → Prop
  | [] => True
  | entry :: rest =>
      entry.1 ∉ typedReads entry.2 ∧
      (∀ later ∈ rest, later.1 ≠ entry.1) ∧
      (∀ later ∈ rest, later.1 ∉ typedReads entry.2) ∧ SafeOrder rest

theorem put_rows (model : Model) (assignment : Name → Comp model) (target : Name)
    (value : model.Ty) (name : Name) :
    (put model assignment target value name).2 = (assignment name).2 := by
  simp only [put]
  split <;> rfl

theorem put_outside (model : Model) (assignment : Name → Comp model) (target : Name)
    (value : model.Ty) (name : Name) (outside : target ≠ name) :
    put model assignment target value name = assignment name := by
  simp [put,Ne.symm outside]

theorem solve_rows (model : Model) (entries : List (Entry Name))
    (assignment : Name → Comp model) (name : Name) :
    (solve model entries assignment name).2 = (assignment name).2 := by
  induction entries generalizing assignment with
  | nil => rfl
  | cons entry rest ih =>
    exact (ih _).trans (put_rows model assignment entry.1 _ name)

theorem solve_outside (model : Model) (entries : List (Entry Name))
    (assignment : Name → Comp model) (name : Name)
    (outside : ∀ entry ∈ entries, entry.1 ≠ name) :
    solve model entries assignment name = assignment name := by
  induction entries generalizing assignment with
  | nil => rfl
  | cons entry rest ih =>
    change solve model rest (put model assignment entry.1 _) name = assignment name
    rw [ih _ (fun later member => outside later (List.mem_cons_of_mem _ member))]
    exact put_outside model assignment entry.1 _ name (outside entry (by simp))

theorem block_satisfied (model : Model) (refl : ∀ value, model.subTy value value)
    (entries : List (Entry Name)) (safe : SafeOrder entries)
    (assignment : Name → Comp model) :
    All model (solve model entries assignment) (block entries) := by
  induction entries generalizing assignment with
  | nil => simp [block,All]
  | cons entry rest ih =>
    obtain ⟨noSelf,distinct,unread,tailSafe⟩ := safe
    have fixed : entry.2.eval model (solve model (entry :: rest) assignment) =
        entry.2.eval model assignment := by
      apply GeneralPresenceConsumerSupport246.type_eval_equal model _ assignment
        (solve_rows model (entry :: rest) assignment) entry.2
      intro name member
      apply congrArg Prod.fst (solve_outside model (entry :: rest) assignment name ?_)
      intro later present same
      rcases List.mem_cons.mp present with rfl | present
      · exact noSelf (same ▸ member)
      · exact unread later present (same ▸ member)
    have targetValue : (solve model (entry :: rest) assignment entry.1).1 =
        entry.2.eval model assignment := by
      change (solve model rest (put model assignment entry.1 _) entry.1).1 = _
      rw [solve_outside model rest _ entry.1 distinct]
      simp [put]
    change All model (solve model (entry :: rest) assignment) (equations entry.1 entry.2 ++ block rest)
    apply (all_append model _ _ _).mpr
    constructor
    · intro atom member
      simp only [equations,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl
      · change model.subTy (solve model (entry :: rest) assignment entry.1).1
          (entry.2.eval model (solve model (entry :: rest) assignment))
        rw [targetValue,fixed]
        exact refl _
      · change model.subTy (entry.2.eval model (solve model (entry :: rest) assignment))
          (solve model (entry :: rest) assignment entry.1).1
        rw [targetValue,fixed]
        exact refl _
    · exact ih tailSafe (put model assignment entry.1 (entry.2.eval model assignment))

theorem arbitrary_public_model (model : Model) (refl : ∀ value, model.subTy value value)
    (entries : List (Entry Name)) (safe : SafeOrder entries)
    (boundary : Name → Comp model) :
    ∃ assignment, All model assignment (block entries) ∧
      (∀ name, (∀ entry ∈ entries, entry.1 ≠ name) → assignment name = boundary name) ∧
      (∀ name, (assignment name).2 = (boundary name).2) :=
  ⟨solve model entries boundary,block_satisfied model refl entries safe boundary,
    solve_outside model entries boundary,solve_rows model entries boundary⟩

end Yulang.GeneralPresenceOrderedBlock247
