import Yulang.GeneralPresenceOrderedBlock247
import Yulang.GeneralPresenceGuardedAllocation247

/-! Initial allocation for arbitrary actual Presence RHSs and consumers.
Targets are reserved once above complete listed typed support and retained on
later refreshes; repeating this allocation on every refresh is not justified.
This does not claim coverage of unlisted journal/cache metadata or source
ownership. Private row-coordinate reads are harmless because all rows stay. -/
namespace Yulang.GeneralPresenceOrderedAllocation247
open Core.PresenceGeneration PresenceNormalForm
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOrderedBlock247
open GeneralPresenceUsedSupport245 (typedReads)
open GeneralPresenceConsumerSupport246
variable {Name : Type} [DecidableEq Name]

omit [DecidableEq Name] in
/-- A direct finite-index proof; no assumed target-uniqueness certificate. -/
theorem safe_finite (names : Fin size → Name) (terms : Fin size → TyTerm Name)
    (injective : Function.Injective names)
    (unread : ∀ first last, names first ∉ typedReads (terms last)) :
    SafeOrder (List.ofFn (fun index => (names index,terms index))) := by
  induction size with
  | zero => simp [SafeOrder]
  | succ size ih =>
    rw [List.ofFn_succ]
    refine ⟨unread 0 0,?_,?_,?_⟩
    · intro entry member
      obtain ⟨index,rfl⟩ := List.mem_ofFn.mp member
      intro same
      have equal := congrArg Fin.val (injective same)
      simp at equal
    · intro entry member
      obtain ⟨index,rfl⟩ := List.mem_ofFn.mp member
      exact unread index.succ 0
    · apply ih (fun index => names index.succ) (fun index => terms index.succ)
      · intro first last same
        exact Fin.succ_inj.mp (injective same)
      · intro first last
        exact unread first.succ last.succ

def support (terms : Fin size → TyTerm Nat) (consumers : List (Atom Nat)) (extraKnown : List Nat) : List Nat :=
  extraKnown ++ ((List.ofFn terms).flatMap typedReads ++ listTypedReads consumers)

def entries (terms : Fin size → TyTerm Nat) (consumers : List (Atom Nat)) (extraKnown : List Nat) : List (Entry Nat) :=
  List.ofFn (fun index => (GeneralPresenceGuardedAllocation247.targets (support terms consumers extraKnown) index,terms index))

theorem rhs_support (terms : Fin size → TyTerm Nat) (consumers : List (Atom Nat))
    (extraKnown : List Nat) (index : Fin size) (name : Nat) (member : name ∈ typedReads (terms index)) :
    name ∈ support terms consumers extraKnown :=
  List.mem_append_right _ (List.mem_append_left _
    (List.mem_flatMap.mpr ⟨terms index,List.mem_ofFn.mpr ⟨index,rfl⟩,member⟩))

theorem consumer_support (terms : Fin size → TyTerm Nat) (consumers : List (Atom Nat))
    (extraKnown : List Nat) (name : Nat) (member : name ∈ listTypedReads consumers) :
    name ∈ support terms consumers extraKnown :=
  List.mem_append_right _ (List.mem_append_right _ member)

theorem safe_entries (terms : Fin size → TyTerm Nat) (consumers : List (Atom Nat)) (extraKnown : List Nat) :
    SafeOrder (entries terms consumers extraKnown) := by
  apply safe_finite _ terms (GeneralPresenceGuardedAllocation247.targets_injective _)
  intro first last member
  exact GeneralPresenceGuardedAllocation247.target_not_support _ first _
    (rhs_support terms consumers extraKnown last _ member) rfl

theorem target_outside_support (terms : Fin size → TyTerm Nat) (consumers : List (Atom Nat))
    (extraKnown : List Nat) (name : Nat) (member : name ∈ support terms consumers extraKnown) :
    ∀ entry ∈ entries terms consumers extraKnown, entry.1 ≠ name := by
  intro entry present
  obtain ⟨index,rfl⟩ := List.mem_ofFn.mp present
  exact GeneralPresenceGuardedAllocation247.target_not_support _ index name member

theorem initial_add_definitions (model : Model) (refl : ∀ value, model.subTy value value)
    (terms : Fin size → TyTerm Nat) (consumers : List (Atom Nat)) (extraKnown : List Nat)
    (boundary : Nat → Comp model) :
    All model boundary consumers ↔
      ∃ assignment, All model assignment (consumers ++ block (entries terms consumers extraKnown)) ∧
        (∀ name ∈ support terms consumers extraKnown, assignment name = boundary name) ∧
        (∀ name, (assignment name).2 = (boundary name).2) := by
  constructor
  · intro valid
    let assignment := solve model (entries terms consumers extraKnown) boundary
    have kept : ∀ name ∈ support terms consumers extraKnown, assignment name = boundary name :=
      fun name member => solve_outside model _ boundary name (target_outside_support terms consumers extraKnown name member)
    have rows : ∀ name, (assignment name).2 = (boundary name).2 := solve_rows model _ boundary
    refine ⟨assignment,?_,kept,rows⟩
    apply (all_append model assignment _ _).mpr
    refine ⟨?_,block_satisfied model refl _ (safe_entries terms consumers extraKnown) boundary⟩
    apply (GeneralPresenceConsumerSupport246.all_iff model assignment boundary rows consumers ?_).mpr valid
    intro name member
    exact congrArg Prod.fst (kept name (consumer_support terms consumers extraKnown name member))
  · rintro ⟨assignment,valid,kept,rows⟩
    have consumersValid := ((all_append model assignment _ _).mp valid).1
    apply (GeneralPresenceConsumerSupport246.all_iff model assignment boundary rows consumers ?_).mp consumersValid
    intro name member
    exact congrArg Prod.fst (kept name (consumer_support terms consumers extraKnown name member))

end Yulang.GeneralPresenceOrderedAllocation247
