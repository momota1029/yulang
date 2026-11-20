import Yulang.GeneralNominalPendingReindex304
import Yulang.GeneralNominalExamples

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 23000
set_option maxHeartbeats 6000000
namespace Yulang.GeneralNominalSlotSwapFixture304
open GeneralSourceState (Head equationAtoms equationAtoms_exact)
open GeneralNominalTotalLocation304 (status SlotStatus)
open GeneralNominalPendingReindex304 (pending)
open GeneralNominalRefinements (Refines)
open GeneralDictionaryBinderLocations (sourceSlot)

def pos (swap : Bool) (i : Fin 2) : Fin 2 := if swap then i.rev else i

theorem pos_inv (swap : Bool) (i : Fin 2) : pos swap (pos swap i) = i := by
  cases swap <;> simp [pos]

def move (a b : Bool) (i : Fin 2) : Fin 2 := pos b (pos a i)

def knownSlot (swap : Bool) : Fin 2 := pos swap 0

theorem move_known (a b : Bool) : move a b (knownSlot a) = knownSlot b := by
  simp [move,knownSlot,pos_inv]

theorem move_source (a b : Bool) (i : Fin 2) : pos b (move a b i) = pos a i :=
  pos_inv b _

theorem move_iff_known (a b : Bool) (i : Fin 2) : move a b i = knownSlot b ↔ i = knownSlot a := by
  constructor
  · intro h
    apply (show Function.Injective (pos a) from fun _ _ eq => by
      simpa only [pos_inv] using congrArg (pos a) eq)
    simpa [knownSlot,move,pos_inv] using congrArg (pos b) h
  · rintro rfl
    exact move_known a b

def shapes : Fin 0 → GeneralSourceState.Shape 2 := Fin.elim0

def startHead (swap : Bool) (i : Fin 2) : Head shapes :=
  if i = knownSlot swap then .scalar .int else .unresolved

abbrev sourceBase (swap : Bool) : GeneralSourceState.State where
  slots := 2
  source := fun i => (pos swap i).val
  source_injective := by
    intro i j h
    have eq : pos swap i = pos swap j := Fin.ext h
    simpa only [pos_inv] using congrArg (pos swap) eq
  rowSource := fun i => (pos swap i).val
  ordinary := equationAtoms (knownSlot swap) (.base .int)
  kinds := 0
  shapes := shapes
  shapes_injective := by intro i; exact Fin.elim0 i
  heads := startHead swap
  intervals := []
  heads_sound := by
    intro m valid i term exactHead
    by_cases same : i = knownSlot swap
    · subst i
      simp only [startHead,ite_true,Head.equation,Option.some.injEq] at exactHead
      cases exactHead
      exact (equationAtoms_exact ..).mp valid
    · simp [startHead,same,Head.equation] at exactHead
  intervals_sound := by intro _ _ _ impossible; cases impossible

def viewHead (swap : Bool) (i : Fin 2) : GeneralNormalizedObservation.Head Fin.elim0 2 :=
  if i = knownSlot swap then .scalar .int else .deferred .unresolved

abbrev snapshot (swap : Bool) : GeneralNominalState.State where
  base := sourceBase swap
  view := {
    kinds := 0
    shapes := Fin.elim0
    shapes_injective := by intro i; exact Fin.elim0 i
    canonical := by intro i; exact Fin.elim0 i
    heads := viewHead swap
    checked := by
      intro i term seen
      by_cases same : i = knownSlot swap
      · simp only [viewHead,same,ite_true,GeneralNormalizedObservation.Head.term,Option.some.injEq] at seen
        cases seen
        exact .head (by simp [sourceBase,startHead,same,Head.equation])
      · simp [viewHead,same,GeneralNormalizedObservation.Head.term,GeneralNormalizedObservation.Deferred.term] at seen
  }
  constructors := GeneralDeclarationExamples.constructors
  nominals := fun _ => none
  catalogue := by intro _ _ impossible; cases impossible
  bodies_opaque := by intro _ _ impossible; cases impossible
  seed := 1

theorem base_graph (a b : Bool) (i : Fin 2) :
    (sourceBase b).graph (move a b i) = (sourceBase a).graph i := by
  change (startHead b (move a b i)).node = (startHead a i).node
  simp [startHead,move_iff_known]

theorem view_graph (a b : Bool) (i : Fin 2) :
    (snapshot b).view.graph (move a b i) = (snapshot a).view.graph i := by
  change (viewHead b (move a b i)).node = (viewHead a i).node
  simp [viewHead,move_iff_known]

def refines (a b : Bool) : Refines (snapshot a) (snapshot b) where
  base := {
    embed := move a b
    source := fun i => congrArg Fin.val (move_source a b i)
    rowSource := fun i => congrArg Fin.val (move_source a b i)
    ordinary := by
      intro atom found
      change atom ∈ equationAtoms (knownSlot a) (.base .int) at found
      change atom.rename (move a b) ∈ equationAtoms (knownSlot b) (.base .int)
      simp only [equationAtoms,List.mem_cons,List.not_mem_nil,or_false] at found ⊢
      rcases found with rfl|rfl <;> simp [PresenceNormalForm.Atom.rename,Core.PresenceGeneration.TyTerm.rename,move_known]
    known := by intro i h; exact fun opposite => h ((base_graph a b i).symm.trans opposite)
    intervals := by intro _ impossible; cases impossible
  }
  heads := by
    intro i term seen
    change (startHead a i).equation = some term at seen
    by_cases h : i = knownSlot a
    · simp only [startHead,h,ite_true,Head.equation,Option.some.injEq] at seen
      cases seen
      apply GeneralNormalizedObservation.Rewrites.head
      have translated := (move_iff_known a b i).mpr h
      change (startHead b (move a b i)).equation = some (.base .int)
      simp [startHead,translated,Head.equation]
    · simp [startHead,h,Head.equation] at seen
  nominals := by intro _ _ impossible; cases impossible
  ordinary := by intro _ impossible; cases impossible
  known := by
    intro key known
    obtain ⟨i,source,head|⟨d,stored⟩⟩ := known
    · exact ⟨move a b i,(congrArg Fin.val (move_source a b i)).trans source,.inl
        (fun impossible => head ((view_graph a b i).symm.trans impossible))⟩
    · cases stored
  reserved := by intro _ impossible; cases impossible
  allocated := by intro _ impossible; cases impossible
  seed := rfl
  constructors := rfl

theorem concrete_source_changes_slots :
    sourceSlot (snapshot false).base 0 = some 0 ∧ sourceSlot (snapshot true).base 0 = some 1 := by
  constructor <;> apply (GeneralDictionaryBinderLocations.sourceSlot_exact ..).mpr <;> rfl

theorem status_values :
    status (snapshot true) 0 = .known ∧
    status (snapshot true) 1 = .unresolved ∧
    status (snapshot true) 2 = .missing := by decide

theorem statuses_survive_swap (id : Nat) : status (snapshot false) id = status (snapshot true) id :=
  GeneralNominalTotalLocation304.status_reindex (refines false true) (refines true false) id

end Yulang.GeneralNominalSlotSwapFixture304
