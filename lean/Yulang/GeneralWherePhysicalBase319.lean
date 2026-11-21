import Yulang.GeneralWherePhysicalIndex319

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16000
set_option maxHeartbeats 7500000
namespace Yulang.GeneralWherePhysicalBase319
open GeneralSourceState (State Head)
open GeneralWherePhysicalIndex319 (old new shape head head_rename_term join_injective)
open GeneralNominalCommonBridge (Assignment assignment Models)
open Core.PresenceGeneration (TyTerm)
open PresenceNormalForm (Atom All all_append all_rename)

/-- Appended identifiers and explicitly checked renamed shape indices.
The latter permits useful closed finite base layouts without assuming
injectivity of an arbitrary supplied shape table. -/
structure Layout (b : State) (count : Nat) where
  ids : Fin count → Nat
  distinct : Function.Injective ids
  no_overlap : ∀ i j, b.source i ≠ ids j
  shape_indices : Function.Injective (shape (old (m := b.slots) count) ∘ b.shapes)

def source (l : Layout b n) : Fin (b.slots+n) → Nat :=
  Fin.addCases b.source l.ids
def rowSource (l : Layout b n) : Fin (b.slots+n) → Nat :=
  Fin.addCases b.rowSource l.ids
def heads (_l : Layout b n) : Fin (b.slots+n) → Head (shape (old n) ∘ b.shapes) :=
  Fin.addCases (fun i => head (old n) (b.heads i)) (fun _ => .unresolved)

@[simp] theorem source_old (l : Layout b n) (i) : source l (old n i) = b.source i := Fin.addCases_left ..
@[simp] theorem source_new (l : Layout b n) (i) : source l (new b.slots i) = l.ids i := Fin.addCases_right ..
@[simp] theorem row_old (l : Layout b n) (i) : rowSource l (old n i) = b.rowSource i := Fin.addCases_left ..
@[simp] theorem head_old (l : Layout b n) (i) :
    (heads l (old n i)).equation = (b.heads i).equation.map (fun t => t.rename (old n)) := by
  unfold heads
  rw [Fin.addCases_left]
  exact head_rename_term _ _
@[simp] theorem head_new (l : Layout b n) (i) : (heads l (new b.slots i)).equation = none := by
  simp [heads,new,GeneralSourceState.Head.equation]

def expand (l : Layout b n) (extra : List (Atom (Fin (b.slots+n)))) : State where
  slots := b.slots+n
  source := source l
  source_injective := join_injective b.source_injective l.distinct l.no_overlap
  rowSource := rowSource l
  ordinary := b.ordinary.map (Atom.rename (old n)) ++ extra
  kinds := b.kinds
  shapes := shape (old n) ∘ b.shapes
  shapes_injective := l.shape_indices
  heads := heads l
  intervals := b.intervals.map (fun ab => (old n ab.1,old n ab.2))
  heads_sound := by
    intro asg modeled i term found
    have prior := (all_rename ..).mp ((all_append ..).mp modeled).1
    refine Fin.addCases (fun j h => ?_) (fun j h => ?_) i found
    · rw [head_old] at h
      cases idx : (b.heads j).equation with
      | none => simp [idx] at h
      | some t =>
        rw [idx] at h
        have same : t.rename (old n) = term := Option.some.inj h
        subst term
        rw [TyTerm.eval_rename]
        exact b.heads_sound (asg ∘ old n) prior j t idx
    · rw [head_new] at h
      cases h
  intervals_sound := by
    intro asg modeled pair found
    have prior := (all_rename ..).mp ((all_append ..).mp modeled).1
    obtain ⟨q,member,rfl⟩ := List.mem_map.mp found
    exact b.intervals_sound (asg ∘ old n) prior q member

theorem assignment_old (l : Layout b n) (extra) (m : Assignment) :
    assignment (expand l extra) m ∘ old n = assignment b m := by
  funext j
  change ((m (source l (old n j))).1,(m (rowSource l (old n j))).2) =
    ((m (b.source j)).1,(m (b.rowSource j)).2)
  rw [source_old,row_old]

theorem base_models (l : Layout b n) (extra : List (Atom (Fin (b.slots+n)))) (m : Assignment) :
    Models (expand l extra) m ↔ Models b m ∧ All CommonNominalFullCarrier.model (assignment (expand l extra) m) extra := by
  constructor
  · intro facts
    have atoms := (all_append ..).mp facts.1
    have oldAtoms := (all_rename ..).mp atoms.1
    rw [assignment_old] at oldAtoms
    refine ⟨⟨oldAtoms,?_,?_⟩,atoms.2⟩
    · intro i t found
      have h : ((expand l extra).heads (old n i)).equation = some (t.rename (old n)) := by
        change (heads l (old n i)).equation = _
        rw [head_old,found]; rfl
      have modeled := facts.2.1 (old n i) (t.rename (old n)) h
      change CommonNominalFullCarrier.Equivalent (m (source l (old n i))).1 _ at modeled
      rw [source_old,TyTerm.eval_rename,assignment_old] at modeled
      exact modeled
    · intro pair member
      have located := facts.2.2 (old n pair.1,old n pair.2) (List.mem_map.mpr ⟨pair,member,rfl⟩)
      change CommonNominalFullCarrier.Subtype (m (source l (old n pair.1))).1 (m (source l (old n pair.2))).1 at located
      rwa [source_old,source_old] at located
  · rintro ⟨oldModel,extraModel⟩
    refine ⟨(all_append ..).mpr ⟨(all_rename ..).mpr (by rw [assignment_old]; exact oldModel.1),extraModel⟩,?_,?_⟩
    · intro i t h
      refine Fin.addCases (fun j h => ?_) (fun j h => ?_) i h
      · change (heads l (old n j)).equation = _ at h
        rw [head_old] at h
        cases idx : (b.heads j).equation with
        | none => simp [idx] at h
        | some tm =>
          rw [idx] at h
          have same : tm.rename (old n) = t := Option.some.inj h
          subst t
          change CommonNominalFullCarrier.Equivalent (m (source l (old n j))).1 _
          rw [source_old,TyTerm.eval_rename,assignment_old]
          exact oldModel.2.1 j tm idx
      · change (heads l (new b.slots j)).equation = _ at h
        rw [head_new] at h
        cases h
    · intro pair found
      obtain ⟨q,member,rfl⟩ := List.mem_map.mp found
      change CommonNominalFullCarrier.Subtype (m (source l (old n q.1))).1 (m (source l (old n q.2))).1
      rw [source_old,source_old]
      exact oldModel.2.2 q member

def refines (l : Layout b n) (extra) : GeneralSourceState.Refines b (expand l extra) where
  embed := old n
  source := source_old l
  rowSource := row_old l
  ordinary := fun a found => List.mem_append_left _ (List.mem_map.mpr ⟨a,found,rfl⟩)
  known := by
    intro i known
    unfold GeneralSourceState.State.graph
    change (heads l (old n i)).node ≠ _
    unfold heads
    rw [Fin.addCases_left]
    cases h : b.heads i <;> simp_all [head,GeneralSourceState.State.graph,GeneralSourceState.Head.node]
  intervals := fun p found => List.mem_map.mpr ⟨p,found,rfl⟩

end Yulang.GeneralWherePhysicalBase319
