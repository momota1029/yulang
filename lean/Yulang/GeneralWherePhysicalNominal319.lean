import Yulang.GeneralWherePhysicalView319

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 18500
set_option maxHeartbeats 11000000
namespace Yulang.GeneralWherePhysicalNominal319
open GeneralWherePhysicalIndex319 (old new)
open GeneralWherePhysicalBase319 (Layout expand source_old source_new base_models)
open GeneralWherePhysicalView319 (expandView)
open GeneralNominalState (State Models Descriptor Denotes FitsAll)
open GeneralNominalRefinements (renameDescriptor renameParameter fits_transport)
open GeneralNominalCommonBridge (Assignment assignment)
open GeneralNormalizedObservation (Head Rewrites)
open PresenceNormalForm (Atom All)

abbrev Extra (s : State) (n : Nat) := List (Atom (Fin (s.base.slots+n)))
abbrev Added (s : State) (n : Nat) := Fin n → Head s.view.shapes (s.base.slots+n)
abbrev Checked {s : State} (l : Layout s.base n) (extra : Extra s n) (added : Added s n) :=
  ∀ i t, (added i).term = some t → Rewrites (expand l extra) (.var (new s.base.slots i)) t

def nominals (s : State) (n : Nat) : Fin (s.base.slots+n) → Option (Descriptor (s.base.slots+n)) :=
  Fin.addCases (fun i => (s.nominals i).map (renameDescriptor (old n))) (fun _ => none)

@[simp] theorem nominal_old (s : State) (n : Nat) (i : Fin s.base.slots) :
    nominals s n (old n i) = (s.nominals i).map (renameDescriptor (old n)) := Fin.addCases_left ..

@[simp] theorem nominal_new (s : State) (n : Nat) (i : Fin n) :
    nominals s n (new s.base.slots i) = none := Fin.addCases_right ..

def extend (s : State) (l : Layout s.base n) (extra : Extra s n)
    (added : Added s n) (valid : Checked l extra added) : State where
  base := expand l extra
  view := expandView l extra s.view added valid
  constructors := s.constructors
  nominals := nominals s n
  catalogue := by
    intro i descriptor recorded
    refine Fin.addCases (fun j h => ?_) (fun j h => ?_) i recorded
    · rw [nominal_old] at h
      cases k : s.nominals j with
      | none => simp [k] at h
      | some d =>
        rw [k] at h
        have same := Option.some.inj h
        subst descriptor
        exact s.catalogue j d k
    · rw [nominal_new] at h; cases h
  bodies_opaque := by
    intro i descriptor recorded
    refine Fin.addCases (fun j h => ?_) (fun j h => ?_) i recorded
    · rw [nominal_old] at h
      cases k : s.nominals j with
      | none => simp [k] at h
      | some d =>
        change Fin.addCases (motive := fun _ => Head s.view.shapes (s.base.slots+n)) (fun i => GeneralWherePhysicalView319.head (old n) (s.view.heads i)) added (old n j) = _
        rw [Fin.addCases_left,s.bodies_opaque j d k]
        rfl
    · rw [nominal_new] at h; cases h
  seed := s.seed
  allocated := s.allocated
  reserved := s.reserved
  ordinary := s.ordinary

def refinement (s : State) (l : Layout s.base n) (extra : Extra s n)
    (added : Added s n) (valid : Checked l extra added) :
    GeneralNominalRefinements.Refines s (extend s l extra added valid) where
  base := GeneralWherePhysicalBase319.refines l extra
  heads := by
    intro i term found
    apply Rewrites.head
    change (GeneralWherePhysicalBase319.heads l (old n i)).equation = _
    rw [GeneralWherePhysicalBase319.head_old,found]; rfl
  nominals := by
    intro i descriptor found
    change nominals s n (old n i) = _
    rw [nominal_old,found]; rfl
  ordinary := fun _ h => h
  known := by
    rintro key ⟨i,equal,headKnown|⟨descriptor,recorded⟩⟩
    · refine ⟨old n i,(source_old l i).trans equal,.inl ?_⟩
      change (Fin.addCases (motive := fun _ => Head s.view.shapes (s.base.slots+n)) (fun i => GeneralWherePhysicalView319.head (old n) (s.view.heads i)) added
        (old n i)).node ≠ _
      rw [Fin.addCases_left]
      cases h : s.view.heads i <;>
        simp_all [GeneralNormalizedObservation.Snapshot.graph,GeneralNormalizedObservation.Head.node,
          GeneralWherePhysicalView319.head]
    · refine ⟨old n i,(source_old l i).trans equal,.inr ⟨renameDescriptor (old n) descriptor,?_⟩⟩
      change nominals s n (old n i) = _
      rw [nominal_old,recorded]; rfl
  reserved := fun _ h => h
  allocated := fun _ h => h
  seed := rfl
  constructors := rfl

theorem fitsAll_reverse {s t : State} (ref : GeneralNominalRefinements.Refines s t)
    (m : Assignment) (params : List (GeneralNominalState.Parameter s.base.slots)) (args)
    (truth : FitsAll s.base m params args) :
    FitsAll t.base m (params.map (renameParameter ref.base.embed)) args := by
  induction truth with
  | nil => exact .nil
  | cons h _ ih => exact .cons ((fits_transport ref m _ _).mpr h) ih

theorem denotes_iff {s t : State} (ref : GeneralNominalRefinements.Refines s t)
    (m : Assignment) (i : Fin s.base.slots) (d : Descriptor s.base.slots) :
    Denotes t.base m (ref.base.embed i) (renameDescriptor ref.base.embed d) ↔ Denotes s.base m i d := by
  constructor
  · rintro ⟨args,fit,sem⟩
    exact ⟨args,GeneralNominalRefinements.fitsAll_transport ref m _ _ fit,by simpa only [ref.base.source,renameDescriptor] using sem⟩
  · rintro ⟨args,fit,sem⟩
    exact ⟨args,fitsAll_reverse ref m _ _ fit,by simpa only [ref.base.source,renameDescriptor] using sem⟩

theorem models_iff (s : State) (l : Layout s.base n) (extra : Extra s n) (added : Added s n)
    (valid : Checked l extra added) (m : Assignment) :
    Models (extend s l extra added valid) m ↔
      Models s m ∧ All CommonNominalFullCarrier.model (assignment (expand l extra) m) extra := by
  let ref := refinement s l extra added valid
  constructor
  · intro facts
    exact ⟨GeneralNominalRefinements.models ref m facts,((base_models l extra m).mp facts.1).2⟩
  · rintro ⟨before,extra⟩
    refine ⟨(base_models l _ _).mpr ⟨before.1,extra⟩,?_,before.2.2⟩
    intro i d found
    refine Fin.addCases (fun j h => ?_) (fun j h => ?_) i found
    · change nominals s n (old n j) = some d at h
      rw [nominal_old] at h
      cases yes : s.nominals j with
      | none => simp [yes] at h
      | some k =>
        rw [yes] at h
        have same := Option.some.inj h
        subst d
        exact (denotes_iff ref m j k).mpr (before.2.1 j k yes)
    · change nominals s n (new s.base.slots j) = some d at h
      rw [nominal_new] at h; cases h

end Yulang.GeneralWherePhysicalNominal319
