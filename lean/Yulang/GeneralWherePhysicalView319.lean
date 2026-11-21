import Yulang.GeneralWherePhysicalBase319

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 17000
set_option maxHeartbeats 9000000
namespace Yulang.GeneralWherePhysicalView319
open GeneralWherePhysicalIndex319 (old new)
open GeneralWherePhysicalBase319 (Layout expand head_old)
open GeneralNormalizedObservation (Snapshot Head Deferred Shape Rewrites recordTerm)
open Core.PresenceGeneration (TyTerm)
open PresenceNormalForm (Atom)

theorem rewrites_rename (l : Layout b n) (extra)
    {a c : TyTerm (Fin b.slots)} (step : Rewrites b a c) :
    Rewrites (expand l extra) (a.rename (old n)) (c.rename (old n)) := by
  induction step with
  | refl _ => exact .refl _
  | trans _ _ ab bc => exact .trans ab bc
  | @head i term found =>
    apply Rewrites.head
    change (GeneralWherePhysicalBase319.heads l (old n i)).equation = _
    rw [head_old,found]; rfl
  | ordinary forward backward =>
    exact .ordinary (List.mem_append_left _ (List.mem_map.mpr ⟨_,forward,rfl⟩))
      (List.mem_append_left _ (List.mem_map.mpr ⟨_,backward,rfl⟩))
  | pair _ _ ab cd => exact .pair ab cd
  | record _ _ ab cd => exact .record ab cd
  | variant _ ab => exact .variant ab
  | union _ _ ab cd => exact .union ab cd
  | required => exact .required
  | shadow => exact .shadow
  | swap apart => exact .swap apart
  | merge => exact .merge
  | idempotent => exact .idempotent

theorem record_rename (f : Fin m → Fin n) (entries : List (Nat × TyTerm (Fin m))) (tail : TyTerm (Fin m)) :
    (recordTerm entries tail).rename f =
      recordTerm (entries.map fun e => (e.1,e.2.rename f)) (tail.rename f) := by
  induction entries with
  | nil => rfl
  | cons one more ih =>
    change TyTerm.record one.1 (one.2.rename f) ((recordTerm more tail).rename f) = _
    rw [ih]
    rfl

def deferred (f : Fin m → Fin n) : Deferred m → Deferred n
  | .unresolved => .unresolved
  | .residual fields tail => .residual (fields.map fun e => (e.1,f e.2)) (tail.rename f)
  | .unsupported term => .unsupported (term.rename f)

theorem deferred_term (f : Fin m → Fin n) (d : Deferred m) :
    (deferred f d).term = d.term.map (fun term => term.rename f) := by
  cases d with
  | unresolved => rfl
  | unsupported _ => rfl
  | residual fields tail =>
    change some (recordTerm (((fields.map fun e => (e.1,f e.2))).map fun e => (e.1, .var e.2))
      (tail.rename f)) = some ((recordTerm (fields.map fun e => (e.1, .var e.2)) tail).rename f)
    rw [record_rename,List.map_map,List.map_map]
    rfl

def head (f : Fin m → Fin n) {shapes : Fin k → Shape} : Head shapes m → Head shapes n
  | .deferred d => .deferred (deferred f d)
  | .scalar b => .scalar b
  | .structural tag kids => .structural tag (f ∘ kids)

theorem structural_term (f : Fin m → Fin n) (s : Shape) (kids : Fin s.arity → Fin m) :
    s.term (f ∘ kids) = (s.term kids).rename f := by
  cases s with
  | pair | variant | exactEmpty => rfl
  | record labels =>
    unfold Shape.term
    rw [record_rename]
    congr 1
    rw [List.map_ofFn]
    rfl

theorem head_term (f : Fin m → Fin n) {shapes : Fin k → Shape} (h : Head shapes m) :
    (head f h).term = h.term.map (fun term => term.rename f) := by
  cases h with
  | deferred reason => exact deferred_term f reason
  | scalar _ => rfl
  | structural s kids => exact congrArg some (structural_term f (shapes s) kids)

/-- All previous inspection facts are transported literally. A new slot's
observation must be provided with a checked normalization in the expanded
ordinary state (or simply left unresolved). -/
def expandView (l : Layout b n) (extra) (view : Snapshot b)
    (added : Fin n → Head view.shapes (b.slots+n))
    (valid : ∀ i t, (added i).term = some t → Rewrites (expand l extra) (.var (new b.slots i)) t) :
    Snapshot (expand l extra) where
  kinds := view.kinds
  shapes := view.shapes
  shapes_injective := view.shapes_injective
  canonical := view.canonical
  heads := Fin.addCases (fun i => head (old n) (view.heads i)) added
  checked := by
    intro i term found
    refine Fin.addCases (fun j h => ?_) (fun j h => ?_) i found
    · rw [Fin.addCases_left,head_term] at h
      cases idx : (view.heads j).term with
      | none => simp [idx] at h
      | some source =>
        rw [idx] at h
        have eq : source.rename (old n) = term := Option.some.inj h
        subst term
        exact rewrites_rename l extra (view.checked j source idx)
    · rw [Fin.addCases_right] at h
      exact valid j term h

end Yulang.GeneralWherePhysicalView319
