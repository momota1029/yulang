import Yulang.GeneralDeclarativeFreshTerms324

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeMergeCenters324
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeDemand320 (Bounds bounds_sound)
open GeneralDeclarativeWhere319 (Capture InInterval)
open GeneralDeclarativeBounds319 (Bound)
open GeneralDeclarativeCaptureClosure320 (withOrdinary ordinary_models preserve_bound)
open GeneralNominalCommonBridge (Assignment)
open PresenceNormalForm (Atom All)
open CommonNominalFullCarrier (Equivalent Subtype model subtype_trans)
open GeneralDeclarativeMerge320 (lower upper lower_exact upper_exact)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)

def centerPair (n a : Nat) : List (Atom Nat) :=
  [.tyLe (.var a) (.var n),.tyLe (.var n) (.var a)]

def align (seed : Capture) (rest : List Capture) : List (Atom Nat) :=
  (seed :: rest).flatMap (fun entry => centerPair seed.center entry.center)

def Linked (s : State) (seed : Capture) (rest : List Capture) : Prop :=
  ∀ m, Models s m → ∀ entry ∈ seed :: rest, Equivalent (m entry.center).1 (m seed.center).1

theorem permitted (shared : Linked s seed rest) (m : Assignment) (valid : Models s m) :
    All model m (align seed rest) := by
  intro atom present
  obtain ⟨entry,known,part⟩ := List.mem_flatMap.mp present
  have equal := shared m valid entry known
  change atom ∈ centerPair seed.center entry.center at part
  rcases List.mem_cons.mp part with rfl|other
  · exact equal.1
  · cases List.mem_singleton.mp other
    exact equal.2

theorem conservative (shared : Linked s seed rest) (m : Assignment) :
    Models (withOrdinary s (align seed rest)) m ↔ Models s m :=
  (ordinary_models m).trans ⟨And.left,fun valid => ⟨valid,permitted shared m valid⟩⟩

theorem links_recorded (found : entry ∈ seed :: rest) :
    Bound (withOrdinary s (align seed rest)).normal entry.center seed.center ∧
      Bound (withOrdinary s (align seed rest)).normal seed.center entry.center := by
  have read (row : Atom Nat) (used : row ∈ centerPair seed.center entry.center) :
      row ∈ (withOrdinary s (align seed rest)).normal.ordinary :=
    List.mem_append_right _ (List.mem_flatMap.mpr ⟨entry,found,used⟩)
  exact ⟨.constraint (read _ List.mem_cons_self),
    .constraint (read _ (List.mem_cons_of_mem _ List.mem_cons_self))⟩

/-- The standard compatibility test is exactly the join-below-meet
condition (no existential model search). It only compares endpoints,
and therefore is not itself a proof of shared actual identities. -/
theorem whole_cross (m : Assignment) (seed : Capture) (rest : List Capture) :
    Subtype ((lower seed rest).eval model m) ((upper seed rest).eval model m) ↔
      ∀ l ∈ seed :: rest, ∀ u ∈ seed :: rest, Subtype (m l.lower).1 (m u.upper).1 := by
  constructor
  · intro known l left u right
    exact (upper_exact m seed rest (m l.lower).1).mp ((lower_exact m seed rest _).mp known l left) u right
  · intro pairwise
    apply (lower_exact m seed rest _).mpr
    intro l fromGroup
    exact (upper_exact m seed rest _).mpr (pairwise l fromGroup)

theorem cross_from_actual {s : State} (shared : Linked s seed rest)
    (bounds : ∀ e ∈ seed :: rest, Bounds s e) (m : Assignment) (valid : Models s m) :
    Subtype ((lower seed rest).eval model m) ((upper seed rest).eval model m) := by
  apply (whole_cross m seed rest).mpr
  intro l hasL u hasU
  exact subtype_trans (bounds_sound (bounds l hasL) m valid).1
    (subtype_trans (shared m valid l hasL).1
      (subtype_trans (shared m valid u hasU).2 (bounds_sound (bounds u hasU) m valid).2))

end Yulang.GeneralDeclarativeMergeCenters324
