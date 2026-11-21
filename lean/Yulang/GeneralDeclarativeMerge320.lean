import Yulang.GeneralDeclarativeEntailment320
import Yulang.CommonNominalFullConstructors

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 14500
set_option maxHeartbeats 4200000
namespace Yulang.GeneralDeclarativeMerge320
open CommonNominalFullCarrier (Ty Equivalent Subtype model subtype_trans subtype_refl
  common_union_is_join common_inter_is_meet)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeHead320 (State Models Read)
open GeneralDeclarativeDemand320 (Bounds bounds_sound)
open GeneralDeclarativeWhere319 (Capture InInterval)
open GeneralDeclarativeBounds319 (Bound bound_sound)
open Core.PresenceGeneration (TyTerm)
open PresenceNormalForm (Atom)

def lower (first : Capture) : List Capture → TyTerm Nat
  | [] => .var first.lower
  | next::rest => .union (.var first.lower) (lower next rest)

def upper (first : Capture) : List Capture → TyTerm Nat
  | [] => .var first.upper
  | next::rest => .inter (.var first.upper) (upper next rest)

theorem lower_exact (m : Assignment) (first : Capture) (rest : List Capture) (actual : Ty) :
    Subtype ((lower first rest).eval model m) actual ↔
      ∀ entry ∈ first :: rest, Subtype (m entry.lower).1 actual := by
  induction rest generalizing first with
  | nil => simp [lower,TyTerm.eval]
  | cons next tail ih =>
    change Subtype (.union (m first.lower).1 ((lower next tail).eval model m)) actual ↔ _
    rw [common_union_is_join,ih]
    simp

theorem upper_exact (m : Assignment) (first : Capture) (rest : List Capture) (actual : Ty) :
    Subtype actual ((upper first rest).eval model m) ↔
      ∀ entry ∈ first :: rest, Subtype actual (m entry.upper).1 := by
  induction rest generalizing first with
  | nil => simp [upper,TyTerm.eval]
  | cons next tail ih =>
    change Subtype actual (.inter (m first.upper).1 ((upper next tail).eval model m)) ↔ _
    rw [common_inter_is_meet,ih]
    simp

def EqualTerm (s : State) (name : Nat) (term : TyTerm Nat) : Prop :=
  Atom.tyLe (.var name) term ∈ s.normal.ordinary ∧
    Atom.tyLe term (.var name) ∈ s.normal.ordinary

theorem equality_sound {s : State} {name : Nat} {term : TyTerm Nat}
    (known : EqualTerm s name term) (m : Assignment) (valid : Models s m) :
    Equivalent (m name).1 (term.eval model m) :=
  ⟨valid.1.1 _ known.1,valid.1.1 _ known.2⟩

/-- Scope has identified one shared actual binder and both ordinary
aggregate equations. None of these data are a dictionary or model choice. -/
structure Merge (s : State) (first : Capture) (rest : List Capture) (combined : Capture) : Prop where
  each : ∀ entry ∈ first :: rest, Bounds s entry
  sameCenter : ∀ entry ∈ first :: rest,
    Bound s.normal entry.center combined.center ∧ Bound s.normal combined.center entry.center
  lowerEq : EqualTerm s combined.lower (lower first rest)
  upperEq : EqualTerm s combined.upper (upper first rest)

theorem interval_exact {s first rest combined} (facts : Merge s first rest combined)
    (m : Assignment) (valid : Models s m) (actual : Ty) :
    InInterval (m combined.lower).1 (m combined.upper).1 actual ↔
      ∀ entry ∈ first :: rest, InInterval (m entry.lower).1 (m entry.upper).1 actual := by
  have lo := equality_sound facts.lowerEq m valid
  have hi := equality_sound facts.upperEq m valid
  constructor
  · intro fitting e present
    exact ⟨(lower_exact m first rest actual).mp (subtype_trans lo.2 fitting.1) e present,
      (upper_exact m first rest actual).mp (subtype_trans fitting.2 hi.1) e present⟩
  · intro fits
    exact ⟨subtype_trans lo.1 ((lower_exact m first rest actual).mpr (fun e h => (fits e h).1)),
      subtype_trans ((upper_exact m first rest actual).mpr (fun e h => (fits e h).2)) hi.2⟩

theorem shared_center {s first rest combined} (facts : Merge s first rest combined)
    (m : Assignment) (valid : Models s m) :
    InInterval (m combined.lower).1 (m combined.upper).1 (m combined.center).1 ∧
    ∀ entry ∈ first :: rest, Equivalent (m entry.center).1 (m combined.center).1 := by
  have link : ∀ entry ∈ first :: rest, Equivalent (m entry.center).1 (m combined.center).1 :=
    fun entry member =>
      ⟨bound_sound m valid.1 (facts.sameCenter entry member).1,
        bound_sound m valid.1 (facts.sameCenter entry member).2⟩
  refine ⟨(interval_exact facts m valid _).mpr ?_,link⟩
  intro entry present
  have own := bounds_sound (facts.each entry present) m valid
  exact ⟨subtype_trans own.1 (link entry present).1,subtype_trans (link entry present).2 own.2⟩

/-- All actual uses now read one binder; the proof neither simulates
allocation nor treats equality of interval endpoints as equality of centers. -/
theorem occurrence_read {s first rest combined} (facts : Merge s first rest combined)
    {capture : Nat → Capture} {name : Nat} (placed : capture name = combined)
    {entry : Capture} (there : entry ∈ first :: rest) :
    Read s capture .actual entry.center (.variable name) := by
  apply Read.capture <;> rw [GeneralDeclarativeHead320.byMode,placed]
  · exact (facts.sameCenter entry there).1
  · exact (facts.sameCenter entry there).2

end Yulang.GeneralDeclarativeMerge320
