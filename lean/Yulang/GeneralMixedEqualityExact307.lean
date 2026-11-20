import Yulang.GeneralNominalVersionedMixedEqualityClosure235
import Yulang.GeneralDictionaryDefaultExpression209

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralMixedEqualityExact307
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedKernel234 (Equal Step)
open GeneralNominalVersionedMixedEqualityClosure235 (Trace trace_sources trace_raw trace_models)
open GeneralNominalVersionedAdministrative232 (equate)
open GeneralNominalFeedbackSteps (RawEqual)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

abbrev raw (s : State roles) (m : Assignment) :=
  GeneralNominalState.Models s.core.erased.current.context.state m

abbrev support (s : State roles) := GeneralNominalState.sources s.core.erased.current.context.state

abbrev entails (s : State roles) (a b : Nat) := RawEqual s.core.erased.current a b

theorem raw_step (s : State roles) (a b : Nat) (m : Assignment) :
    raw (equate s a b) m ↔ raw s m ∧ Equivalent (m a).1 (m b).1 :=
  (GeneralNominalState.extend_models ..).trans
    (and_congr Iff.rfl (GeneralNominalCaptureMerges.equations_exact ..))

theorem reconstruct (path : Trace anchor s) (m : Assignment) :
    raw s m ↔ raw anchor m ∧
      ∀ a ∈ support anchor, ∀ b ∈ support anchor, entails s a b → Equivalent (m a).1 (m b).1 := by
  induction path with
  | refl =>
    exact ⟨fun h => ⟨h,fun a _ b _ eq => eq m h⟩,And.left⟩
  | @tail current a b path ha hb eq novel ih =>
    constructor
    · intro h
      exact ⟨(ih.mp ((raw_step current a b m).mp h).1).1,fun a _ b _ eq => eq m h⟩
    · rintro ⟨base,exactAll⟩
      apply (raw_step current a b m).mpr
      refine ⟨ih.mpr ⟨base,?_⟩,exactAll a ((trace_sources path).mp ha) b ((trace_sources path).mp hb)
        (GeneralNominalFeedbackSteps.equate_feedback current.core.erased.current a b)⟩
      intro x xLive y yLive old
      exact exactAll x xLive y yLive (GeneralNominalVersionedMixedEqualityClosure235.raw_preserved old)

def ObservesSame (anchor s t : State roles) : Prop :=
  ∀ a ∈ support anchor, ∀ b ∈ support anchor, entails s a b ↔ entails t a b

def SameRaw (s t : State roles) : Prop := ∀ m, raw s m ↔ raw t m

theorem exact_code (ps : Trace anchor s) (pt : Trace anchor t) :
    ObservesSame anchor s t ↔ SameRaw s t := by
  constructor
  · intro code m
    rw [reconstruct ps,reconstruct pt]
    exact and_congr Iff.rfl ⟨fun h a ha b hb eq => h a ha b hb ((code a ha b hb).mpr eq),
      fun h a ha b hb eq => h a ha b hb ((code a ha b hb).mp eq)⟩
  · intro same a _ b _
    exact ⟨fun h m hm => h m ((same m).mpr hm),fun h m hm => h m ((same m).mp hm)⟩

/-- Equality-only transitions are the identical administrative constructor from
Mixed234, with its genuine source support and strict raw guard. -/
inductive EqStep : State roles → State roles → Prop
  | next {s} (a b : Nat) : a ∈ support s → b ∈ support s → Equal s a b → ¬ entails s a b →
      EqStep s (equate s a b)

theorem extend (ps : Trace anchor s) (act : EqStep s t) : Trace anchor t := by
  cases act with | next a b ha hb eq novel => exact .tail ps ha hb eq novel

theorem actual (r : GeneralDeclarations.Registry) (d : GeneralSourceDictionaries.Occurrence roles)
    (act : EqStep s t) : Step r d s t := by
  cases act with
  | next a b ha hb eq novel =>
    exact ⟨d,.root,.administrative (.equate d a b ha hb eq novel)⟩

theorem copy_pair (ps : Trace anchor s) (pt : Trace anchor t) (same : SameRaw s t)
    (a b : Nat) (one : a ∈ support s) (two : b ∈ support s)
    (equal : Equal s a b) (novel : ¬ entails s a b) :
    EqStep t (equate t a b) ∧ SameRaw (equate s a b) (equate t a b) := by
  refine ⟨.next a b ((trace_sources pt).mpr ((trace_sources ps).mp one))
    ((trace_sources pt).mpr ((trace_sources ps).mp two)) ?_ ?_,?_⟩
  · intro m live
    exact equal m ((trace_models ps m).mpr ((trace_models pt m).mp live))
  · intro holds
    exact novel (fun m valid => holds m ((same m).mp valid))
  · intro m
    rw [raw_step,raw_step,same m]

theorem exact_successor (ps : Trace anchor s) (pt : Trace anchor t) (same : SameRaw s t)
    (act : EqStep s u) : ∃ v, EqStep t v ∧ SameRaw u v := by
  cases act with
  | next a b one two equal novel =>
    exact ⟨equate t a b,copy_pair ps pt same a b one two equal novel⟩

theorem terminal_formula (p : Trace anchor s)
    (closed : GeneralNominalVersionedMixedTerminalStable234.EqualityClosed s)
    (m : Assignment) :
    raw s m ↔ raw anchor m ∧
      ∀ a ∈ support anchor, ∀ b ∈ support anchor, Equal anchor a b → Equivalent (m a).1 (m b).1 := by
  rw [reconstruct p]
  apply and_congr Iff.rfl
  constructor
  · intro read a ha b hb eq
    exact read a ha b hb (closed a b ((trace_sources p).mpr ha) ((trace_sources p).mpr hb)
      (fun x h => eq x ((trace_models p x).mp h)))
  · intro read a ha b hb entail
    exact read a ha b hb (fun x h => entail x ((trace_models p x).mpr h).1.1)

theorem canonical_terminal (ps : Trace anchor s) (pt : Trace anchor t)
    (sc : GeneralNominalVersionedMixedTerminalStable234.EqualityClosed s)
    (tc : GeneralNominalVersionedMixedTerminalStable234.EqualityClosed t) : SameRaw s t :=
  fun m => (terminal_formula ps sc m).trans (terminal_formula pt tc m).symm

end Yulang.GeneralMixedEqualityExact307
