import Yulang.CommonEffectTypeRowMap
import Yulang.CommonFiniteMask

/-! Demand-order invariance under a two-sided row order automorphism.
Negative arrow ranks quantify arbitrary environments; the proof transports
those environments and observations in BOTH directions. No finite depth/rank
bound or restriction of a universal type to an image is used. -/
namespace Yulang.CommonEffectFiniteRowMap
open Common (Row rowLe)
open CommonFinite (Observation Environment ProbeAt MaskedProbeStep)

def type (onRow : Row → Row) : CommonFinite.Ty Row → CommonFinite.Ty Row
  | .base scalar => .base scalar
  | .bottom => .bottom
  | .top => .top
  | .union first last => .union (type onRow first) (type onRow last)
  | .inter first last => .inter (type onRow first) (type onRow last)
  | .pair first last => .pair (type onRow first) (type onRow last)
  | .emptyRecord => .emptyRecord
  | .exactEmpty => .exactEmpty
  | .record label head tail => .record label (type onRow head) (type onRow tail)
  | .recordDefault label source fallback => .recordDefault label (type onRow source) (type onRow fallback)
  | .variant label payload => .variant label (type onRow payload)
  | .arrow arg incoming result outgoing => .arrow (type onRow arg) (onRow incoming) (type onRow result) (onRow outgoing)
  | .mask hidden body => .mask hidden (type onRow body)

def observation (onRow : Row → Row) : Observation Row → Observation Row
  | .trivial => .trivial
  | .impossible => .impossible
  | .base scalar => .base scalar
  | .records => .records
  | .role name => .role name
  | .pairFirst body => .pairFirst (observation onRow body)
  | .pairLast body => .pairLast (observation onRow body)
  | .field label body => .field label (observation onRow body)
  | .optional label body => .optional label (observation onRow body)
  | .variant label body => .variant label (observation onRow body)
  | .arrowArgument name => .arrowArgument name
  | .arrowResult body => .arrowResult (observation onRow body)
  | .arrowInputRow row => .arrowInputRow (onRow row)
  | .arrowOutputRow row => .arrowOutputRow (onRow row)

def environment (onRow : Row → Row) (source : Environment Row) : Environment Row :=
  ⟨fun name => type onRow (source.types name), source.roles⟩

theorem type_inverse (first last : Row → Row) (inverse : ∀ row, last (first row) = row)
    (source : CommonFinite.Ty Row) : type last (type first source) = source := by
  induction source <;> simp_all only [type]

theorem observation_inverse (first last : Row → Row) (inverse : ∀ row, last (first row) = row)
    (source : Observation Row) : observation last (observation first source) = source := by
  induction source <;> simp_all only [observation]

theorem environment_inverse (first last : Row → Row) (inverse : ∀ row, last (first row) = row)
    (source : Environment Row) : environment last (environment first source) = source := by
  cases source
  simp only [environment, type_inverse first last inverse]

theorem observation_trivial (onRow : Row → Row) (source : Observation Row) :
    observation onRow source = .trivial ↔ source = .trivial := by
  cases source <;> simp [observation]

theorem step_exact (onRow : Row → Row)
    (rowsExact : ∀ first last, rowLe (onRow first) (onRow last) ↔ rowLe first last)
    (before after : CommonFinite.Ty Row → CommonFinite.Ty Row → Prop)
    (argumentsExact : ∀ first last, after (type onRow first) (type onRow last) ↔ before first last)
    (hidden : List Nat) (source : CommonFinite.Ty Row) (env : Environment Row) (obs : Observation Row) :
    MaskedProbeStep rowLe (environment onRow env) after hidden (type onRow source) (observation onRow obs) ↔
      MaskedProbeStep rowLe env before hidden source obs := by
  induction source generalizing hidden obs with
  | union a b iha ihb =>
    rw [type, CommonFinite.maskedProbeStep_union, CommonFinite.maskedProbeStep_union]
    exact and_congr (iha hidden obs) (ihb hidden obs)
  | inter a b iha ihb =>
    rw [type, CommonFinite.maskedProbeStep_inter, CommonFinite.maskedProbeStep_inter]
    exact or_congr (iha hidden obs) (ihb hidden obs)
  | mask more body ih =>
    rw [type, CommonFinite.maskedProbeStep_mask, CommonFinite.maskedProbeStep_mask]
    exact ih (hidden ++ more) obs
  | record label head tail ihh iht =>
    have tailField (label' : Nat) (body : Observation Row) := iht hidden (.field label' body)
    have tailOptional (label' : Nat) (body : Observation Row) := iht hidden (.optional label' body)
    simp only [observation] at tailField tailOptional
    cases obs <;> simp_all only [type, observation, environment, MaskedProbeStep, observation_trivial]
  | recordDefault label source fallback ihs ihf =>
    have sourceField (label' : Nat) (body : Observation Row) := ihs hidden (.field label' body)
    have sourceOptional (label' : Nat) (body : Observation Row) := ihs hidden (.optional label' body)
    have sourcePresence := ihs hidden (.field label .trivial)
    simp only [observation] at sourceField sourceOptional sourcePresence
    cases obs <;> simp_all only [type, observation, environment, MaskedProbeStep, observation_trivial]
  | _ =>
    cases obs <;> simp_all only [type, observation, environment, MaskedProbeStep,
      observation_trivial]

theorem probe_exact (first last : Row → Row) (_leftInverse : ∀ row, last (first row) = row)
    (rightInverse : ∀ row, first (last row) = row)
    (rowsExact : ∀ a b, rowLe (first a) (first b) ↔ rowLe a b)
    (rank : Nat) (env : Environment Row) (source : CommonFinite.Ty Row) (obs : Observation Row) :
    ProbeAt rowLe rank (environment first env) (type first source) (observation first obs) ↔ ProbeAt rowLe rank env source obs := by
  induction rank generalizing env source obs with
  | zero => exact step_exact first rowsExact (fun _ _ => True) (fun _ _ => True) (fun _ _ => Iff.rfl) [] source env obs
  | succ rank ih =>
    apply step_exact first rowsExact _ _ ?_ [] source env obs
    intro a b
    constructor
    · intro accepted next test premise
      exact (ih next a test).mp (accepted (environment first next) (observation first test) ((ih next b test).mpr premise))
    · intro accepted next test premise
      have bSame := ih (environment last next) b (observation last test)
      have aSame := ih (environment last next) a (observation last test)
      rw [environment_inverse last first rightInverse, observation_inverse last first rightInverse] at bSame aSame
      exact aSame.mpr (accepted (environment last next) (observation last test) (bSame.mp premise))

theorem producerLe_exact (first last : Row → Row) (leftInverse : ∀ row, last (first row) = row)
    (rightInverse : ∀ row, first (last row) = row)
    (rowsExact : ∀ a b, rowLe (first a) (first b) ↔ rowLe a b)
    (source target : CommonFinite.Ty Row) :
    CommonFinite.ProducerLe rowLe (type first source) (type first target) ↔ CommonFinite.ProducerLe rowLe source target := by
  rw [CommonFinite.producerLe_iff_probe, CommonFinite.producerLe_iff_probe]
  constructor
  · intro accepted rank env obs premise
    exact (probe_exact first last leftInverse rightInverse rowsExact rank env source obs).mp
      (accepted rank (environment first env) (observation first obs)
        ((probe_exact first last leftInverse rightInverse rowsExact rank env target obs).mpr premise))
  · intro accepted rank env obs premise
    have targetSame := probe_exact first last leftInverse rightInverse rowsExact rank (environment last env) target (observation last obs)
    have sourceSame := probe_exact first last leftInverse rightInverse rowsExact rank (environment last env) source (observation last obs)
    rw [environment_inverse last first rightInverse, observation_inverse last first rightInverse] at targetSame sourceSame
    exact sourceSame.mpr (accepted rank (environment last env) (observation last obs) (targetSame.mp premise))

end Yulang.CommonEffectFiniteRowMap
