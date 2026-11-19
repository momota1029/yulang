import Yulang.GeneralRebaseObservationLimits278

namespace Yulang.GeneralRebaseOperationalKey278
open GeneralRebaseRoundMicro278 (Tick next)
open GeneralRebaseInstallTimeline278 (installedCount observedCount)
open GeneralRebaseObservationLimits278 (VersionInstallAvailable LooseInstallAvailable)

structure Key where
  installed : Nat
  observed : Nat
  canInstall : Bool
  deriving DecidableEq, Repr

def encode (t : Tick) : Key :=
  ⟨installedCount t, observedCount t, decide (t.phase = .enter)⟩

/-- Reject inconsistent counter/flag combinations; the flag distinguishes
    reobserve from the next install without copying the three-valued phase. -/
def decode (k : Key) : Option Tick :=
  if k.canInstall then
    if k.installed = k.observed then some ⟨k.installed,.enter⟩ else none
  else if k.installed = k.observed+1 then
    some ⟨k.observed,.installed⟩
  else if k.installed = k.observed then
    match k.installed with
    | 0 => none
    | i+1 => some ⟨i,.refreshed⟩
  else none

theorem decode_encode (t : Tick) : decode (encode t) = some t := by
  rcases t with ⟨n,p⟩
  cases p
  · simp [encode,decode,installedCount,observedCount]
  · simp [encode,decode,installedCount,observedCount]
  · simp [encode,decode,installedCount,observedCount]

theorem encode_injective (a b : Tick) (same : encode a = encode b) : a = b := by
  have both := congrArg decode same
  simpa only [decode_encode,Option.some.injEq] using both

theorem decode_sound (k : Key) (t : Tick) (h : decode k = some t) : encode t = k := by
  rcases k with ⟨a,b,c⟩
  cases c
  · unfold decode at h
    simp only [Bool.false_eq_true,ite_false] at h
    by_cases earlier : a = b+1
    · have tick : (⟨b,.installed⟩ : Tick) = t := by simpa [earlier] using h
      subst t
      simp [encode,installedCount,observedCount,earlier]
    · by_cases eq : a = b
      · subst b
        cases a with
        | zero => simp at h
        | succ a =>
          have tick : (⟨a,.refreshed⟩ : Tick) = t := by simpa using h
          subst t
          rfl
      · simp [earlier,eq] at h
  · unfold decode at h
    simp only [↓reduceIte] at h
    by_cases eq : a = b
    · subst b
      have tick : (⟨a,.enter⟩ : Tick) = t := by simpa using h
      subst t
      rfl
    · simp [eq] at h

theorem version_flag (t : Tick) : (encode t).canInstall = true ↔ VersionInstallAvailable t := by
  rcases t with ⟨n,p⟩
  cases p
  · refine ⟨fun _ => ⟨_,(GeneralRebaseVersionAbsorb278.enter_install n _).mpr rfl⟩,fun _ => rfl⟩
  · exact ⟨fun h => by contradiction,fun ⟨target,step⟩ =>
      False.elim (GeneralRebaseVersionAbsorb278.installed_absorbs n target step)⟩
  · exact ⟨fun h => by contradiction,fun ⟨target,step⟩ =>
      False.elim (GeneralRebaseVersionAbsorb278.refreshed_absorbs n target step)⟩

theorem loose_flag (t : Tick) : (encode t).canInstall = true ↔ LooseInstallAvailable t := by
  rcases t with ⟨n,p⟩
  cases p
  · refine ⟨fun _ => ⟨_,(GeneralRebaseLooseAbsorb278.enter_install n _).mpr rfl⟩,fun _ => rfl⟩
  · exact ⟨fun h => by contradiction,fun ⟨target,step⟩ =>
      False.elim (GeneralRebaseLooseAbsorb278.installed_absorbs n target step)⟩
  · exact ⟨fun h => by contradiction,fun ⟨target,step⟩ =>
      False.elim (GeneralRebaseLooseAbsorb278.refreshed_absorbs n target step)⟩

def advance (k : Key) : Option Key := (decode k).map (encode ∘ next)

theorem advance_exact (t : Tick) : advance (encode t) = some (encode (next t)) := by
  simp [advance,decode_encode]

theorem advance_only (k l : Key) (edge : advance k = some l) :
    ∃ t, encode t = k ∧ encode (next t) = l := by
  cases h : decode k with
  | none => simp [advance,h] at edge
  | some t =>
    refine ⟨t,decode_sound k t h,?_⟩
    simpa [advance,h] using edge

theorem actual_families (k l : Key) (edge : advance k = some l) :
    ∃ t, encode t = k ∧ encode (next t) = l ∧
      GeneralNominalVersionedMixedKernel234.Step GeneralDictionaryVersionLoopSource237.registry
        GeneralDictionaryVersionLoopSource237.root (GeneralRebaseVersionMicro278.raw t)
          (GeneralRebaseVersionMicro278.raw (next t)) ∧
      GeneralRebaseLooseMicro278.PointStep (GeneralRebaseLooseMicro278.raw t)
        (GeneralRebaseLooseMicro278.raw (next t)) := by
  obtain ⟨t,fromKey,toKey⟩ := advance_only k l edge
  exact ⟨t,fromKey,toKey,GeneralRebaseVersionMicro278.actual t,GeneralRebaseLooseMicro278.point_actual t⟩

end Yulang.GeneralRebaseOperationalKey278
