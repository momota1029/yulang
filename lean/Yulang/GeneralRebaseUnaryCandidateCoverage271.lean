import Yulang.GeneralRebaseInstalledOutputCycles271

namespace Yulang.GeneralRebaseUnaryCandidateCoverage271
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedCycles232 (Cyclic CandidateCycle RawCandidateK2)
open GeneralNominalRecursiveInspection (Origin)
open GeneralNominalCommonBridge (Assignment)
open GeneralSourceDictionaries (Occurrence)
open GeneralDeclarations (Registry)
open GeneralRebaseSourceSurvivor267 (Boundary)
open GeneralRebaseNominalOrigin269 (Raw origin)
open GeneralRebaseUnaryRank271 (Unary value)
open GeneralRebaseUnaryReadback271 (Result run cycle stepNom stepStruct)
open GeneralRebasePartialBool268 (Answer Reflect)
open CommonNominalFullCarrier

theorem run_total (source : Nat → Option Unary) (covers : ∀ i, (source i).isSome = true) (o : Origin) :
 run source o ≠ .unknown := by
 induction o with
 | source n =>
   cases h : source n with
   | none =>
     have full := covers n
     rw [h] at full
     cases full
   | some t => simp [run,h]
 | nominal p name j ih =>
   change stepNom name j (run source p) ≠ .unknown
   cases known : run source p with
   | unknown => exact False.elim (ih known)
   | absent => intro impossible; cases impossible
   | found t =>
     cases t with
     | scalar b => intro impossible; cases impossible
     | wrapper name2 child =>
       change (if name = name2 ∧ j = 0 then Result.found child else Result.absent) ≠ Result.unknown
       split <;> intro impossible <;> cases impossible
 | structural p shape j ih =>
   change stepStruct (run source p) ≠ .unknown
   cases known : run source p with
   | unknown => exact False.elim (ih known)
   | absent | found _ => intro impossible; cases impossible

theorem universal_noncycle (state : State roles) (m : Assignment) (valid : Models state m)
 (source : Nat → Option Unary) (covers : ∀ i, (source i).isSome = true)
 (trusted : ∀ i ty, source i = some ty → Equivalent (m i).1 (value ty)) (o : Origin) :
 ¬ Cyclic state o := by
 have no := GeneralRebaseUnaryReadback271.cycle_sound state m valid source trusted o
 have definitely : cycle source o = some false := by
   unfold cycle
   split
   · exact False.elim ((run_total source covers o) (by assumption))
   · rfl
 rw [definitely] at no
 exact no

theorem no_raw_candidate (registry : Registry) (state : State roles) (focus : Occurrence roles)
 (model : ∃ m, Models state m) (none : ∀ o, ¬ Cyclic state o) :
 ¬ RawCandidateK2 registry state.core.erased.current.context (GeneralNominalVersionedCandidates231.inputs focus) := by
 rintro ⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩
 exact none (origin state visited.1) (GeneralRebaseRawIntoFull271.recurs state model visited.1 cycle)

theorem no_semantic_candidate (registry : Registry) (state : State roles) (focus : Occurrence roles)
 (none : ∀ o, ¬ Cyclic state o) : ¬ CandidateCycle registry state focus := by
 rintro ⟨_,_,entry,_,loop⟩
 exact none entry.1 loop

theorem no_candidate (registry : Registry) (state : State roles) (focus : Occurrence roles)
 (model : ∃ m, Models state m) (none : ∀ o, ¬ Cyclic state o) : ¬ (Boundary roles).CandidateK2 registry state focus := by
 rintro (raw | full)
 · exact no_raw_candidate _ state focus model none raw
 · exact no_semantic_candidate _ state focus none full

def declaredTotal : Answer := some false

/-- The response is bound to a supplied full model whose source readback
is total and certified finite unary, not just a table of boolean claims. -/
theorem declaredTotal_sound (registry : Registry) (state : State roles) (focus : Occurrence roles)
 (m : Assignment) (full : Models state m) (source : Nat → Option Unary)
 (covers : ∀ i, (source i).isSome = true)
 (trusted : ∀ i ty, source i = some ty → Equivalent (m i).1 (value ty)) :
 Reflect ((Boundary roles).CandidateK2 registry state focus) declaredTotal :=
 no_candidate registry state focus ⟨m,full⟩ (universal_noncycle state m full source covers trusted)

namespace Installed252
open GeneralDictionaryOutputDepth252 (model root sourceRegistry)
open GeneralDictionaryOutputDepthInstall252 (installed installed_model)
open GeneralRebaseInstalledOutputCycles271 (source known)

theorem checked_candidates :
 Reflect ((Boundary GeneralDictionaryOutputDepth252.roles).CandidateK2 sourceRegistry installed root) declaredTotal :=
 declaredTotal_sound sourceRegistry installed root model installed_model source (fun _ => rfl)
    (fun i _ found => Option.some.inj found ▸ known i)

end Installed252
end Yulang.GeneralRebaseUnaryCandidateCoverage271
