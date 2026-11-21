import Yulang.GeneralWhereVersionCase317

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 26000000
namespace Yulang.GeneralWhereVersionBase317
open GeneralWhereVersionCase317 (lower upper addresses_differ)
open GeneralLiveCompoundLeafInstall316 (after reachable)
open GeneralLiveCompoundPost316 (raw)
open GeneralLiveCompoundPostFrames316 (rootPlan)
open GeneralLiveCompoundRegistry316 (otherChild)
open GeneralVersionedEndpointAddress315 (key)
open GeneralNominalState (sources)
open GeneralSourceState (equationAtoms equationAtoms_exact)
open Core.PresenceGeneration (TyTerm)

abbrev injectOld (i : Fin 8) : Fin 10 := i.castAdd 2
abbrev injectNew (i : Fin 2) : Fin 10 := i.natAdd 8
abbrev five : Fin 10 := injectOld 5
abbrev six : Fin 10 := injectOld 6
abbrev seven : Fin 10 := injectOld 7
abbrev two : Fin 10 := injectOld 2
abbrev loSlot : Fin 10 := injectNew 0
abbrev hiSlot : Fin 10 := injectNew 1

theorem lower_fresh : lower ∉ sources raw :=
  GeneralVersionedHighOrigins315.raw_absent reachable
    (k := key rootPlan .lower otherChild.id 0 GeneralWhereVersionCase317.expr) (by decide)

theorem upper_fresh : upper ∉ sources raw :=
  GeneralVersionedHighOrigins315.raw_absent reachable
    (k := key rootPlan .upper otherChild.id 0 GeneralWhereVersionCase317.expr) (by decide)

noncomputable def source : Fin 10 → Nat :=
  fun i => Fin.addCases (m := 8) (n := 2) (motive := fun _ => Nat)
    GeneralMixedCompoundUpperBase307.source (fun j => if j = 0 then lower else upper) i

theorem source_old (i : Fin 8) : source (injectOld i) = GeneralMixedCompoundUpperBase307.source i := by
  simp only [source,injectOld,Fin.addCases_left]

theorem source_lo : source loSlot = lower := by simp [source]
theorem source_hi : source hiSlot = upper := by simp [source]

theorem new_cases (i : Fin 2) : i = 0 ∨ i = 1 := by omega

theorem old_not_lo (i : Fin 8) : GeneralMixedCompoundUpperBase307.source i ≠ lower :=
  fun h => lower_fresh (h ▸ GeneralNominalAllocationSupport.slot_source raw i)

theorem old_not_hi (i : Fin 8) : GeneralMixedCompoundUpperBase307.source i ≠ upper :=
  fun h => upper_fresh (h ▸ GeneralNominalAllocationSupport.slot_source raw i)

theorem injective : Function.Injective source := by
  intro a b
  refine Fin.addCases (m := 8) (n := 2) (fun i => ?_) (fun i => ?_) a <;>
    refine Fin.addCases (m := 8) (n := 2) (fun j => ?_) (fun j => ?_) b
  · change source (injectOld _) = source (injectOld _) → _
    rw [source_old,source_old]
    intro h; exact congrArg injectOld (GeneralMixedCompoundUpperBase307.injective h)
  · rcases new_cases j with rfl|rfl
    · exact fun h => False.elim (old_not_lo i (source_old i ▸ source_lo ▸ h))
    · exact fun h => False.elim (old_not_hi i (source_old i ▸ source_hi ▸ h))
  · rcases new_cases i with rfl|rfl
    · exact fun h => False.elim (old_not_lo j (source_old j ▸ source_lo ▸ h.symm))
    · exact fun h => False.elim (old_not_hi j (source_old j ▸ source_hi ▸ h.symm))
  · rcases new_cases i with rfl|rfl <;> rcases new_cases j with rfl|rfl
    · exact fun _ => rfl
    · exact fun h => False.elim (addresses_differ (source_lo ▸ source_hi ▸ h))
    · exact fun h => False.elim (addresses_differ (source_lo ▸ source_hi ▸ h.symm))
    · exact fun _ => rfl

abbrev shapes (k : Fin 2) : GeneralSourceState.Shape 10 := if k = 0 then .emptyRecord else .variant 0
abbrev heads (i : Fin 10) : GeneralSourceState.Head shapes :=
  if i = two ∨ i = seven then .structural 0 Fin.elim0 else
  if i = five then .structural 1 (fun _ => injectOld 4) else
  if i = six ∨ i = loSlot ∨ i = hiSlot then .structural 1 (fun _ => two) else .unresolved

abbrev endpointTerm : TyTerm (Fin 10) := .variant 0 (.var two)

abbrev ordinary :=
  GeneralMixedCompoundUpperBase307.base.ordinary.map (PresenceNormalForm.Atom.rename injectOld) ++
    equationAtoms loSlot endpointTerm ++ equationAtoms hiSlot endpointTerm

noncomputable def base : GeneralSourceState.State where
  slots := 10
  source := source
  source_injective := injective
  rowSource := source
  ordinary := ordinary
  kinds := 2
  shapes := shapes
  shapes_injective := by
    intro a b h
    rcases new_cases a with rfl|rfl <;> rcases new_cases b with rfl|rfl
    · rfl
    · cases h
    · cases h
    · rfl
  heads := heads
  intervals := []
  heads_sound := by
    intro assignment valid i term found
    have parts := (PresenceNormalForm.all_append ..).mp valid
    have first := (PresenceNormalForm.all_append ..).mp parts.1
    have prior := (PresenceNormalForm.all_rename ..).mp first.1
    by_cases empty : i = two ∨ i = seven
    · rcases empty with rfl|rfl
      · have eq : term = .emptyRecord := Option.some.inj found.symm
        subst term; exact GeneralMixedCompoundUpperBase307.base.heads_sound (assignment ∘ injectOld) prior 2 _ rfl
      · have eq : term = .emptyRecord := Option.some.inj found.symm
        subst term; exact GeneralMixedCompoundUpperBase307.base.heads_sound (assignment ∘ injectOld) prior 7 _ rfl
    · by_cases oldFive : i = five
      · subst i
        have eq : term = .variant 0 (.var (injectOld 4)) := Option.some.inj found.symm
        subst term; exact GeneralMixedCompoundUpperBase307.base.heads_sound (assignment ∘ injectOld) prior 5 _ rfl
      · by_cases point : i = six ∨ i = loSlot ∨ i = hiSlot
        · rcases point with rfl|rfl|rfl
          · have eq : term = endpointTerm := Option.some.inj found.symm
            subst term; exact GeneralMixedCompoundUpperBase307.base.heads_sound (assignment ∘ injectOld) prior 6 _ rfl
          · have eq : term = endpointTerm := Option.some.inj found.symm
            subst term; exact (equationAtoms_exact ..).mp first.2
          · have eq : term = endpointTerm := Option.some.inj found.symm
            subst term; exact (equationAtoms_exact ..).mp parts.2
        · simp [heads,empty,oldFive,point,GeneralSourceState.Head.equation] at found
  intervals_sound := by intro _ _ _ impossible; cases impossible

end Yulang.GeneralWhereVersionBase317
