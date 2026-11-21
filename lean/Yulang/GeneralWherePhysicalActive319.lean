import Yulang.GeneralWherePhysicalFresh319

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29500
set_option maxHeartbeats 24000000
namespace Yulang.GeneralWherePhysicalActive319
open GeneralDictionaryJournalRefinement228Source (snapshot interpretation)
open GeneralDictionaryJournalRefinement228Reobserve (pointSnapshot exactCopy)
open GeneralWherePhysicalPast319 (point layout extra firstLo savedHi two four)
open GeneralWherePhysicalFresh319 (raw finalLayout newAtoms oldLo upperSlot lowerSlot oldTwo oldFour)
open GeneralWherePhysicalIndex319 (old new)
open GeneralWherePhysicalBase319 (expand head_old)
open GeneralWherePhysicalNominal319 (refinement nominal_old nominal_new)
open GeneralWherePhysicalDeferred319 (deferred noAdded)
open GeneralNominalRefinements (renameDescriptor)
open GeneralNormalizedObservation (Head Shape Snapshot Rewrites)
open Core.PresenceGeneration (TyTerm)
open GeneralSourceState (equationAtoms)
open PresenceNormalForm (Atom)
open GeneralNominalState (State Models)
open GeneralNominalCommonBridge (Assignment)

abbrev shapes (k : Fin 2) : Shape := if k = 0 then .record [] else .variant 0

abbrev heads (i : Fin 8) : Head shapes 8 :=
  if i = oldTwo then .structural 0 Fin.elim0
  else if i = oldLo then .structural 1 (fun _ => oldFour)
  else if i = upperSlot ∨ i = lowerSlot then .structural 1 (fun _ => oldTwo)
  else .deferred .unresolved

theorem recorded_two : (raw.base.heads oldTwo).equation = some .emptyRecord := by
  change (GeneralWherePhysicalBase319.heads finalLayout (old 1 two)).equation = _
  rw [head_old]
  change Option.map (fun t => t.rename (old 1)) ((GeneralWherePhysicalBase319.heads layout (old 2 (2 : Fin 5))).equation) = _
  rw [head_old]
  rfl

theorem old_eqs (operand : Fin 7) (slot : Fin 7)
    (found : ∀ a ∈ equationAtoms slot (.variant 0 (.var operand)), a ∈ extra) :
    Rewrites raw.base (.var (old 1 slot)) (.variant 0 (.var (old 1 operand))) := by
  refine .ordinary ?_ ?_
  · apply List.mem_append_left
    exact List.mem_map.mpr ⟨.tyLe (.var slot) (.variant 0 (.var operand)),
      List.mem_append_right _ (found _ List.mem_cons_self),rfl⟩
  · apply List.mem_append_left
    exact List.mem_map.mpr ⟨.tyLe (.variant 0 (.var operand)) (.var slot),
      List.mem_append_right _ (found _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))),rfl⟩

theorem lower_shape : Rewrites raw.base (.var lowerSlot) (.variant 0 (.var oldTwo)) :=
  .ordinary (List.mem_append_right _ List.mem_cons_self)
    (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))

theorem upper_shape : Rewrites raw.base (.var upperSlot) (.variant 0 (.var oldTwo)) :=
  old_eqs two savedHi (fun _ h => List.mem_append_right _ h)

theorem archived_shape : Rewrites raw.base (.var oldLo) (.variant 0 (.var oldFour)) :=
  old_eqs four firstLo (fun _ h => List.mem_append_left _ h)

noncomputable def view : Snapshot raw.base where
  kinds := 2
  shapes := shapes
  shapes_injective := by
    intro a b h
    have c (i : Fin 2) : i = 0 ∨ i = 1 := by omega
    rcases c a with rfl|rfl <;> rcases c b with rfl|rfl
    · rfl
    · cases h
    · cases h
    · rfl
  canonical := by
    intro k
    change (if k = 0 then Shape.record [] else Shape.variant 0).Canonical
    split <;> first | exact List.Pairwise.nil | trivial
  heads := heads
  checked := by
    intro i term found
    unfold heads at found
    split at found
    · rename_i same
      subst i
      have eq : TyTerm.emptyRecord = term := Option.some.inj found
      subst term; exact .head recorded_two
    · split at found
      · rename_i same
        subst i
        have eq : TyTerm.variant 0 (.var oldFour) = term := Option.some.inj found
        subst term; exact archived_shape
      · split at found
        · rename_i either
          have eq : TyTerm.variant 0 (.var oldTwo) = term := Option.some.inj found
          subst term
          rcases either with rfl|rfl
          · exact upper_shape
          · exact lower_shape
        · cases found

theorem nominal_origin {i : Fin 8} {d} (found : raw.nominals i = some d) :
    i = old 1 (old 2 (0 : Fin 5)) ∨ i = old 1 (old 2 (1 : Fin 5)) := by
  refine Fin.addCases (m := 7) (n := 1) (fun j h => ?_) (fun j h => ?_) i found
  · change GeneralWherePhysicalNominal319.nominals point 1 (old 1 j) = _ at h
    rw [nominal_old] at h
    revert h
    refine Fin.addCases (m := 5) (n := 2) (fun k h => ?_) (fun k h => ?_) j
    · change (GeneralWherePhysicalNominal319.nominals pointSnapshot 2 (old 2 k)).map _ = _ at h
      rw [nominal_old] at h
      change ((if k = 0 ∨ k = 1 then some exactCopy else none).map _).map _ = some d at h
      by_cases z : k = 0
      · exact .inl (congrArg (fun j : Fin 5 => old 1 (old 2 j)) z)
      · by_cases o : k = 1
        · exact .inr (congrArg (fun j : Fin 5 => old 1 (old 2 j)) o)
        · simp [z,o] at h
    · change (GeneralWherePhysicalNominal319.nominals pointSnapshot 2 (new 5 k)).map _ = _ at h
      rw [nominal_new] at h
      cases h
  · change GeneralWherePhysicalNominal319.nominals point 1 (new point.base.slots j) = _ at h
    rw [nominal_new] at h
    cases h

theorem opaque_heads (i : Fin raw.base.slots) (d : GeneralNominalState.Descriptor raw.base.slots)
    (stored : raw.nominals i = some d) : view.heads i = .deferred .unresolved := by
  rcases nominal_origin stored with rfl|rfl <;> rfl

noncomputable def active : State :=
  { raw with view := view, bodies_opaque := opaque_heads }

noncomputable abbrev ctx : GeneralNominalCandidates.Context := ⟨active,interpretation⟩

theorem active_models (m : Assignment) : Models active m ↔ Models raw m := Iff.rfl

abbrev embed (i : Fin 7) : Fin 8 := old 1 i

noncomputable def refines : GeneralNominalRefinements.Refines point active where
  base := (refinement point finalLayout newAtoms (deferred point 1) (noAdded (s := point) finalLayout newAtoms)).base
  heads := (refinement point finalLayout newAtoms (deferred point 1) (noAdded (s := point) finalLayout newAtoms)).heads
  nominals := (refinement point finalLayout newAtoms (deferred point 1) (noAdded (s := point) finalLayout newAtoms)).nominals
  ordinary := fun _ h => h
  known := by
    intro id
    rintro ⟨i,src,prior|⟨d,found⟩⟩
    · have was : i = two := by
        revert prior
        refine Fin.addCases (m := 5) (n := 2) (fun j h => ?_) (fun j h => ?_) i
        · by_cases two' : j = 2
          · exact congrArg (old 2) two'
          · have bad : point.view.graph (old 2 j) = .unresolved := by
              unfold GeneralNormalizedObservation.Snapshot.graph
              change (Fin.addCases (motive := fun _ => Head pointSnapshot.view.shapes 7)
                (fun k => GeneralWherePhysicalView319.head (old 2) (pointSnapshot.view.heads k))
                (deferred pointSnapshot 2) (old 2 j)).node = _
              rw [Fin.addCases_left]
              have oldDeferred : pointSnapshot.view.heads j = .deferred .unresolved := by
                change (if j = 2 then _ else _) = _
                simp [two']
              rw [oldDeferred]; rfl
            exact False.elim (h bad)
        · apply False.elim (h ?_)
          unfold GeneralNormalizedObservation.Snapshot.graph
          change (Fin.addCases (motive := fun _ => Head pointSnapshot.view.shapes 7)
            (fun k => GeneralWherePhysicalView319.head (old 2) (pointSnapshot.view.heads k))
            (deferred pointSnapshot 2) (new 5 j)).node = _
          rw [Fin.addCases_right]
          rfl
      subst i
      exact ⟨oldTwo,(GeneralWherePhysicalBase319.source_old finalLayout two).trans src,.inl (by decide +kernel)⟩
    · exact ⟨embed i,(GeneralWherePhysicalBase319.source_old finalLayout i).trans src,.inr ⟨_,
        (refinement point finalLayout newAtoms (deferred point 1) (noAdded (s := point) finalLayout newAtoms)).nominals i d found⟩⟩
  reserved := fun _ h => h
  allocated := fun _ h => h
  seed := rfl
  constructors := rfl

end Yulang.GeneralWherePhysicalActive319
