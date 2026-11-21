import Yulang.GeneralWhereVersionWitness317

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29000
set_option maxHeartbeats 32000000
namespace Yulang.GeneralWhereVersionSnapshot317
open GeneralWhereVersionBase317
open GeneralWhereVersionCase317 (lower upper)
open GeneralDictionaryJournalRefinement228Source (constructors interpretation)
open GeneralLiveCompoundUpperSnapshot316 (desc)
open GeneralLiveCompoundPost316 (raw)
open GeneralNominalCommonBridge (Assignment)
open GeneralSourceState (equationAtoms equationAtoms_exact)
open Core.PresenceGeneration (TyTerm)
open CommonNominalFullCarrier

abbrev viewHeads (i : Fin 10) :
    GeneralNormalizedObservation.Head GeneralDictionaryCompoundBase239.viewShapes 10 :=
  if i = two ∨ i = seven then .structural 0 Fin.elim0 else
  if i = five then .structural 1 (fun _ => injectOld 4) else
  if i = six ∨ i = loSlot ∨ i = hiSlot then .structural 1 (fun _ => two) else .deferred .unresolved

noncomputable def view : GeneralNormalizedObservation.Snapshot base where
  kinds := 2
  shapes := GeneralDictionaryCompoundBase239.viewShapes
  shapes_injective := GeneralMixedCompoundUpperBase307.view.shapes_injective
  canonical := GeneralMixedCompoundUpperBase307.view.canonical
  heads := viewHeads
  checked := by
    intro i term found
    by_cases empty : i = two ∨ i = seven
    · rcases empty with rfl|rfl <;>
        have eq : term = .emptyRecord := Option.some.inj found.symm <;> subst term <;> exact .head rfl
    · by_cases isFive : i = five
      · subst i
        have eq : term = .variant 0 (.var (injectOld 4)) := Option.some.inj found.symm
        subst term; exact .head rfl
      · by_cases isPoint : i = six ∨ i = loSlot ∨ i = hiSlot
        · rcases isPoint with rfl|rfl|rfl <;>
            have eq : term = endpointTerm := Option.some.inj found.symm <;> subst term <;> exact .head rfl
        · simp [viewHeads,empty,isFive,isPoint,GeneralNormalizedObservation.Head.term,
            GeneralNormalizedObservation.Deferred.term] at found

abbrev zero : Fin 10 := injectOld 0
abbrev one : Fin 10 := injectOld 1
abbrev nextDesc : GeneralNominalState.Descriptor 10 := GeneralNominalRefinements.renameDescriptor injectOld desc

noncomputable def snap : GeneralNominalState.State where
  base := base
  view := view
  constructors := constructors
  nominals := fun i => if i = zero ∨ i = one then some nextDesc else none
  catalogue := by
    intro i d found
    split at found
    · cases Option.some.inj found; rfl
    · cases found
  bodies_opaque := by
    intro i d found
    split at found
    · rename_i b
      rcases b with rfl|rfl <;> rfl
    · cases found
  allocated := raw.allocated
  reserved := raw.reserved
  ordinary := raw.ordinary
  seed := raw.seed

noncomputable abbrev context : GeneralNominalCandidates.Context := ⟨snap,interpretation⟩

theorem base_heads (i : Fin 8) :
    (base.heads (injectOld i)).equation =
      (GeneralMixedCompoundUpperBase307.base.heads i).equation.map (fun t => t.rename injectOld) := by
  revert i
  decide +kernel

theorem sub_assignment (m : Assignment) :
    GeneralNominalCommonBridge.assignment base m ∘ injectOld =
      GeneralNominalCommonBridge.assignment raw.base m := by
  funext i
  change ((m (source (injectOld i))).1,(m (source (injectOld i))).2) =
    ((m (GeneralMixedCompoundUpperBase307.source i)).1,(m (GeneralMixedCompoundUpperBase307.source i)).2)
  rw [source_old]

abbrev oldTwo : Fin 8 := 2

theorem constrained (m : Assignment) (old : GeneralNominalState.Models raw m)
    (first : Equivalent (m lower).1 (variant 0 (m 2).1)) (last : Equivalent (m upper).1 (variant 0 (m 2).1)) :
    GeneralNominalState.Models snap m := by
  have original : GeneralNominalCommonBridge.Models raw.base m := old.1
  refine ⟨⟨?_,?_,fun _ h => nomatch h⟩,?_,old.2.2⟩
  · apply (PresenceNormalForm.all_append ..).mpr
    constructor
    · apply (PresenceNormalForm.all_append ..).mpr
      constructor
      · change PresenceNormalForm.All CommonNominalFullCarrier.model (GeneralNominalCommonBridge.assignment base m)
          (GeneralMixedCompoundUpperBase307.base.ordinary.map (PresenceNormalForm.Atom.rename injectOld))
        rw [PresenceNormalForm.all_rename,sub_assignment]
        exact original.1
      · have holds : Equivalent (m (source loSlot)).1 (variant 0 (m (source two)).1) := by
          rw [source_lo,source_old]; exact first
        intro a member
        simp only [equationAtoms,List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl|rfl
        · exact holds.1
        · exact holds.2
    · have holds : Equivalent (m (source hiSlot)).1 (variant 0 (m (source two)).1) := by
        rw [source_hi,source_old]; exact last
      intro a member
      simp only [equationAtoms,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl
      · exact holds.1
      · exact holds.2
  · intro i term found
    change Fin 10 at i
    change (base.heads i).equation = some term at found
    revert found
    refine Fin.addCases (m := 8) (n := 2) (fun j => ?_) (fun j => ?_) i
    · rw [base_heads]
      intro found
      obtain ⟨expr,stored,renamed⟩ := Option.map_eq_some_iff.mp found
      subst term
      have same := original.2.1 j expr stored
      change Equivalent (m (source (injectOld j))).1
        ((expr.rename injectOld).eval CommonNominalFullCarrier.model (GeneralNominalCommonBridge.assignment base m))
      rw [source_old,TyTerm.eval_rename,sub_assignment]
      exact same
    · rcases new_cases j with rfl|rfl
      · intro found
        have eq : term = endpointTerm := Option.some.inj found.symm
        subst term
        change Equivalent (m (source loSlot)).1 (variant 0 (m (source two)).1)
        rw [source_lo,source_old]
        exact first
      · intro found
        have eq : term = endpointTerm := Option.some.inj found.symm
        subst term
        change Equivalent (m (source hiSlot)).1 (variant 0 (m (source two)).1)
        rw [source_hi,source_old]
        exact last
  · intro i d found
    change (if i = zero ∨ i = one then some nextDesc else none) = some d at found
    split at found
    · rename_i both
      cases Option.some.inj found
      have move (values) (fits : GeneralNominalState.FitsAll raw.base m desc.arguments values) :
          GeneralNominalState.FitsAll base m nextDesc.arguments values := by
        change GeneralNominalState.FitsAll raw.base m [.type (oldTwo,oldTwo),.type (oldTwo,oldTwo)] values at fits
        change GeneralNominalState.FitsAll base m [.type (two,two),.type (two,two)] values
        have oneFits (a) (f : GeneralNominalState.Fits raw.base m (.type (oldTwo,oldTwo)) a) :
            GeneralNominalState.Fits base m (.type (two,two)) a := by
          cases a with
          | inl ty =>
            change Subtype (m (source two)).1 ty ∧ Subtype ty (m (source two)).1
            rw [source_old]; exact f
          | inr row => cases f
        cases fits with
        | cons x xs => cases xs with
          | cons y ys => cases ys; exact .cons (oneFits _ x) (.cons (oneFits _ y) .nil)
      rcases both with rfl|rfl
      · obtain ⟨args,fit,value⟩ := old.2.1 (0 : Fin 8) desc rfl
        refine ⟨args,move args fit,?_⟩
        change Equivalent (m (source zero)).1 (nominal 0 args)
        rw [source_old]; exact value
      · obtain ⟨args,fit,value⟩ := old.2.1 (1 : Fin 8) desc rfl
        refine ⟨args,move args fit,?_⟩
        change Equivalent (m (source one)).1 (nominal 0 args)
        rw [source_old]; exact value
    · cases found

end Yulang.GeneralWhereVersionSnapshot317
