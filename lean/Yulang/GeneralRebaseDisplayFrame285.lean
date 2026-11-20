import Yulang.GeneralRebaseDisplayEvidenceWatch284
import Yulang.GeneralRebaseDepthMinimal285

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 22000
set_option maxHeartbeats 8500000
namespace Yulang.GeneralRebaseDisplayFrame285
open GeneralNominalExamples (state listDescriptor heads base displayRoot displayChild)
open GeneralNominalVersionedJournal232 (Models)
open GeneralRebaseCompiledDisplay277 (after compiled)
open GeneralNominalVersionedEvidence231 (Evidence)
open CommonNominalFullCarrier (Equivalent nominal subtype_refl)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)

abbrev S : CommonNominalFullCarrier.Ty := .base .int
abbrev L := nominal 0 [.inl S]

def TypeCheck (m : Assignment) : Prop := Equivalent (m 1).1 S ∧ Equivalent (m 0).1 L

theorem source_check (m : Assignment) : GeneralNominalState.Models (state true) m ↔ TypeCheck m := by
  constructor
  · intro holds
    have one : Equivalent (m 1).1 S := ⟨holds.1.1 _ List.mem_cons_self,
      holds.1.1 _ (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    have zero := (GeneralNominalState.denotes_singleton_exact (base true) m (0 : Fin 2) 1 listDescriptor rfl).mp
      (holds.2.1 (0 : Fin 2) listDescriptor rfl)
    have lifted := GeneralNominalState.singleton_nominal_congr 0 (m 1).1 S one
    exact ⟨one,⟨CommonNominalFullCarrier.subtype_trans zero.1 lifted.1,
      CommonNominalFullCarrier.subtype_trans lifted.2 zero.2⟩⟩
  · rintro ⟨one,zero⟩
    refine ⟨⟨?_,?_,?_⟩,?_,by simp [PresenceNormalForm.All]⟩
    · intro atom presence
      change atom ∈ GeneralSourceState.equationAtoms (1 : Fin 2) (.base .int) at presence
      simp only [GeneralSourceState.equationAtoms,List.mem_cons,List.not_mem_nil,or_false] at presence
      rcases presence with rfl|rfl
      · exact one.1
      · exact one.2
    · intro slot t h
      by_cases yes : slot = 1
      · subst slot
        have equal : (.base .int : Core.PresenceGeneration.TyTerm (Fin 2)) = t := by
          simpa [heads,GeneralSourceState.Head.equation] using h
        subst t
        exact one
      · simp [heads,yes,GeneralSourceState.Head.equation] at h
    · intro pair member
      simp only [base,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl <;> exact subtype_refl _
    · intro slot descriptor present
      by_cases yes : slot = 0
      · subst slot
        have equal : listDescriptor = descriptor := Option.some.inj present
        subst descriptor
        exact ⟨[.inl S],.cons one .nil,zero⟩
      · simp [state,yes] at present

theorem final_check (m : Assignment) : Models after m ↔ TypeCheck m :=
 (GeneralRebaseCompiledInstall277.models m).trans
   ((GeneralRebaseDisplayExecutor276.model_exact .source m).trans (source_check m))

theorem parent_exact (m : Assignment) (p : Payload) :
    Models after m ∧ Evidence compiled after.core m displayRoot p ↔
      TypeCheck m ∧ p = .node 1 [.node 3 []] := by
  constructor
  · rintro ⟨held,ev⟩
    exact ⟨(final_check m).mp held,GeneralRebaseCompiledPayload277.parent_shape _ _ ev⟩
  · rintro ⟨checked,rfl⟩
    have held := (final_check m).mpr checked
    exact ⟨held,GeneralRebaseCompiledEvidence277.real_nonleaf _ held⟩

theorem child_exact (m : Assignment) (p : Payload) :
    Models after m ∧ Evidence compiled after.core m displayChild p ↔
      TypeCheck m ∧ p = .node 3 [] := by
  constructor
  · rintro ⟨held,ev⟩
    exact ⟨(final_check m).mp held,GeneralRebaseCompiledPayload277.child_shape _ _ ev⟩
  · rintro ⟨checked,rfl⟩
    have held := (final_check m).mpr checked
    exact ⟨held,GeneralRebaseCompiledEvidence277.child_evidence _ held⟩

theorem parent_finite (p : Payload) :
    GeneralRebaseDepthMinimal285.Frames
      (fun m => Models after m ∧ Evidence compiled after.core m displayRoot p) [0,1] := by
  intro a b same
  change (Models after a ∧ Evidence compiled after.core a displayRoot p) ↔
    (Models after b ∧ Evidence compiled after.core b displayRoot p)
  rw [parent_exact,parent_exact]
  simp only [TypeCheck,same 0 (by decide),same 1 (by decide)]

theorem child_finite (p : Payload) :
    GeneralRebaseDepthMinimal285.Frames
      (fun m => Models after m ∧ Evidence compiled after.core m displayChild p) [0,1] := by
  intro a b same
  change (Models after a ∧ Evidence compiled after.core a displayChild p) ↔
    (Models after b ∧ Evidence compiled after.core b displayChild p)
  rw [child_exact,child_exact]
  simp only [TypeCheck,same 0 (by decide),same 1 (by decide)]

end Yulang.GeneralRebaseDisplayFrame285
