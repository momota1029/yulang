import Yulang.GeneralRebaseRegistryEvidence277
import Yulang.GeneralRebaseMixedOwnedTrace277

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseRegistryDiagnostics277
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Models)
open GeneralRebaseRegistrySurface277 (Surface symmetric prepared survivor inspectionPending)
open GeneralRebaseRegistryEvidence277 (frame body_schema body_holds)
open GeneralRebaseCompiledRetag277 (retag)
open GeneralNominalVersionedCycles232 (RawCandidateK2 CandidateCycle)
open GeneralNominalVersionedDiagnostic232 (boundary v6 v7 AdministrativeReady HeadEquations)
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls} {a b : Registry} {s : State roles} {root : Occurrence roles}

abbrev On (a b : Registry) (s : State roles) (root : Occurrence roles) :=
  Surface a b s.core.erased.current.context root

theorem surface_of_covered (held : GeneralRebaseOwnedSupport277.Covered s.core.erased.current.context.state)
    (ctors : a.constructors = b.constructors)
    (roster : ∀ d : Declaration, d.role = root.demand.role → (d ∈ a.declarations ↔ d ∈ b.declarations)) :
    On a b s root :=
  ⟨ctors,roster,fun _ _ _ => ⟨fun _ => GeneralRebaseOwnedSupport277.allFresh held _ _ _,
    fun _ => GeneralRebaseOwnedSupport277.allFresh held _ _ _⟩⟩

theorem raw_k2_forward (surface : On a b s root)
    (given : RawCandidateK2 a s.core.erased.current.context (GeneralNominalVersionedCandidates231.inputs root)) :
    RawCandidateK2 b s.core.erased.current.context (GeneralNominalVersionedCandidates231.inputs root) := by
  obtain ⟨head,d,visible,checked,role,ready,bs,located,pos,inside,cycle⟩ := given
  have sameRole : d.role = root.demand.role := role
  have atRoot := (GeneralNominalVersionedCandidates231.prepared_ignores_outputs
    (registry := a) (first := GeneralNominalVersionedCandidates231.inputs root) (last := root) rfl).mp ready
  have atOther := (prepared surface sameRole).mp atRoot
  have inputOnly := (GeneralNominalVersionedCandidates231.prepared_ignores_outputs
    (registry := b) (first := GeneralNominalVersionedCandidates231.inputs root) (last := root) rfl).mpr atOther
  exact ⟨head,d,(surface.visible d sameRole).mp visible,surface.constructors ▸ checked,role,inputOnly,
    bs,located,pos,inside,cycle⟩

theorem cycle_forward (surface : On a b s root) (given : CandidateCycle a s root) : CandidateCycle b s root := by
  obtain ⟨p,atFrame,entry,seen,cyclic⟩ := given
  let ct := surface.constructors.symm.trans (congrArg Registry.constructors atFrame.registry_eq).symm
  exact ⟨retag p b ct,frame surface atFrame,entry,seen,cyclic⟩

theorem k2 (surface : On a b s root) :
    (boundary roles).CandidateK2 a s root ↔ (boundary roles).CandidateK2 b s root := by
  change (RawCandidateK2 a _ _ ∨ CandidateCycle a s root) ↔
   (RawCandidateK2 b _ _ ∨ CandidateCycle b s root)
  exact or_congr ⟨raw_k2_forward surface,raw_k2_forward (symmetric surface)⟩
    ⟨cycle_forward surface,cycle_forward (symmetric surface)⟩

theorem inspection (surface : On a b s root) :
    (boundary roles).InspectionPending a s root ↔ (boundary roles).InspectionPending b s root := by
  change (_ ∨ ¬ AdministrativeReady s root) ↔ (_ ∨ ¬ AdministrativeReady s root)
  exact or_congr (inspectionPending surface) Iff.rfl

theorem survivor_iff (surface : On a b s root) (key : Nat) (kids : List (Occurrence roles)) :
    (boundary roles).Survivor a s root key kids ↔ (boundary roles).Survivor b s root key kids :=
  survivor surface

theorem ready (p : Plan roles) (r : Registry) (ctors) :
    GeneralNominalCenteredHeadMatEffects.Ready s.core root (retag p r ctors) ↔
      GeneralNominalCenteredHeadMatEffects.Ready s.core root p := by
  unfold GeneralNominalCenteredHeadMatEffects.Ready
  simp only [body_schema]
  rfl

theorem effects (p : Plan roles) (r : Registry) (ctors) (m : Assignment) :
    GeneralNominalVersionedEffects231.ClassEffects s.core root (retag p r ctors) m ↔
      GeneralNominalVersionedEffects231.ClassEffects s.core root p m := by
  rw [GeneralNominalVersionedEffects231.class_effects_iff,GeneralNominalVersionedEffects231.class_effects_iff]
  unfold GeneralNominalCenteredHeadMatEffects.ClassEffects
  simp only [body_holds]
  rfl

theorem chosen_head_forward (surface : On a b s root) (m : Assignment) (key : Nat)
    (given : GeneralNominalVersionedDiagnostic232.ChosenHead a s root key m) :
    GeneralNominalVersionedDiagnostic232.ChosenHead b s root key m := by
  obtain ⟨⟨kids,unique⟩,p,hasFrame,compiled,head⟩ := given
  refine ⟨⟨kids,(GeneralRebaseRegistrySurface277.unique surface).mp unique⟩,_,frame surface hasFrame,?_,head⟩
  exact (ready p b _).mpr compiled

theorem chosen_effects_forward (surface : On a b s root) (m : Assignment) (key : Nat)
    (given : GeneralNominalVersionedDiagnostic232.ChosenEffects a s root key m) :
    GeneralNominalVersionedDiagnostic232.ChosenEffects b s root key m := by
  obtain ⟨⟨kids,unique⟩,p,hasFrame,compiled,head,held⟩ := given
  refine ⟨⟨kids,(GeneralRebaseRegistrySurface277.unique surface).mp unique⟩,_,frame surface hasFrame,?_,head,?_⟩
  · exact (ready p b _).mpr compiled
  · exact (effects p b _ m).mpr held

theorem output_conflict (surface : On a b s root) (key : Nat) :
    (boundary roles).OutputConflict a s root key ↔ (boundary roles).OutputConflict b s root key := by
  change GeneralNominalVersionedDiagnostic232.OutputConflict a s root key ↔
    GeneralNominalVersionedDiagnostic232.OutputConflict b s root key
  have heads : ∀ m, GeneralNominalVersionedDiagnostic232.ChosenHead a s root key m ↔
      GeneralNominalVersionedDiagnostic232.ChosenHead b s root key m := fun m =>
    ⟨chosen_head_forward surface m key,chosen_head_forward (symmetric surface) m key⟩
  have bodies : ∀ m, GeneralNominalVersionedDiagnostic232.ChosenEffects a s root key m ↔
      GeneralNominalVersionedDiagnostic232.ChosenEffects b s root key m := fun m =>
    ⟨chosen_effects_forward surface m key,chosen_effects_forward (symmetric surface) m key⟩
  unfold GeneralNominalVersionedDiagnostic232.OutputConflict
  simp only [heads,bodies]

theorem feasible_forward (surface : On a b s root) (key : Nat)
    (given : GeneralNominalVersionedDiagnostic232.Feasible a s root key) :
    GeneralNominalVersionedDiagnostic232.Feasible b s root key := by
  obtain ⟨m,valid,p,hasFrame,held⟩ := given
  exact ⟨m,valid,_,frame surface hasFrame,held⟩

theorem at_key_forward (surface : On a b s root) (key : Nat)
    (given : GeneralNominalVersionedDiagnostic232.AtKey a s root key) :
    GeneralNominalVersionedDiagnostic232.AtKey b s root key := by
  obtain ⟨inhabited,⟨p,hasFrame⟩,bad⟩ := given
  exact ⟨inhabited,⟨_,frame surface hasFrame⟩,fun witness =>
    bad (feasible_forward (symmetric surface) key witness)⟩

end Yulang.GeneralRebaseRegistryDiagnostics277
