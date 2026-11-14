import Yulang.GeneralDictionaryNominalSharedDiscovery179
import Yulang.GeneralNominalExamples

/-! Two occurrences of one binder pass actual nonpoint inspection. This is a
shape-discovery regression, not an unrestricted evidence or installation test. -/
namespace Yulang.GeneralDictionaryNominalSharedDiscoveryExample179
open GeneralDeclarations GeneralDeclarationPatterns GeneralNominalRecursiveInspection GeneralNominalRecursiveCandidates
abbrev base : GeneralSourceState.State where
  slots := 4
  source := Fin.val
  source_injective := fun _ _ h => Fin.ext h
  rowSource := Fin.val
  ordinary := []
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro i; exact Fin.elim0 i
  heads := fun _ => .unresolved
  intervals := []
  heads_sound := by intro _ _ _ _ h; cases h
  intervals_sound := by intro _ _ _ h; cases h
abbrev view : GeneralNormalizedObservation.Snapshot base where
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro i; exact Fin.elim0 i
  canonical := by intro i; exact Fin.elim0 i
  heads := fun _ => .deferred .unresolved
  checked := by intro _ _ h; cases h
abbrev descriptor : GeneralNominalState.Descriptor 4 := ⟨0,⟨[.type,.type],0⟩,[.type (2,3),.type (2,3)],rfl⟩
abbrev state : GeneralNominalState.State where
  base := base
  view := view
  constructors := fun _ => some ⟨[.type,.type],0⟩
  nominals := fun i => if i.val < 2 then some descriptor else none
  catalogue := by intro i d h; split at h; cases Option.some.inj h; rfl; cases h
  bodies_opaque := by intro _ _ _; rfl
abbrev context : Context := ⟨state,GeneralNominalExamples.interpretation⟩
abbrev declaration : Declaration := ⟨1,0,[.app 0 [.var 0,.var 0]],[],[],[]⟩

abbrev names : Fin 2 → Nat := fun _ => 0

theorem repeated_names : ¬ Function.Injective names := by
  intro h
  have same := h (a₁ := (0 : Fin 2)) (a₂ := (1 : Fin 2)) rfl
  have values := congrArg Fin.val same
  cases values

theorem query_exact : GeneralNominalInspection.queries context.state context.interpretation declaration =
    [.nominal 0 (List.ofFn fun i => .variables [names i])] := by
  simp [GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,
    GeneralNominalInspection.translate,GeneralNominalExamples.interpretation,List.ofFn_succ,names]

theorem inspection_finished : Finished (report context declaration [(0,1)]) := by
  unfold Finished
  decide +kernel

theorem shape_recovered : ∃ shape : GeneralDictionaryNominalPairShared178.SharedShape context declaration,
    shape.lower = 0 ∧ shape.upper = 1 ∧ shape.left.declaration.name = 0 ∧
      shape.n = 2 ∧ HEq shape.names names :=
  GeneralDictionaryNominalSharedDiscovery179.shared_shape_exists context declaration 0 1
    (by decide +kernel) 0 names query_exact inspection_finished

end Yulang.GeneralDictionaryNominalSharedDiscoveryExample179
