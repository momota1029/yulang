import Yulang.GeneralWhereOriginActualShift318
import Yulang.GeneralWhereOriginBatch318

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 31000
set_option maxHeartbeats 36000000
namespace Yulang.GeneralWhereOriginSingleSource318
open GeneralDeclarations GeneralDeclarationPatterns
open GeneralDictionaryJournalRefinement228Source (roles root snapshot context constructors interpretation)
open GeneralLiveCompoundRegistry316 (otherChild leaf)
open GeneralNominalCenters
open GeneralNominalSaturationState (Packet)

-- Only the fixture changes: the second nominal parameter gets a distinct
-- source binder. No core declarations, checking rules or inference change.
abbrev declaration : Declaration := { GeneralLiveCompoundRegistry316.declaration with
  head := [.app 0 [.var 0,.var 1]] }

abbrev sourceRegistry : Registry := ⟨constructors,roles,[declaration,leaf]⟩
abbrev registry := GeneralNominalCenteredHeadAllocEncoding.registry sourceRegistry

theorem declaration_checked : DeclarationChecked constructors roles declaration := by
  constructor
  · simp [Declaration.Signature,Clause.Signature,Declared]
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,normalizeArgs,normalize,GeneralDictionaryOptionalExpression229.pattern,
      variablesArgs,Pattern.variables,merge,hide,variantRow]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors,GeneralDictionaryOptionalExpression229.pattern]
  · intro clause member; cases List.mem_singleton.mp member; exact ⟨rfl,rfl⟩
  · intro clause member; cases List.mem_singleton.mp member
    exact (checkSmaller_exact _ _).mp (by decide +kernel)
  · intro clause member; cases List.mem_singleton.mp member
    unfold ConservativeSmaller; decide +kernel
  · intro clause member captures; cases List.mem_singleton.mp member
    constructor
    · simp [counted,substArgs,Pattern.subst,normalizeArgs,normalize,encodeArgs,Pattern.encode,Roles.argsSize,Roles.Term.size]
      exact Roles.Term.size_pos _
    · intro name
      simp [counted,substArgs,Pattern.subst,normalizeArgs,normalize,encodeArgs,Pattern.encode,Roles.argsOccurrences,Roles.Term.occurrences]

theorem checked : Checked sourceRegistry := ⟨by decide +kernel,by
  intro d member
  rcases List.mem_cons.mp member with h|rest
  · cases h; exact declaration_checked
  · cases List.mem_singleton.mp rest
    exact GeneralLiveCompoundRegistry316.leaf_checked⟩

theorem boundary_checked :
    (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Checked sourceRegistry :=
  ⟨rfl,checked⟩

abbrev older : Packet roles :=
  ⟨registry,context,GeneralNominalDemandMerging.pointSite root,declaration,declaration_checked,[(0,0)]⟩
noncomputable abbrev newer : Packet roles :=
  ⟨registry,GeneralLiveCompoundUpperSnapshot316.context,GeneralNominalDemandMerging.pointSite root,
    declaration,declaration_checked,[(0,0)]⟩
abbrev oldPlan : Plan roles := ⟨older,rootSite snapshot.seed root,rfl⟩
noncomputable abbrev newPlan : Plan roles := ⟨newer,rootSite snapshot.seed root,rfl⟩

end Yulang.GeneralWhereOriginSingleSource318
