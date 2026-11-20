import Yulang.GeneralObservedMetadataStrictActual290

/-! Two globally compatible primitive interpretations can still compile
different statements. Type/arity alone do not certify the scalar value. -/
namespace Yulang.GeneralObservedMetadataPrimitiveDrift290
open GeneralRebaseRowChildSource287 (raw interp constructors registry)
open GeneralNominalCandidates (Metadata)
open GeneralObservedMetadataControls290 (insertPrimitive)
open GeneralObservedMetadataScope290 (certify coverage)
open GeneralObservedMetadataReport290 (queriesFrom)
open GeneralObservedMetadataBodies290 (compileFrom)
open GeneralDeclarations (Declaration)

abbrev first := insertPrimitive interp 8 (.scalar .int)
abbrev last := insertPrimitive interp 8 (.scalar .str)
abbrev d : Declaration := ⟨42,1,[.app 8 []],[],[],[]⟩

theorem valid_scalar (base : Inference.Base) :
    Metadata (registry true) ⟨raw,insertPrimitive interp 8 (.scalar base)⟩ := by
  refine ⟨rfl,?_⟩
  intro key primitive found
  by_cases target : key = 8
  · subst key
    have matched : primitive = .scalar base := Option.some.inj found.symm
    subst primitive
    exact ⟨⟨[],8⟩,rfl,rfl⟩
  · change (if key = 8 then some (.scalar base) else (none : Option GeneralCandidateInspection.Primitive)) = _ at found
    rw [ite_eq_right target] at found
    cases found

theorem same_layout_different_query :
    queriesFrom constructors first d = [.scalar .int] ∧
    queriesFrom constructors last d = [.scalar .str] := by
  constructor <;>
    change [GeneralNominalInspection.translate _ _ (.app 8 [])] = _ <;>
    simp [GeneralNominalInspection.translate,first,last,insertPrimitive]

theorem primitive_value_matters :
    certify (coverage raw [d]) constructors first constructors last = .disagreement ∧
    Metadata (registry true) ⟨raw,first⟩ ∧ Metadata (registry true) ⟨raw,last⟩ :=
  ⟨by decide +kernel,valid_scalar .int,valid_scalar .str⟩

end Yulang.GeneralObservedMetadataPrimitiveDrift290
