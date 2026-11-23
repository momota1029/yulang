import Yulang.GeneralDeclarativeWitnessSparseVariance357
namespace Yulang.GeneralDeclarativeWitnessVarianceFixtures357
open GeneralDeclarativeWitnessSparseVariance357 (Source Header Made compile lookup)

def source : Source 3 2 0 :=
  ⟨[⟨20,[(.value,0)]⟩,⟨42,[(.value,1)]⟩,⟨90,[]⟩],
    fun i => if i.val = 0 then .parameter 0 else
      if i.val = 1 then .arrow (.inr 1) .empty (.inl 2) .empty else .base .int,
    fun p => if p.val = 0 then 0 else 1⟩

def inspect (s : Source 3 2 0) (name : Nat) :=
  (compile s).bind (fun checked => lookup checked name)

theorem actual_box_covariant : inspect source 20 = some [⟨.value,.covariant⟩] := by
  decide +kernel

theorem actual_arrow_param_contravariant : inspect source 42 = some [⟨.value,.contravariant⟩] := by
  decide +kernel

theorem real_nullary : inspect source 90 = some [] := by decide +kernel

theorem no_dense_filler : inspect source 21 = none := by decide +kernel

theorem reject_unowned_formal :
    (compile {source with headers := ⟨92,[(.value,0)]⟩ :: source.headers}).isSome = false := by
  decide +kernel

theorem reject_wrong_declared_kind :
    (compile {source with headers := [⟨20,[(.row,0)]⟩,⟨42,[(.value,1)]⟩]}).isSome = false := by
  decide +kernel

def withCall (id : Nat) : Source 3 2 0 :=
  {source with bodies := fun i => if i.val = 2 then .nominal id [] else source.bodies i}

theorem true_nullary_call : (compile (withCall 90)).isSome = true := by decide +kernel

theorem absent_call_does_not_lower : (compile (withCall 21)).isSome = false := by decide +kernel

end Yulang.GeneralDeclarativeWitnessVarianceFixtures357
