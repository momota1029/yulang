import Yulang.GeneralDeclarativeI65I74NativeProducerGrammar465
import Yulang.GeneralDeclarativeI65I74InlineStructuralPolicy458
import Yulang.GeneralDeclarativeI65NativePrefix369

namespace Yulang.GeneralDeclarativeI65.I72.NativeProducer465.InlineBoundary
open Yulang.GeneralDeclarativeI65 (State Origin OriginRoute originalOfWrite)
open Yulang.GeneralDeclarativeI65.I72
open Yulang.GeneralDeclarativeI65.I72.NativeProducer465
open Yulang.GeneralDeclarativeHead320 (Equation)
open Yulang.GeneralDeclarativeI65.I72.RecordTraversal455.MixedQA (Address)
open Yulang.GeneralDeclarativeWitnessNativeValue360 (Write Code)
open Yulang.GeneralDeclarativeWitnessNativeOrder362 (node)
open Yulang.Core.PresenceGeneration (TyTerm)

/-- This describes the existing inline lanes only; named paths are not excluded. -/
def NeedsInlinePayload (s : Yulang.GeneralDeclarativeI65.State) (child : Nat) : Prop :=
  ∃ payload ∈ s.origins, OriginRoute s payload child ∧
    ∃ term : TyTerm Nat, (∀ n, term ≠ .var n) ∧ payload.endpoint = .ordinary term

theorem inline_variant_policy_needs_stored_nonvariable (s : Yulang.GeneralDeclarativeI65.State) (root : Nat) (row : Equation)
    (a : Address) (c : Nat) (h : VariantInlinePolicy458.allows s root row a c true) :
    NeedsInlinePayload s c := by
  obtain ⟨tag,child,term,_,nonvar,raw,p,pm,o,om,pr,slot,route,alias,issuer,pShape,oShape⟩ := h.2
  have place := h.1
  unfold VariantInlinePolicy458.variantAt at place
  obtain ⟨key,addr,eq⟩ := place
  rw [raw] at eq
  cases eq
  exact ⟨o,om,route,term,nonvar,oShape⟩

theorem actual_new_inline_lanes_need_stored_nonvariable (s : Yulang.GeneralDeclarativeI65.State) (root : Nat) (row : Equation)
    (a : Address) (c : Nat) (h : InlineStructuralPolicy458.NewAuthority s root row a c) :
    NeedsInlinePayload s c := by
  rcases h with pair | record | nominal
  · obtain ⟨_,p,pm,o,om,t,known,scopeOK,nonvar,pr,slot,route,alias,issuer,ep⟩ := pair
    exact ⟨o,om,route,t,nonvar,ep⟩
  · obtain ⟨l,la,words,t,src,raw,counts,fields,labels,placed,atSrc,nonvar,
      p,pm,o,om,slot,pr,route,issuer,alias,pep,oep⟩ := record
    exact ⟨o,om,route,t,nonvar,oep⟩
  · obtain ⟨key,t,atAddr,raw,mode,scopeOK,nonvar,p,pm,o,om,slot,pr,route,alias,issuer,pep,oep⟩ := nominal
    exact ⟨o,om,route,t,nonvar,oep⟩

theorem a_real_inline_step_needs_an_origin_outside_all_native360_writes
    (s : Yulang.GeneralDeclarativeI65.State) (root : Nat) (row : Equation) (a : Address) (c : Nat)
    (h : VariantInlinePolicy458.allows s root row a c true ∨
      InlineStructuralPolicy458.NewAuthority s root row a c) :
    ∃ o ∈ s.origins, OriginRoute s o c ∧ ∀ w : Write, originalOfWrite w ≠ o := by
  have original := h.elim
    (inline_variant_policy_needs_stored_nonvariable s root row a c)
    (actual_new_inline_lanes_need_stored_nonvariable s root row a c)
  obtain ⟨o,hits,route,t,shape,atOrig⟩ := original
  refine ⟨o,hits,route,fun w same => ?_⟩
  have endpoint : node w.code = .ordinary t := (congrArg Origin.endpoint same).trans atOrig
  exact concrete_nonvariable_ordinary_source_is_never_native360_emission w.code t shape endpoint

theorem a_state_whose_entire_origin_list_is_emitted_by_native360_cannot_enter_inline_lanes
    (s : Yulang.GeneralDeclarativeI65.State) (root : Nat) (row : Equation) (a : Address) (c : Nat)
    (fromOnlyOldCompiler : ∀ o ∈ s.origins, ∃ w : Write, originalOfWrite w = o) :
    ¬ (VariantInlinePolicy458.allows s root row a c true ∨
      InlineStructuralPolicy458.NewAuthority s root row a c) := by
  intro why
  obtain ⟨o,atOrig,_,absent⟩ := a_real_inline_step_needs_an_origin_outside_all_native360_writes s root row a c why
  obtain ⟨w,physical⟩ := fromOnlyOldCompiler o atOrig
  exact absent w physical

end Yulang.GeneralDeclarativeI65.I72.NativeProducer465.InlineBoundary
