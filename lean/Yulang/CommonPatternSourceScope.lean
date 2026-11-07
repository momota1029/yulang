import Yulang.CommonPatternConcreteScope
import Yulang.CoreCommonSyntaxExact
import Yulang.CoreData

/-! Actual named data elaboration commutes with the concrete prefix
permutation. The existing coverage gate is retained separately: unsupported
list/nominal forms are not accepted by proving an equality of their fallbacks. -/

namespace Yulang.CommonPatternSourceScope

open Core
open CommonPatternConcreteScope (findName reindex)
open CommonPatternBindingAlignment (lookup LookupEq)
open CommonPatternScopeRenaming (renameExpr liftIndex)

theorem resolve_bindings (name : Nat) (bindings : List (Nat × A)) :
    Data.resolve name (bindings.map Prod.fst) = (lookup name bindings).map (fun _ => findName name bindings) := by
  induction bindings with
  | nil => rfl
  | cons binding rest ih =>
      rcases binding with ⟨current, value⟩
      by_cases same : name = current
      · simp [Data.resolve, lookup, findName, same]
      · simp only [List.map_cons, Data.resolve, lookup, findName, same, ↓reduceIte, ih, Option.map_map]
        cases lookup name rest <;> rfl

theorem resolve_append (name : Nat) (initial suffix : List Nat) :
    Data.resolve name (initial ++ suffix) =
      (Data.resolve name initial).orElse (fun _ => (Data.resolve name suffix).map (initial.length + ·)) := by
  induction initial with
  | nil => simp [Data.resolve]
  | cons current rest ih =>
      by_cases same : name = current
      · simp [Data.resolve, same]
      · simp only [List.cons_append, Data.resolve, same, ↓reduceIte, List.length_cons, ih]
        cases Data.resolve name rest <;> cases Data.resolve name suffix <;> simp [Nat.add_assoc, Nat.add_comm]

def ScopeRenames (source target : List Nat) (rename : Nat → Nat) : Prop :=
  ∀ name, Data.resolve name target = (Data.resolve name source).map rename

theorem ScopeRenames.cons (same : ScopeRenames source target rename) (name : Nat) :
    ScopeRenames (name :: source) (name :: target) (liftIndex rename) := by
  intro current
  by_cases equal : current = name
  · simp [Data.resolve, equal, liftIndex]
  · simp only [Data.resolve, equal, ↓reduceIte, same current, Option.map_map]
    rfl

theorem concrete_scope (source target : List (Nat × A)) (same : LookupEq source target)
    (outer : List Nat) :
    ScopeRenames (source.map Prod.fst ++ outer) (target.map Prod.fst ++ outer) (reindex source target) := by
  intro name
  simp only [resolve_append, resolve_bindings, List.length_map]
  have equivalent := same name
  cases found : lookup name source with
  | none =>
      have absent : lookup name target = none := equivalent.symm.trans found
      simp only [absent, Option.map_none, Option.orElse_none]
      rw [Option.map_map]
      cases Data.resolve name outer with
      | none => rfl
      | some index => simp [reindex, Nat.not_lt.mpr (Nat.le_add_right _ _)]
  | some value =>
      have present : lookup name target = some value := equivalent.symm.trans found
      have located := CommonPatternConcreteScope.get_findName name source found
      obtain ⟨inside, entry⟩ := List.getElem?_eq_some_iff.mp located
      have named : (source[findName name source]).1 = name := congrArg Prod.fst entry
      simp only [present, Option.map_some, Option.orElse_some]
      simp [reindex, inside, named]

theorem rename_valueLower (value : CommonData.Value) (rename : Nat → Nat) :
    renameExpr rename (CommonData.valueLower value) = CommonData.valueLower value := by
  cases value with
  | literal => simp only [CommonData.valueLower, renameExpr]
  | pair first last =>
      simp only [CommonData.valueLower, renameExpr, rename_valueLower first, rename_valueLower last]
  | record fields =>
      cases fields with
      | nil => simp only [CommonData.valueLower, renameExpr]
      | cons field rest =>
          rcases field with ⟨name, value⟩
          have smaller : sizeOf value < sizeOf (CaseValues.Value.record ((name, value) :: rest)) := by
            simp; omega
          simp only [CommonData.valueLower, renameExpr, rename_valueLower value,
            rename_valueLower (.record rest)]
  | variant tag payload => simp only [CommonData.valueLower, renameExpr, rename_valueLower payload]
  | nominal | list => simp only [CommonData.valueLower, renameExpr]
termination_by sizeOf value

theorem lower_localVar (same : ScopeRenames source target rename) (name : Nat) :
    renameExpr rename (CommonSyntax.lower (Data.localVar (F := Empty) source name)) =
      CommonSyntax.lower (Data.localVar (F := Empty) target name) := by
  unfold Data.localVar
  rw [same name]
  cases Data.resolve name source <;> rfl

/-- The actual source embed and actual Common lower commute, including the
scope extension under each source let. No typing/evaluation success premise
is used. Accepted compilation still requires the original coverage gate. -/
theorem lower_embed_rename (expression : CaseDataTerms.Expr Empty)
    (same : ScopeRenames source target rename) :
    renameExpr rename (CommonSyntax.lower (Data.embed source expression)) =
      CommonSyntax.lower (Data.embed target expression) := by
  induction expression generalizing source target rename with
  | value value => exact rename_valueLower value rename
  | var name => exact lower_localVar same name
  | letE name value body ihv ihb =>
      simp only [Data.embed, CommonSyntax.lower, renameExpr, ihv same, ihb (same.cons name)]
  | pair first last ihf ihl | record name first last ihf ihl | recordDefault name first last ihf ihl =>
      simp only [Data.embed, CommonSyntax.lower, renameExpr, ihf same, ihl same]
  | fst value ih | snd value ih | field name value ih | variant name value ih =>
      simp only [Data.embed, CommonSyntax.lower, renameExpr, ih same]
  | emptyRecord | nominal | nil | cons => rfl

theorem covered_embed_rename (expression : CaseDataTerms.Expr Empty)
    (same : ScopeRenames source target rename) :
    CommonSyntax.covered (Data.embed source expression) = CommonSyntax.covered (Data.embed target expression) := by
  induction expression generalizing source target rename with
  | value => rfl
  | var name =>
      unfold Data.embed Data.localVar
      rw [same name]
      cases Data.resolve name source <;> rfl
  | letE name value body ihv ihb =>
      simp only [Data.embed, CommonSyntax.covered, ihv same, ihb (same.cons name)]
  | pair first last ihf ihl | record name first last ihf ihl | recordDefault name first last ihf ihl =>
      simp only [Data.embed, CommonSyntax.covered, ihf same, ihl same]
  | fst value ih | snd value ih | field name value ih | variant name value ih =>
      simp only [Data.embed, CommonSyntax.covered, ih same]
  | emptyRecord | nominal | nil | cons => rfl

open PresenceGeneration (Comp Binding)
open CommonPatternEnvironment (NamedTypes semanticPrefix)

def corePrefix (bindings : NamedTypes) : List (CommonSyntax.Binding Common.model) :=
  bindings.map (fun binding => .mono (Comp.pure Common.model binding.2))

theorem core_prefix_related (bindings : NamedTypes)
    (related : CommonSyntax.EnvRel Common.model environment outer) :
    CommonSyntax.EnvRel Common.model (corePrefix bindings ++ environment) (semanticPrefix bindings ++ outer) := by
  induction bindings with
  | nil => exact related
  | cons binding rest ih =>
      exact CommonSyntax.EnvRel.mono ih (Comp.pure Common.model binding.2)

/-- Actual named source elaboration, independent Common constructor typing,
arbitrary captured polymorphic suffixes and every result. Unsupported data
is rejected on both sides by the existing coverage theorem, internally. -/
theorem named_typing_exact (expression : CaseDataTerms.Expr Empty) (source target : NamedTypes)
    (distinct : (source.map Prod.fst).Nodup) (same : LookupEq source target) (outerNames : List Nat)
    (environment : List (CommonSyntax.Binding Common.model)) (outer : List (Binding Common.model))
    (related : CommonSyntax.EnvRel Common.model environment outer) (result : Comp Common.model) :
    CommonSyntax.Typing Common.model (corePrefix source ++ environment)
      (Data.embed (source.map Prod.fst ++ outerNames) expression) result ↔
    CommonSyntax.Typing Common.model (corePrefix target ++ environment)
      (Data.embed (target.map Prod.fst ++ outerNames) expression) result := by
  have scopes := concrete_scope source target same outerNames
  have coverage := covered_embed_rename expression scopes
  cases accepted : CommonSyntax.covered (Data.embed (source.map Prod.fst ++ outerNames) expression) with
  | false =>
      have denied := coverage.symm.trans accepted
      constructor
      · intro typed; have bad := CommonSyntax.typing_covered typed; rw [accepted] at bad; cases bad
      · intro typed; have bad := CommonSyntax.typing_covered typed; rw [denied] at bad; cases bad
  | true =>
      rw [CommonSyntax.lowering_exact _ accepted (core_prefix_related source related),
        CommonSyntax.lowering_exact _ (coverage.symm.trans accepted) (core_prefix_related target related)]
      have expressions := lower_embed_rename expression scopes
      rw [← expressions]
      exact CommonPatternScopeRenaming.typing_rename_exact _ Common.model _ _ _
        (CommonPatternConcreteScope.concrete_instances source target distinct same outer) result

open PresenceGeneration (SchemeEnv CompTerm Formula generate)

/-- A real finite gate before the existing finite expression generator. -/
def generateData (environment : SchemeEnv α) (scope : List Nat)
    (expression : CaseDataTerms.Expr Empty) (result : CompTerm α) : Formula α :=
  if CommonSyntax.covered (Data.embed scope expression) then
    generate environment (CommonSyntax.lower (Data.embed scope expression)) result
  else .bot

theorem generateData_exact (expression : CaseDataTerms.Expr Empty) (scope : List Nat)
    (assignment : α → Comp Common.model) (symbolic : SchemeEnv α)
    (environment : List (CommonSyntax.Binding Common.model)) (semantic : List (Binding Common.model))
    (coreRelated : CommonSyntax.EnvRel Common.model environment semantic)
    (symbolicRelated : PresenceGeneration.EnvRel Common.model assignment symbolic semantic)
    (result : CompTerm α) :
    (generateData symbolic scope expression result).Holds Common.model assignment ↔
      CommonSyntax.Typing Common.model environment (Data.embed scope expression)
        (result.eval Common.model assignment) := by
  cases accepted : CommonSyntax.covered (Data.embed scope expression) with
  | false =>
      simp only [generateData, accepted, Bool.false_eq_true, ↓reduceIte, Formula.Holds]
      constructor
      · exact False.elim
      · intro typed
        have bad := CommonSyntax.typing_covered typed
        rw [accepted] at bad
        cases bad
  | true =>
      simp only [generateData, accepted, ↓reduceIte]
      exact (PresenceGeneration.generate_models_iff_typing Common.model _ symbolic semantic assignment result
        symbolicRelated).trans (CommonSyntax.lowering_exact _ accepted coreRelated _).symm

theorem named_generation_exact (expression : CaseDataTerms.Expr Empty) (source target : NamedTypes)
    (distinct : (source.map Prod.fst).Nodup) (same : LookupEq source target) (outerNames : List Nat)
    (environment : List (CommonSyntax.Binding Common.model)) (outer : List (Binding Common.model))
    (related : CommonSyntax.EnvRel Common.model environment outer)
    (sourceSlots : α → Comp Common.model) (targetSlots : β → Comp Common.model)
    (sourceEnv : SchemeEnv α) (targetEnv : SchemeEnv β)
    (sourceRelated : PresenceGeneration.EnvRel Common.model sourceSlots sourceEnv (semanticPrefix source ++ outer))
    (targetRelated : PresenceGeneration.EnvRel Common.model targetSlots targetEnv (semanticPrefix target ++ outer))
    (sourceResult : CompTerm α) (targetResult : CompTerm β)
    (resultSame : sourceResult.eval Common.model sourceSlots = targetResult.eval Common.model targetSlots) :
    (generateData sourceEnv (source.map Prod.fst ++ outerNames) expression sourceResult).Holds Common.model sourceSlots ↔
      (generateData targetEnv (target.map Prod.fst ++ outerNames) expression targetResult).Holds Common.model targetSlots := by
  rw [generateData_exact expression _ sourceSlots sourceEnv _ _ (core_prefix_related source related) sourceRelated,
    generateData_exact expression _ targetSlots targetEnv _ _ (core_prefix_related target related) targetRelated,
    resultSame]
  exact named_typing_exact expression source target distinct same outerNames environment outer related _

end Yulang.CommonPatternSourceScope
