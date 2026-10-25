import YulangClosure.PaperTupleSplitExecution
import YulangClosure.PaperTypeApplicationPreservation

/-!
Execution of the manuscript's finite template code table (operational manuscript
§types and ordinary reductions). Captured values are explicit arguments, as in
the manuscript; a registered body is checked once in its formal environment.
The table-body premise below is an independent syntax-directed typing judgment,
not a preservation or reachability assumption. Recursive calls refer to the
same finite table; this module makes no termination claim.
-/
namespace YulangClosure.PaperTypes.PaperTemplateExecution

open PaperTupleSplitExecution

/-- Enter a block of type binders without changing the ambient type variables. -/
abbrev shiftTypes := PaperTypeApplicationPreservation.shiftTypeSubstitutionN

/-- A template has no implicit lexical or graph captures. Its formal values
include all captures; ambient type variables and declarations remain shared. -/
inductive BodyTyped (d : DeclarationTable) : TemplateBody → Prop where
  | mk {identity arity formals result body} :
      PaperComputationTyped (mapDeclarationTable (shiftTypes arity) d) []
        (extendTupleEnvironment formals []) body result →
      BodyTyped d (.mk identity arity formals result body)

/-- The paper's independent obligation to check every registered template body. -/
def BodiesTyped (d : DeclarationTable) : Prop :=
  ∀ entry, entry ∈ d.templates → BodyTyped d entry

/-- First matching code identity. Uniqueness is supplied by the existing
invocation typing rule, rather than assumed by this executable lookup. -/
def lookupTemplate : List TemplateBody → Nat → Option TemplateBody
  | [], _ => none
  | entry :: rest, identity =>
      if templateIdentity entry = identity then some entry
      else lookupTemplate rest identity

theorem lookupTemplate_resolved {templates identity entry}
    (resolved : TemplateDeclarationResolved templates identity entry) :
    lookupTemplate templates identity = some entry := by
  induction templates with
  | nil => cases resolved.1
  | cons first rest ih =>
      by_cases hfirst : templateIdentity first = identity
      · have he : first = entry := resolved.2.2 first (by simp) hfirst
        simpa only [lookupTemplate, hfirst, ↓reduceIte] using congrArg some he
      · have hmem : entry ∈ rest := by
          rcases List.mem_cons.mp resolved.1 with he | hm
          · exact False.elim (hfirst (he ▸ resolved.2.1))
          · exact hm
        have hresolved : TemplateDeclarationResolved rest identity entry :=
          ⟨hmem, resolved.2.1, fun other hm hi =>
            resolved.2.2 other (List.mem_cons_of_mem first hm) hi⟩
        simpa only [lookupTemplate, hfirst, ↓reduceIte] using ih hresolved

/-- One finite expansion, with one simultaneous type instance and one
simultaneous value substitution. No scope, receipt, or view is introduced. -/
def expandTemplate : TemplateBody → List Ty → List Value → Option Computation
  | .mk _ arity formals _ body, typeArguments, arguments =>
      if typeArguments.length = arity ∧ arguments.length = formals.length then
        termSubstituteComputation (tupleReplacement arguments Value.variable)
          (mapPaperComputation (instantiateSubstitution typeArguments) body)
      else none

def templateStep (d : DeclarationTable) : Computation → Option Computation
  | .template identity typeArguments arguments =>
      (lookupTemplate d.templates identity).bind
        (fun entry => expandTemplate entry typeArguments arguments)
  | _ => none

theorem templateStep_resolved {d identity arity formals result body typeArguments arguments}
    (resolved : TemplateDeclarationResolved d.templates identity
      (.mk identity arity formals result body))
    (typeArity : typeArguments.length = arity)
    (valueArity : arguments.length = formals.length) :
    templateStep d (.template identity typeArguments arguments) =
      termSubstituteComputation (tupleReplacement arguments Value.variable)
        (mapPaperComputation (instantiateSubstitution typeArguments) body) := by
  simp [templateStep, lookupTemplate_resolved resolved, expandTemplate, typeArity, valueArity]

theorem expandTemplate_typeArity_mismatch
    (identity arity formals result body typeArguments arguments)
    (mismatch : typeArguments.length ≠ arity) :
    expandTemplate (.mk identity arity formals result body) typeArguments arguments = none := by
  simp [expandTemplate, mismatch]

theorem expandTemplate_valueArity_mismatch
    (identity arity formals result body typeArguments arguments)
    (mismatch : arguments.length ≠ formals.length) :
    expandTemplate (.mk identity arity formals result body) typeArguments arguments = none := by
  simp [expandTemplate, mismatch]

/-- Instantiate the registered derivation itself. The declaration table is
restored by cancellation, and the formal order is exactly the invocation order. -/
theorem BodyTyped.instantiate {d identity arity formals result body typeArguments}
    (hb : BodyTyped d (.mk identity arity formals result body))
    (typeArity : typeArguments.length = arity) :
    PaperComputationTyped d []
      (extendTupleEnvironment (formals.map (instantiateType typeArguments)) [])
      (mapPaperComputation (instantiateSubstitution typeArguments) body)
      (instantiateType typeArguments result) := by
  cases hb with
  | mk bodyTyping =>
      have ht := bodyTyping.typeTransport (instantiateSubstitution typeArguments)
      have hd : mapDeclarationTable (instantiateSubstitution typeArguments)
          (mapDeclarationTable (shiftTypes arity) d) = d := by
        simpa only [liftSubN, typeArity, shiftTypes] using
          PaperTypeApplicationPreservation.mapDeclarationTable_cancel 0 typeArguments d
      rw [hd, mapTypeEnvironment_extendTupleEnvironment] at ht
      have instantiate_eq : instantiateType typeArguments =
          subst (instantiateSubstitution typeArguments) := by
        funext ty
        rfl
      rw [instantiate_eq]
      simpa only [mapGraphEnvironment, List.map_nil, mapTypeEnvironment] using ht

/-- Substitute the actual values into the once-checked body. Any caller graph
and lexical environment is allowed; captures enter only through actual values. -/
theorem BodyTyped.expand {d g e identity arity formals result body typeArguments arguments}
    (hb : BodyTyped d (.mk identity arity formals result body))
    (typeArity : typeArguments.length = arity)
    (ha : ValuesTyped d g e arguments (formals.map (instantiateType typeArguments))) :
    ∃ next, expandTemplate (.mk identity arity formals result body) typeArguments arguments = some next ∧
      PaperComputationTyped d g e next (instantiateType typeArguments result) := by
  have typedBody := hb.instantiate typeArity
  have emptyGraph : GraphLookupPreserved [] g := by
    intro identity ty lookup
    cases lookup
  have graphBody := typedBody.graphWeaken emptyGraph
  have emptyEnvironment : TermSubstitutionTyped d g [] e Value.variable := by
    intro n ty lookup
    cases lookup
  obtain ⟨next, hs, ht⟩ := graphBody.termSubstitute
    (tupleReplacement_typed ha emptyEnvironment)
  have valueArity : arguments.length = formals.length := by
    simpa only [List.length_map] using values_length ha
  refine ⟨next, ?_, ht⟩
  simpa [expandTemplate, typeArity, valueArity] using hs

/-- Execute one typed invocation using the actual entry recovered from the
unchanged invocation rule and the finite table's independent body derivations. -/
theorem template_applicable {d g e identity typeArguments arguments result}
    (hd : BodiesTyped d)
    (hc : PaperComputationTyped d g e (.template identity typeArguments arguments) result) :
    ∃ next, templateStep d (.template identity typeArguments arguments) = some next ∧
      PaperComputationTyped d g e next result := by
  obtain ⟨arity, formals, bodyResult, body, resolved, typeArity, ha, he⟩ :=
    hc.templateInversion
  cases he
  obtain ⟨next, hs, ht⟩ := (hd _ resolved.1).expand typeArity ha
  refine ⟨next, ?_, ht⟩
  simpa only [templateStep, lookupTemplate_resolved resolved, Option.bind_some] using hs

/-- Every successful raw template step preserves the caller's exact type. -/
theorem template_preservation {d g e c next result}
    (hd : BodiesTyped d) (hc : PaperComputationTyped d g e c result)
    (hs : templateStep d c = some next) :
    PaperComputationTyped d g e next result := by
  cases c with
  | template identity typeArguments arguments =>
      obtain ⟨actual, he, ht⟩ := template_applicable hd hc
      exact Option.some.inj (he.symm.trans hs) ▸ ht
  | _ => simp [templateStep] at hs

/-- A two-type, two-value entry whose last source formal is index zero. -/
def lastFormalEntry : TemplateBody :=
  .mk 41 2 [.var 0, .var 1] (.var 1) (.ret (.variable 0))

def lastFormalTable : DeclarationTable :=
  { operations := [], nominalConstructors := [], primitives := [],
    templates := [lastFormalEntry], nativeListIdentity := 0 }

theorem lastFormalTable_bodiesTyped : BodiesTyped lastFormalTable := by
  intro entry hm
  have he : entry = lastFormalEntry := List.mem_singleton.mp hm
  subst entry
  exact .mk (.ret (.variable rfl))

/-- Distinct argument types and values discriminate simultaneous substitution
and the last-formal-at-zero convention. -/
theorem lastFormal_execution :
    templateStep lastFormalTable
      (.template 41 [.base .int, .base .bool]
        [.literal (.integer 7), .literal (.boolean true)]) =
      some (.ret (.literal (.boolean true))) := by
  simp [templateStep, lastFormalTable, lastFormalEntry, lookupTemplate, templateIdentity,
    expandTemplate, mapPaperComputation, mapPaperValue, tupleReplacement, prefixReplacement,
    termSubstituteComputation, supportedTermComputation, supportedTermValue,
    replaceTermComputation, replaceTermValue]

theorem lastFormal_invocation_typed (g : GraphEnvironment) (e : TypeEnvironment) :
    PaperComputationTyped lastFormalTable g e
      (.template 41 [.base .int, .base .bool]
        [.literal (.integer 7), .literal (.boolean true)]) (.base .bool) := by
  have resolved : TemplateDeclarationResolved lastFormalTable.templates 41 lastFormalEntry := by
    refine ⟨by simp [lastFormalTable], rfl, ?_⟩
    intro other hm _
    exact List.mem_singleton.mp hm
  exact .template resolved rfl (.cons .literal (.cons .literal .nil))

/-- Apply the general preservation theorem to the checked two-type table,
with an arbitrary caller graph and lexical environment. -/
theorem lastFormal_result_typed (g : GraphEnvironment) (e : TypeEnvironment) :
    PaperComputationTyped lastFormalTable g e
      (.ret (.literal (.boolean true))) (.base .bool) :=
  template_preservation lastFormalTable_bodiesTyped
    (lastFormal_invocation_typed g e) lastFormal_execution

end YulangClosure.PaperTypes.PaperTemplateExecution
