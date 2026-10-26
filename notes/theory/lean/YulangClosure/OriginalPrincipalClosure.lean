import YulangClosure.SourcePrincipalTransport
import YulangClosure.OriginalPrincipality
import YulangClosure.SimpleSubConstraintSoundness
import YulangClosure.SimpleSubLatticeCertificates

/-!
Original-source discriminators at the remaining occurrence/principality seam.

This module DOES NOT prove original principality. It constructs the original
single-recursive replay source with an observed y field and the reproduced
direct-return source; checks their original source-rule censuses, retains the
actual written-boundary and Return scopes, and proves a solution-set obstruction for the
high/low pair and two independent uses. The obstruction is also proved for
all regular lattice solution graphs, including recursive types and all four
Function ports. The native source-to-copy bridge, complete source membership,
actual receiving association, and publication eligibility remain obligations.
No source law, receiving convention, or FiberConstant premise is introduced.
-/
namespace YulangClosure.OriginalPrincipalClosure

open OriginalSource OriginalSourceEnvironment



namespace ObservedReplay

open SourcePrincipalTransport

/-- The supported single-self-recursive BRD/AR source, with the same y
returned as one additional field. No local mutual group is used here. -/
def lastFields : Source .recordItems :=
  .recordField 30 3 (.name ⟨31, none⟩ 4) .recordNil
def laterFields : Source .recordItems :=
  .recordField 19 1 recursiveCall lastFields
def fields : Source .recordItems := .recordField 15 0 hCall laterFields
def fInitializer : Source .expression :=
  .lambda ⟨8, none⟩ ⟨9, 3, none, false⟩ (.wild 10)
    (.lambda ⟨11, none⟩ ⟨12, 4, none, false⟩ (.wild 13)
      (.record ⟨14, none⟩ fields))
def bindings : Source .bindings := .binding 7 2 none fInitializer .bindingsNil

def firstCall : Source .expression :=
  .app ⟨35, none⟩
    (.app ⟨36, none⟩ (.name ⟨37, none⟩ 2)
      (.record ⟨38, none⟩ (.recordField 39 2
        (.literal ⟨40, none⟩ (.int 0)) .recordNil)))
    (.literal ⟨41, none⟩ (.int 0))
def secondCall : Source .expression :=
  .app ⟨44, none⟩
    (.app ⟨45, none⟩ (.name ⟨46, none⟩ 2)
      (.record ⟨47, none⟩ (.recordField 48 2
        (.literal ⟨49, none⟩ (.bool true)) .recordNil)))
    (.literal ⟨50, none⟩ (.bool true))
def clients : Source .expression :=
  .record ⟨32, none⟩
    (.recordField 33 4 (.select ⟨34, some 0⟩ firstCall 3)
      (.recordField 42 5 (.select ⟨43, some 1⟩ secondCall 3) .recordNil))
def topBody : Source .expression :=
  .block ⟨5, none⟩ (.statementsCons (.letS 6 true bindings) .statementsNil) clients
def topInitializer : Source .expression :=
  .lambda ⟨2, none⟩ ⟨3, 1, none, false⟩ (.wild 4) topBody
def program : Source .expression :=
  .block ⟨0, none⟩
    (.statementsCons (.letS 27 false
      (.binding 1 0 none topInitializer .bindingsNil)) .statementsNil)
    (.name ⟨26, none⟩ 0)

/-- y is now used twice: in the recursive argument and in the output field.
Its original value entry role is unchanged; the single-use flag is not forged. -/
def bodyContext : Context :=
  {name := 4, owner := 12, kind := .formal, entry := some .value, singleUse := false} ::
    SourcePrincipalTransport.xContext

def clientContext : Context :=
  [{name := 2, owner := 7, kind := .published}, hBinding]

/-- Complete source owner census from raw syntax. Annotation formation and
selection rules remain present, and both f uses have distinct source sites. -/
theorem complete_call_census :
    sourceCallOwners [] program =
      [.closure 2 [] 3 4 5,
       .closure 8 recursiveContext 9 10 11,
       .closure 11 xContext 12 13 14,
       .application 16 bodyContext 17 18,
       .application 20 bodyContext 21 22,
       .application 35 clientContext 36 41,
       .application 36 clientContext 37 38,
       .application 44 clientContext 45 50,
       .application 45 clientContext 46 47] := by
  simp only [sourceCallOwners, program, topInitializer, topBody, bindings,
    fInitializer, fields, laterFields, lastFields, clients, firstCall, secondCall,
    hCall, recursiveCall, argument, hName, xName, fName, yName,
    sourceRules, statementRulesK, statementsRulesK, bindingsRulesK, expressionRulesK]
  rfl

/-- Both original calls still carry their complete certificate, source
incidence, whole argument compatibility, and both checking relations. -/
theorem original_complete_apps :
    sourceRules bodyContext hCall =
      .existsE ⟨16, .viewLogic, 0⟩
        (.rule .app 16 bodyContext
          (([AtomKind.descriptorFormation, .wholeArgumentCompatibility,
            .completeCallCertificate, .sourceCallIncidence, .callableImage,
            .roleAndInitialCallOrigin].map
              (fun kind => Premise.atom (atom kind 16 bodyContext [17, 18]))) ++
           [.checking ⟨.value, 16, bodyContext, ⟨17, .returnedValue⟩, ⟨16, .descriptor⟩⟩,
            .checking ⟨.computation, 16, bodyContext,
              ⟨16, .callableImage⟩, ⟨16, .synthesis⟩⟩])
          (.two (sourceRules bodyContext hName) (sourceRules bodyContext xName))) ∧
    sourceRules bodyContext recursiveCall =
      .existsE ⟨20, .viewLogic, 0⟩
        (.rule .app 20 bodyContext
          (([AtomKind.descriptorFormation, .wholeArgumentCompatibility,
            .completeCallCertificate, .sourceCallIncidence, .callableImage].map
              (fun kind => Premise.atom (atom kind 20 bodyContext [21, 22]))) ++
           [.checking ⟨.value, 20, bodyContext, ⟨21, .returnedValue⟩, ⟨20, .descriptor⟩⟩,
            .checking ⟨.computation, 20, bodyContext,
              ⟨20, .callableImage⟩, ⟨20, .synthesis⟩⟩])
          (.two (sourceRules bodyContext fName) (sourceRules bodyContext argument))) := by
  simp only [hCall, recursiveCall, sourceRules]
  exact ⟨rfl, rfl⟩

/-- The returned-y field is below both actual Returns. The theorem never
turns an unfinished h/f invocation into a completed observation. -/
theorem output_keeps_both_return_telescopes :
    sourceRules bodyContext fields =
      .rule .recordField 15 bodyContext
        [.atom {(atom .visibleFieldUpdate 15 bodyContext [16]) with labels := [0]}]
        (.two (sourceRules bodyContext hCall)
          (.executionE ⟨16, .returnRebind, 0⟩
            (.rule .recordField 19 bodyContext
              [.atom {(atom .visibleFieldUpdate 19 bodyContext [20]) with labels := [1]}]
              (.two (sourceRules bodyContext recursiveCall)
                (.executionE ⟨20, .returnRebind, 0⟩
                  (sourceRules bodyContext lastFields)))))) := by
  simp only [fields, laterFields, sourceRules]
  rfl

/-- The two public result observations are actual original annotation
boundaries. They were not inserted as private solver-only client clauses. -/
theorem actual_output_boundaries :
    sourceRules clientContext (.select ⟨34, some 0⟩ firstCall 3) =
      .rule .annotation 34 clientContext
        [.atom {(atom .finalAnnotationFormation 34 clientContext) with annotation := some 0},
         .boundary 34 clientContext ⟨34, .synthesis⟩ ⟨34, .writtenTarget⟩]
        (.one (sourceRules clientContext (.select ⟨34, none⟩ firstCall 3))) ∧
    sourceRules clientContext (.select ⟨43, some 1⟩ secondCall 3) =
      .rule .annotation 43 clientContext
        [.atom {(atom .finalAnnotationFormation 43 clientContext) with annotation := some 1},
         .boundary 43 clientContext ⟨43, .synthesis⟩ ⟨43, .writtenTarget⟩]
        (.one (sourceRules clientContext (.select ⟨43, none⟩ secondCall 3))) := by
  constructor <;> simp only [sourceRules] <;> rfl

def publishedF : Binding := {name := 2, owner := 7, kind := .published}

/-- Every published f Name receives its own whole-instance binder at its
actual site; in particular this applies to both real sites 37 and 46.
The recursive Name retains the single original internal binding. -/
theorem f_use_binder (site : Nat) :
    sourceRules clientContext (.name ⟨site, none⟩ 2) =
      .existsE ⟨site, .publishedInstance, 0⟩
        (.rule .name site clientContext
          [.atom {(atom .exactWholeInstance site clientContext) with
            names := [2], binding := some publishedF}]
          (.one (.rule .name site clientContext
            [.atom {(atom .resolvedSameBinding site clientContext) with
              names := [2], binding := some publishedF},
             .atom {(atom .computedFetchOnce site clientContext) with
              names := [2], binding := some publishedF}] .nil))) ∧
    lookupBinding bodyContext 2 = some fBinding := by
  simp only [sourceRules]
  exact ⟨rfl, rfl⟩

/-- Both registered direct receivers remain literal source projections under
all original frame classes, including future runtime payloads. -/
theorem direct_receivers_after_all_frames (readout : RuntimeReadout s View)
    (root : Root s View) (frames : List (Frame (Payload s View))) :
    let state := frames.foldl (decodeFrame readout) (root.withSource [] program).decoded
    state.callSubject ⟨16, .invocation, 0⟩ = ⟨17, .returnedValue⟩ ∧
    state.callSubject ⟨20, .invocation, 0⟩ = ⟨21, .returnedValue⟩ := by
  dsimp only
  have owners :
      (frames.foldl (decodeFrame readout) (root.withSource [] program).decoded).callOwner
        ⟨16, .invocation, 0⟩ = some (.application 16 bodyContext 17 18) ∧
      (frames.foldl (decodeFrame readout) (root.withSource [] program).decoded).callOwner
        ⟨20, .invocation, 0⟩ = some (.application 20 bodyContext 21 22) := by
    unfold Decoded.callOwner
    rw [decoded_call_owners]
    change (sourceCallOwners [] program).find? _ = _ ∧
      (sourceCallOwners [] program).find? _ = _
    rw [complete_call_census]
    exact ⟨rfl, rfl⟩
  simp only [Decoded.callSubject, owners.1, owners.2, Option.map_some, Option.getD_some]
  exact ⟨rfl, rfl⟩

end ObservedReplay

namespace SourceRetainedEvidence

/- An observational projection of the existing rule tree. This neither
adds evidence nor changes any original admission predicate or binder. -/
mutual
def sharedOwners : RuleTree → List Binder
  | .sharedE binder body => binder :: sharedOwners body
  | .rule _ _ _ _ children => forestSharedOwners children
  | .existsE _ body | .forallE _ body | .initializerE _ body | .executionE _ body
  | .publishGroup _ body | .atPublication _ body
  | .aliasPublication _ _ body => sharedOwners body
  | .choice _ left right => sharedOwners left ++ sharedOwners right

def forestSharedOwners : RuleForest → List Binder
  | .nil => []
  | .cons first rest => sharedOwners first ++ forestSharedOwners rest
end


end SourceRetainedEvidence

namespace DirectReturn

open SourcePrincipalTransport

/-- The actual rejected native source has expression statements and returns
its existing y binding directly. There is no field selection or record pattern. -/
def result : Source .expression := .name ⟨25, none⟩ 4
def statements : Source .statements :=
  .statementsCons (.expressionS 15 hCall)
    (.statementsCons (.expressionS 19 recursiveCall) .statementsNil)
def body : Source .expression := .block ⟨14, none⟩ statements result
def fInitializer : Source .expression :=
  .lambda ⟨8, none⟩ ⟨9, 3, none, false⟩ (.wild 10)
    (.lambda ⟨11, none⟩ ⟨12, 4, none, false⟩ (.wild 13) body)
def fBindings : Source .bindings := .binding 7 2 none fInitializer .bindingsNil
abbrev firstCall := ObservedReplay.firstCall
abbrev secondCall := ObservedReplay.secondCall
def iBindings : Source .bindings := .binding 33 5 (some 0) firstCall .bindingsNil
def bBindings : Source .bindings := .binding 43 6 (some 1) secondCall .bindingsNil
def clients : Source .expression :=
  .tuple ⟨51, none⟩ (.expressionsCons (.name ⟨52, none⟩ 5)
    (.expressionsCons (.name ⟨53, none⟩ 6) .expressionsNil))
def topBody : Source .expression :=
  .block ⟨5, none⟩
    (.statementsCons (.letS 6 true fBindings)
      (.statementsCons (.letS 32 false iBindings)
        (.statementsCons (.letS 42 false bBindings) .statementsNil))) clients
def topInitializer : Source .expression :=
  .lambda ⟨2, none⟩ ⟨3, 1, none, false⟩ (.wild 4) topBody
def ignoreInitializer : Source .expression :=
  .lambda ⟨62, none⟩ ⟨63, 8, none, false⟩ (.wild 64) (.literal ⟨65, none⟩ (.int 0))
def mainCall : Source .expression :=
  .app ⟨72, none⟩ (.name ⟨73, none⟩ 0) (.name ⟨74, none⟩ 7)
def program : Source .expression :=
  .block ⟨0, none⟩
    (.statementsCons (.letS 27 false
      (.binding 1 0 none topInitializer .bindingsNil))
      (.statementsCons (.letS 60 false
        (.binding 61 7 none ignoreInitializer .bindingsNil))
        (.statementsCons (.letS 70 false
          (.binding 71 9 none mainCall .bindingsNil)) .statementsNil)))
    (.name ⟨75, none⟩ 9)

abbrev bodyContext := ObservedReplay.bodyContext
abbrev clientContext := ObservedReplay.clientContext
def iBinding : Binding := {name := 5, owner := 33, kind := .published}
def secondContext : Context := iBinding :: clientContext
def topBinding : Binding := {name := 0, owner := 1, kind := .published}
def ignoreBinding : Binding := {name := 7, owner := 61, kind := .published}
def mainContext : Context := [ignoreBinding, topBinding]

/-- Four closures and all seven applications in the closed direct-return
source, including the real top/ignore application and the two sequential
written local boundaries. No Call or intermediate execution is erased. -/
theorem complete_call_census :
    sourceCallOwners [] program =
      [.closure 2 [] 3 4 5,
       .closure 8 recursiveContext 9 10 11,
       .closure 11 xContext 12 13 14,
       .application 16 bodyContext 17 18,
       .application 20 bodyContext 21 22,
       .application 35 clientContext 36 41,
       .application 36 clientContext 37 38,
       .application 44 secondContext 45 50,
       .application 45 secondContext 46 47,
       .closure 62 [topBinding] 63 64 65,
       .application 72 mainContext 73 74] := by
  simp only [sourceCallOwners, program, topInitializer, topBody, fBindings,
    fInitializer, body, statements, result, iBindings, bBindings, clients,
    firstCall, secondCall, ObservedReplay.firstCall, ObservedReplay.secondCall,
    ignoreInitializer, mainCall, hCall, recursiveCall, argument,
    hName, xName, fName, yName,
    sourceRules, statementRulesK, statementsRulesK, bindingsRulesK, expressionRulesK]
  rfl

/-- y is returned only after both actual statement executions. Pending
h/recursive invocations retain the whole original suffix. -/
theorem direct_return_keeps_both_calls :
    sourceRules bodyContext body =
      .rule .expressionS 15 bodyContext
        [.atom (atom .expressionDiscard 15 bodyContext [16])]
        (.two (sourceRules bodyContext hCall)
          (.executionE ⟨16, .returnRebind, 0⟩
            (.rule .expressionS 19 bodyContext
              [.atom (atom .expressionDiscard 19 bodyContext [20])]
              (.two (sourceRules bodyContext recursiveCall)
                (.executionE ⟨20, .returnRebind, 0⟩
                  (.rule .block 14 bodyContext
                    [.atom (atom .blockFinalRoot 14 bodyContext [25])]
                    (.one (sourceRules bodyContext result)))))))) := by
  simp only [body, statements, sourceRules, statementsRulesK, statementRulesK]
  rfl

/-- The written Int/Bool boundary is on the actual invocation's final root,
inside its initializer and before the original Shared/publication telescope. -/
theorem written_boundary_telescope (context : Context) (site name target : Nat)
    (call : Source .expression) (continuation : RuleTree) :
    bindingsRulesK context (.binding site name (some target) call .bindingsNil)
      true continuation =
      .initializerE site
        (expressionRulesK context call
          (.rule .annotation site context
            [.atom {(atom .finalAnnotationFormation site context [call.site]) with
              annotation := some target},
             .boundary site context ⟨call.site, .finalRoot⟩ ⟨site, .writtenTarget⟩]
            (.one (.executionE ⟨site, .returnRebind, 0⟩
              (.sharedE ⟨site, .shared, 0⟩
                (.rule .binding site context
                  [.atom {(atom .oneShotInitializer site context [call.site]) with
                    names := [name], annotation := some target},
                   .atom {(atom .publicationFinalRoot site context [call.site]) with
                    names := [name], annotation := some target}]
                  (.one (.publishGroup [(name, site)] continuation)))))))) := by
  simp only [bindingsRulesK]
  rfl

/-- Actual direct source receivers survive arbitrary original runtime frames.
This still does not assign a receiver to a native Replay/ExtrudeFresh pair. -/
theorem direct_receivers_after_all_frames (readout : RuntimeReadout s View)
    (root : Root s View) (frames : List (Frame (Payload s View))) :
    let state := frames.foldl (decodeFrame readout) (root.withSource [] program).decoded
    state.callSubject ⟨16, .invocation, 0⟩ = ⟨17, .returnedValue⟩ ∧
    state.callSubject ⟨20, .invocation, 0⟩ = ⟨21, .returnedValue⟩ := by
  dsimp only
  have owners :
      (frames.foldl (decodeFrame readout) (root.withSource [] program).decoded).callOwner
        ⟨16, .invocation, 0⟩ = some (.application 16 bodyContext 17 18) ∧
      (frames.foldl (decodeFrame readout) (root.withSource [] program).decoded).callOwner
        ⟨20, .invocation, 0⟩ = some (.application 20 bodyContext 21 22) := by
    unfold Decoded.callOwner
    rw [decoded_call_owners]
    change (sourceCallOwners [] program).find? _ = _ ∧
      (sourceCallOwners [] program).find? _ = _
    rw [complete_call_census]
    exact ⟨rfl, rfl⟩
  simp only [Decoded.callSubject, owners.1, owners.2, Option.map_some, Option.getD_some]
  exact ⟨rfl, rfl⟩

/-- The exact current program introduces Shared at its six real binding
initializers. This does not supply the distinct formal-rebind evidence. -/
theorem shared_binder_census :
    SourceRetainedEvidence.sharedOwners (sourceRules [] program) =
      [⟨7, .shared, 0⟩, ⟨33, .shared, 0⟩, ⟨43, .shared, 0⟩,
       ⟨1, .shared, 0⟩, ⟨61, .shared, 0⟩, ⟨71, .shared, 0⟩] := by
  simp only [program, topInitializer, topBody, fBindings,
    fInitializer, body, statements, result, iBindings, bBindings, clients,
    firstCall, secondCall, ObservedReplay.firstCall, ObservedReplay.secondCall,
    ignoreInitializer, mainCall, hCall, recursiveCall, argument,
    hName, xName, fName, yName,
    sourceRules, statementRulesK, statementsRulesK, bindingsRulesK, expressionRulesK,
    SourceRetainedEvidence.sharedOwners]
  rfl

/-- None of the four actual formal owners has the needed retained Shared
binder in this frozen builder. This is a representation gap, not permission
to drop that original source evidence or a refutation of source typing. -/
theorem formal_shared_evidence_absent :
    ∀ formal ∈ [3, 9, 12, 63],
      (⟨formal, .shared, 0⟩ : Binder) ∉
        SourceRetainedEvidence.sharedOwners (sourceRules [] program) := by
  rw [shared_binder_census]
  decide

end DirectReturn

namespace DirectReturnInterfaces
open SimpleSub

/-- Native projections of the closed two-view candidate. The actual source
inlet is fixed once at S; these checked facets do not reassign that inlet.
Complete Strict/ReadInvoke and all original guards remain separate obligations. -/
def support : Term .value := .union (.atom 0) (.atom 1)
def record (A : Term .value) : Term .value := .recordCons 2 false A .recordNil
def inner (A : Term .value) : Term .value := .function A .bottom .bottom A
def bothViews : Term .value := .intersection (inner (.atom 0)) (inner (.atom 1))
def outer : Term .value := .function (record support) .bottom .bottom bothViews
def capturedH : Term .value := .function (record support) .bottom .bottom (.atom 0)

/-- Every recursive use checks the SAME closed F. No polymorphic recursive
instance or per-use capture assignment occurs in this finite projection. -/
theorem recursive_call (A : Term .value) (allowed : Sub A support) :
    Sub outer (.function (record A) .bottom .bottom bothViews) := by
  exact .function (.recordCons 2 false allowed (.refl _)) (.refl _) (.refl _) (.refl _)

/-- The first whole Function use and the first facet use all four ports. -/
theorem integer_instance :
    Sub outer (.function (record (.atom 0)) .bottom .bottom bothViews) ∧
    Sub bothViews (.function (.atom 0) .bottom .bottom (.atom 0)) :=
  ⟨recursive_call _ (.unionLeft _ _), .intersectionLeft _ _⟩

/-- The second use projects the other proof of the SAME intersection. -/
theorem boolean_instance :
    Sub outer (.function (record (.atom 1)) .bottom .bottom bothViews) ∧
    Sub bothViews (.function (.atom 1) .bottom .bottom (.atom 1)) :=
  ⟨recursive_call _ (.unionRight _ _), .intersectionRight _ _⟩

/-- These projections are closed under every row renaming. In particular
freshening cannot select a different f or h type on the two client branches. -/
theorem closed_interfaces_rename_fixed (rowMap : Renaming) :
    outer.rename rowMap = outer ∧ capturedH.rename rowMap = capturedH := ⟨rfl, rfl⟩

end DirectReturnInterfaces

namespace TwoUses
open SimpleSub SimpleSub.Generalization

/-- A sound outer-atom observation of the existing finite structural Sub.
The full Function/record/tuple/variant rules remain in the induction. -/
def atomView (atom : Nat) {k} : Term k → Prop
  | .atom other => atom = other
  | .bottom => False
  | .top => True
  | .union a b => atomView atom a ∨ atomView atom b
  | .intersection a b => atomView atom a ∧ atomView atom b
  | _ => False

theorem sub_preserves_atomView {k} {a b : Term k} (sub : Sub a b) (atom : Nat) :
    atomView atom a → atomView atom b := by
  induction sub with
  | refl _ => exact fun h => h
  | trans _ _ first second => exact fun h => second (first h)
  | bottom _ => exact False.elim
  | top _ => exact fun _ => True.intro
  | unionLeft _ _ => exact Or.inl
  | unionRight _ _ => exact Or.inr
  | unionElim _ _ left right => exact fun h => h.elim left right
  | intersectionLeft _ _ => exact And.left
  | intersectionRight _ _ => exact And.right
  | intersectionIntro _ _ left right => exact fun h => ⟨left h, right h⟩
  | unionMono _ _ left right => exact fun h => h.elim (fun h => Or.inl (left h)) (fun h => Or.inr (right h))
  | intersectionMono _ _ left right => exact fun h => ⟨left h.1, right h.2⟩
  | function => exact False.elim
  | recordCons => exact False.elim
  | tupleCons => exact False.elim
  | variantCons => exact False.elim

theorem distinct_atoms_not_sub (first second : Nat) (distinct : first ≠ second) :
    ¬ Sub (Term.atom (k := .value) first) (.atom second) := by
  intro sub
  exact distinct (sub_preserves_atomView sub first rfl)

/-- The parent y is high, its actual positive approximation is low. -/
def before : Generalization.Levels := fun _ row => if row = 0 then 2 else 1
def after : Generalization.Levels := fun _ _ => 1
def quotient : Renaming := fun _ row => if row = 0 then 1 else row
def wholeMap : Renaming := transport 2 2 1 after quotient
def link : Store := [⟨.value, .var 0, .var 1⟩]
def clients : Store :=
  [⟨.value, .atom 0, .var 2⟩, ⟨.value, .var 2, .atom 0⟩,
   ⟨.value, .atom 1, .var 4⟩, ⟨.value, .var 4, .atom 1⟩]
def valuation : Valuation := fun _ row =>
  if row = 1 then .union (.atom 0) (.atom 1)
  else if row = 2 then .atom 0
  else if row = 4 then .atom 1
  else .bottom

/-- There is ONE simultaneous ordinary solution for the base link and both
independent use constraints. No per-clause or per-use witness is selected. -/
theorem ordinary_joint_solution :
    ((usesStore 2 1 before [0, 1] link) ++ clients).Satisfied valuation := by
  rw [Store.satisfied_append, usesStore_satisfied]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp only [link, Store.satisfied_cons, Store.satisfied_nil, Constraint.Satisfied,
      Term.subst, valuation]
    exact ⟨.bottom _, True.intro⟩
  · intro use member
    have cases : use = 0 ∨ use = 1 := by simpa using member
    rcases cases with rfl | rfl
    · simp [link, Store.satisfied_cons, Constraint.Satisfied, Term.subst,
        freshen, before, valuation, Sub.unionLeft]
    · simp [link, Store.satisfied_cons, Constraint.Satisfied, Term.subst,
        freshen, before, valuation, Sub.unionRight]
  · simp [clients, Store.satisfied_cons, Constraint.Satisfied, Term.subst,
      valuation, Sub.refl]

/-- Even allowing every internal assignment to change, no single solution
survives the collapsed two-use clients. This is not all-model preservation
or a fixed-transform FiberConstant hypothesis. -/
theorem intruded_no_joint_solution (solution : Valuation) :
    ¬ (((usesStore 2 1 after [0, 1] (link.map (Constraint.rename quotient))) ++
        clients.map (Constraint.rename wholeMap)).Satisfied solution) := by
  intro solved
  have clientSolved := (Store.satisfied_append _ _ _).mp solved |>.2
  simp only [clients, List.map_cons, List.map_nil, Store.satisfied_cons,
    Store.satisfied_nil, Constraint.Satisfied, Constraint.rename,
    Term.rename, Term.subst] at clientSolved
  have use0 : wholeMap .value 2 = 1 := rfl
  have use1 : wholeMap .value 4 = 1 := rfl
  rw [use0, use1] at clientSolved
  exact distinct_atoms_not_sub 1 0 (by decide)
    (.trans clientSolved.2.2.1 clientSolved.2.1)

/-- Exact existence failure across the high/low identification for the
observable two-use constraints, under the native finite-use algebra. -/
theorem solution_set_separation :
    (∃ solution, ((usesStore 2 1 before [0, 1] link) ++ clients).Satisfied solution) ∧
    ¬ (∃ solution,
      ((usesStore 2 1 after [0, 1] (link.map (Constraint.rename quotient))) ++
        clients.map (Constraint.rename wholeMap)).Satisfied solution) := by
  exact ⟨⟨valuation, ordinary_joint_solution⟩,
    fun ⟨solution, solved⟩ => intruded_no_joint_solution solution solved⟩

end TwoUses

namespace RegularSeparation
open SimpleSub SimpleSub.Regular SimpleSub.Lattice

/-- One ground-atom observation, independent of recursive children. -/
def nodeView (atom : Nat) {k} : Regular.Node k → Prop
  | .atom other => atom = other
  | .top => True
  | _ => False

/-- Least positive membership through all lattice nodes. Recursive structural
children are retained by the graph and do not masquerade as ground atoms. -/
inductive AtomOccurs (graph : Lattice.Graph) (atom : Nat) : Kind → Nat → Prop where
  | atom {k i} (found : graph.lookup k i = some (.structural (.atom atom))) :
      AtomOccurs graph atom k i
  | top {k i} (found : graph.lookup k i = some (.structural .top)) :
      AtomOccurs graph atom k i
  | unionLeft {k i a b} (found : graph.lookup k i = some (.union a b)) :
      AtomOccurs graph atom k a → AtomOccurs graph atom k i
  | unionRight {k i a b} (found : graph.lookup k i = some (.union a b)) :
      AtomOccurs graph atom k b → AtomOccurs graph atom k i
  | intersection {k i a b} (found : graph.lookup k i = some (.intersection a b)) :
      AtomOccurs graph atom k a → AtomOccurs graph atom k b → AtomOccurs graph atom k i

theorem occurs_structural {graph : Lattice.Graph} {atom k i node}
    (found : graph.lookup k i = some (.structural node)) :
    AtomOccurs graph atom k i ↔ nodeView atom node := by
  constructor
  · intro occurrence
    cases occurrence <;> simp_all [nodeView]
    all_goals subst node <;> simp
  · cases node <;> simp only [nodeView]
    · intro equal
      subst equal
      exact .atom found
    · exact False.elim
    · intro _
      exact .top found
    all_goals exact False.elim

theorem occurs_union {graph : Lattice.Graph} {atom k i a b}
    (found : graph.lookup k i = some (.union a b)) :
    AtomOccurs graph atom k i ↔
      AtomOccurs graph atom k a ∨ AtomOccurs graph atom k b := by
  constructor
  · intro occurrence
    cases occurrence <;> simp_all
  · intro member
    exact member.elim (AtomOccurs.unionLeft found) (AtomOccurs.unionRight found)

theorem occurs_intersection {graph : Lattice.Graph} {atom k i a b}
    (found : graph.lookup k i = some (.intersection a b)) :
    AtomOccurs graph atom k i ↔
      AtomOccurs graph atom k a ∧ AtomOccurs graph atom k b := by
  constructor
  · intro occurrence
    cases occurrence <;> simp_all
  · intro member
    exact .intersection found member.1 member.2

theorem union_lookup {graph : Lattice.Graph} {k i a b}
    (found : unionAt graph k i = some (a, b)) :
    graph.lookup k i = some (.union a b) := by
  cases lookup : graph.lookup k i with
  | none => simp [unionAt, lookup] at found
  | some node =>
    cases node <;> simp_all [unionAt]

theorem intersection_lookup {graph : Lattice.Graph} {k i a b}
    (found : intersectionAt graph k i = some (a, b)) :
    graph.lookup k i = some (.intersection a b) := by
  cases lookup : graph.lookup k i with
  | none => simp [intersectionAt, lookup] at found
  | some node =>
    cases node <;> simp_all [intersectionAt]

theorem nodeRel_preserves_view {relation : Comparison → Prop} {k}
    {lower upper : Regular.Node k} (related : NodeRel relation lower upper) (atom : Nat) :
    nodeView atom lower → nodeView atom upper := by
  cases lower <;> cases upper <;> simp_all [NodeRel, nodeView]

/-- Every constructor of the regular lattice layer preserves the same atom
observation. No conclusion is assumed for the recursive comparison table. -/
theorem layer_preserves_atom {graph : Lattice.Graph} {relation : Comparison → Prop}
    {pair : Comparison} (related : Lattice.Layer graph relation pair) (atom : Nat) :
    AtomOccurs graph atom pair.kind pair.lower → AtomOccurs graph atom pair.kind pair.upper := by
  induction related with
  | @structural pair children expanded closed =>
    cases lowerFound : graph.lookup pair.kind pair.lower with
    | none => simp [structuralExpand, lowerFound] at expanded
    | some lower =>
      cases upperFound : graph.lookup pair.kind pair.upper with
      | none => simp [structuralExpand, lowerFound, upperFound] at expanded
      | some upper =>
        cases lower with
        | union a b => simp [structuralExpand, lowerFound, upperFound] at expanded
        | intersection a b => simp [structuralExpand, lowerFound, upperFound] at expanded
        | structural lower =>
          cases upper with
          | union a b => simp [structuralExpand, lowerFound, upperFound] at expanded
          | intersection a b => simp [structuralExpand, lowerFound, upperFound] at expanded
          | structural upper =>
            simp only [structuralExpand, lowerFound, upperFound] at expanded
            have relation : NodeRel relation lower upper := by
              apply (nodeRel_iff _ _ _).mpr
              rw [expanded]
              exact closed
            intro member
            exact (occurs_structural upperFound).mpr
              (nodeRel_preserves_view relation atom ((occurs_structural lowerFound).mp member))
  | refl _ => exact fun member => member
  | trans _ _ first second => exact fun member => second (first member)
  | @bottom k a b found present =>
    have lower : graph.lookup k a = some (.structural .bottom) := by
      cases lookup : graph.lookup k a with
      | none => simp [bottomAt, lookup] at found
      | some node =>
        cases node <;> simp_all [bottomAt]
        rename_i structuralNode
        cases structuralNode <;> simp_all
    intro member
    exact False.elim ((occurs_structural lower).mp member)
  | @top k a b found present =>
    have upper : graph.lookup k b = some (.structural .top) := by
      cases lookup : graph.lookup k b with
      | none => simp [topAt, lookup] at found
      | some node =>
        cases node <;> simp_all [topAt]
        rename_i structuralNode
        cases structuralNode <;> simp_all
    exact fun _ => .top upper
  | unionLeft found => exact AtomOccurs.unionLeft (union_lookup found)
  | unionRight found => exact AtomOccurs.unionRight (union_lookup found)
  | unionElim found _ _ first second =>
    exact fun member => ((occurs_union (union_lookup found)).mp member).elim first second
  | intersectionLeft found => exact fun member => ((occurs_intersection (intersection_lookup found)).mp member).1
  | intersectionRight found => exact fun member => ((occurs_intersection (intersection_lookup found)).mp member).2
  | intersectionIntro found _ _ first second =>
    exact fun member => .intersection (intersection_lookup found) (first member) (second member)
  | unionMono lower upper _ _ first second =>
    intro member
    exact ((occurs_union (union_lookup lower)).mp member).elim
      (fun value => .unionLeft (union_lookup upper) (first value))
      (fun value => .unionRight (union_lookup upper) (second value))
  | intersectionMono lower upper _ _ first second =>
    intro member
    have values := (occurs_intersection (intersection_lookup lower)).mp member
    exact .intersection (intersection_lookup upper) (first values.1) (second values.2)

/-- Arbitrary regular graphs and all lattice alternatives still cannot
identify the two independent ground result observations. No acyclicity or
finite-tree interpretation is used. -/
theorem distinct_atoms_not_regular_sub {graph : Lattice.Graph} {first second a b}
    (left : graph.lookup .value a = some (.structural (.atom first)))
    (right : graph.lookup .value b = some (.structural (.atom second)))
    (distinct : first ≠ second) : ¬ Lattice.RegularSub graph ⟨.value, a, b⟩ := by
  intro related
  have member := layer_preserves_atom (related 1) first (AtomOccurs.atom left)
  exact distinct ((occurs_structural right).mp member)

/-- A single shared post-intrusion coordinate cannot satisfy the source
Boolean argument and the first use's integer output, even when every other
coordinate is changed jointly and the entire solution graph is recursive. -/
theorem shared_use_observations_impossible {graph : Lattice.Graph} {integer boolean shared}
    (intRoot : graph.lookup .value integer = some (.structural (.atom 0)))
    (boolRoot : graph.lookup .value boolean = some (.structural (.atom 1)))
    (argument : Lattice.RegularSub graph ⟨.value, boolean, shared⟩)
    (result : Lattice.RegularSub graph ⟨.value, shared, integer⟩) : False :=
  distinct_atoms_not_regular_sub boolRoot intRoot (by decide)
    (Lattice.regular_trans argument result)

end RegularSeparation
end YulangClosure.OriginalPrincipalClosure
