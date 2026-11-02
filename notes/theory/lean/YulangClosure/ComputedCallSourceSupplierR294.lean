import YulangClosure.ComputedCallUnionRealizationR293
import YulangClosure.OriginalSourceEvents

/-!
R294: exact obstruction in the existing source-owned event registry.

The selected EI/GR1 constructor needs a CalRet-dependent argument telescope and
complete phase/arm schemas. The original sourceRules App emits ViewLogic, local
atoms and two checking goals, but does not itself open these runtime binders.
For the actual nested source `(f x) y`, sourceRecord cannot supply ANY history
record. This is an equation of the existing source constructors, not an
interpretation of arbitrary Inputs, a refutation of EI, or a claim that every
other registry is empty. Static callOwners does register the outer App.

No source supplier, EI introduction, R293 EI identification or R159 admission
is claimed. Original semantics and all existing definitions remain unchanged.
-/
namespace YulangClosure.ComputedCallSourceSupplierR294

open OriginalSource OriginalSourceEnvironment OriginalSourceInterpretation
open OriginalSourceEvents

/-- Arbitrary original resolved-name identities and context are retained. -/
def computedSource (f x y : Name) : Source .expression :=
  .app ⟨4, none⟩
    (.app ⟨2, none⟩ (.name ⟨0, none⟩ f) (.name ⟨1, none⟩ x))
    (.name ⟨3, none⟩ y)

theorem name_owners_empty (context : Context) (site : Site) (name : Name)
    (route : OriginalSourceEvents.Route) (scope : List ScopeEntry) :
    owners route scope (sourceRules context (.name ⟨site, none⟩ name)) = [] := by
  simp only [sourceRules]
  split <;> rfl

/-- App itself contributes no event owner: only its children are traversed,
under the original ViewLogic scope and two distinct child routes. -/
theorem app_owners_children (context : Context) (site : Site)
    (callee argument : Source .expression)
    (route : OriginalSourceEvents.Route) (scope : List ScopeEntry) :
    owners route scope (sourceRules context (.app ⟨site, none⟩ callee argument)) =
      owners ((route ++ [0]) ++ [0])
        (extendScope scope route ⟨site, .viewLogic, 0⟩) (sourceRules context callee) ++
      (owners (((route ++ [0]) ++ [0]) ++ [1])
        (extendScope scope route ⟨site, .viewLogic, 0⟩) (sourceRules context argument) ++ []) := by
  simp only [sourceRules, RuleForest.two]
  rfl

/-- No runtime owner is emitted by this nested computed App's rule tree,
including when its Names resolve to published/family/formal bindings. -/
theorem computed_owners_empty (context : Context) (f x y : Name) :
    sourceOwners context (computedSource f x y) = [] := by
  simp only [sourceOwners, computedSource, app_owners_children,
    name_owners_empty, List.nil_append]


/-- Exhaustive over every event index, response/resume/future raw packet,
parent history, assignment, occurrence and declaration. This does not say
that the actual Call cannot execute or that another registry cannot supply it. -/
theorem computed_record_absent {s : Sorts} {View : Type}
    (assignment : RecordAssignment s View) (context : Context) (f x y : Name)
    (index : Nat) (origin : Declaration) (parents : List (HistoryStep s View))
    (occurrence : Nat) (raw : RawRecord s View) :
    sourceRecord assignment context (computedSource f x y) index origin parents occurrence raw = none := by
  simp [sourceRecord, computed_owners_empty]

/-- The independent actual static Call registry does retain this App. The
negative result above must not be generalized to all source registration. -/
theorem computed_outer_call_registered (context : Context) (f x y : Name) :
    CallOwner.application 4 context 2 3 ∈ sourceCallOwners context (computedSource f x y) := by
  unfold computedSource
  rw [source_app_call_owner]
  exact List.mem_cons_self

end YulangClosure.ComputedCallSourceSupplierR294
