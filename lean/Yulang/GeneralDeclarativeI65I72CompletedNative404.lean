import Yulang.GeneralDeclarativeI65I72SupportedSound404

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72
open GeneralDeclarativeI65
open CommonRoleOutermostResolver (Dictionary Result Summarizes Tree)
open CommonRecursiveNominalIntervals (Endpoint Obligation)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeHead320 (Equation)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralDeclarativeInspect321 (Inspects Visit PatternK2)

def onePointName404 {s slots c param p} :
    MixedArg401 s (NamedSlot401 slots) c param p → Option Nat
  | .valuePoint _ _ _ cap => some cap.val.center
  | _ => none

def singlePointName404 {s slots c params ps} :
    MixedArgs401 s (NamedSlot401 slots) c params ps → Option Nat
  | .nil => none
  | .cons a more =>
    match more with
    | .nil => onePointName404 a
    | .cons _ _ => none

/-- Exact original typed term, not arbitrary equality of models:
a declared covariant unary value application with one actual lexical
point argument. Width/invariant/row alternatives do not use this rule. -/
def TypedCovariantPoint404 {s slots c p} (key logical : Nat) :
    NamedMixedTree401 s slots c p → Prop
  | .declaredApp name use _ _ args =>
    name = key ∧ use.mode = .declared [⟨.value,.covariant⟩] ∧
      singlePointName404 args = some logical
  | _ => False

theorem actual_typed_point_yields_literal_declared_code404 {s slots c p key logical}
    (tree : NamedMixedTree401 s slots c p) (actual : TypedCovariantPoint404 key logical tree) :
    DeclaredHead404 key tree ∧ fixedValueCode403 tree = some (.nominal key [.variable logical]) := by
  cases tree with
  | declaredApp name use authored table args =>
    have head : name = key := actual.1
    have mode : use.mode = .declared [⟨.value,.covariant⟩] := actual.2.1
    have observed : singlePointName404 args = some logical := actual.2.2
    refine ⟨⟨head,_,mode⟩,?_⟩
    subst key
    cases args with
    | nil => cases observed
    | cons a rest =>
      cases rest with
      | nil =>
        cases a with
        | valuePoint _ _ _ cap =>
          have exactSite : cap.val.center = logical := Option.some.inj observed
          subst logical
          rfl
        | valueInterval | rowPoint | rowInterval | valueTree => cases observed
      | cons => cases observed
  | binder | record | variant | join | scalar | emptyRecord | exactEmpty | pair =>
    exact False.elim actual

/-- The actual visible unary structural candidate. An already completed
output, if proved by the exact support child, gives the lower original
operand; the other operand is independently authored in this same state.
No new authored Origin is inserted for a completed output. -/
structure CompletedUnaryEntry404 (s : State) (q : Request) (row : Declaration)
    (need : OutputNeed s) where
  visibleRow : row ∈ visible s.core q
  input : Capture
  exactInput : q.demand.arguments = [input]
  written : Pattern
  exactHead : row.head = [written]
  key : Nat
  child : Pattern
  dispatch : normalize written = .app key [child]
  actualLower : need.expected.original.target = input.lower
  lowerChild : Nat
  lowerTerm : TypedCovariantPoint404 key lowerChild need.expected.rhs
  upper : Origin
  upperAuthored : upper ∈ s.core.origins
  upperRoute : OriginRoute s.core upper input.upper
  upperChild : Nat
  upperSyntax : upper.endpoint = .nominal key [.inl (.point (.ordinary (.var upperChild)))]
  query : Expr
  exactChild : translate (authoredRegistry s.core.current).constructors
    (interpretation s.core.current.environment.source.snapshot) child = some query
  inspecting : Inspects query

def CompletedUnaryEntry404.literal {s q row need} (entry : CompletedUnaryEntry404 s q row need) :
    LiteralInputNeed404 s entry.input need :=
  let consumed := actual_typed_point_yields_literal_declared_code404 need.expected.rhs entry.lowerTerm
  ⟨entry.key,[.variable entry.lowerChild],entry.actualLower,consumed.1,consumed.2⟩

/-- Read the actual support entry before using the compiled first lower
ordinary visit. The interval job and site are from the literal typed
point operand, and do not assume that its comparison succeeds. -/
theorem completed_lower_justifies_entered_native_child404 {R s q row needs need}
    (entry : CompletedUnaryEntry404 s q row need) (keeps : KeepsFixedOutputs404 R)
    (support : SupportForest R s needs) (slot : Nat) (there : needs[slot]? = some need) :
    (⟨entry.input.lower,.nominal entry.key [.variable entry.lowerChild]⟩ : Equation) ∈
      s.core.current.ordinary.equations ∧
    (CommonRecursiveNominalIntervals.decomposeContextArgument
      (α := Nat) false ⟨.value,.covariant⟩
      (.inl (.point (.ordinary (.var entry.lowerChild))))
      (.inl (.point (.ordinary (.var entry.upperChild))))) =
      some [(false,Obligation.value (.ordinary (.var entry.lowerChild)) (.ordinary (.var entry.upperChild)))] ∧
    Visit (GeneralDeclarativeGraphRows321.structural s.core.current.ordinary)
      entry.lowerChild entry.query entry.lowerChild :=
  ⟨support_at_literal_ordinal_yields_nominal404 keeps support slot there entry.literal,
    rfl,.here entry.inspecting⟩

structure CompletedChildK2404 (s : State) (q : Request) (needs : List (OutputNeed s)) where
  need : OutputNeed s
  index : Nat
  onList : needs[index]? = some need
  row : Declaration
  entry : CompletedUnaryEntry404 s q row need
  cycle : CurrentCycleAt s entry.lowerChild

def completedNativePrioritySource404 : SourcePrimitives where
  elected := supportedVariableSource404.elected
  other := fun s q verdict needs =>
    supportedVariableSource404.other s q verdict needs ∨
      (verdict = .rejected ∧ Nonempty (CompletedChildK2404 s q needs))

theorem native_priority_keeps_exact_rows404 : KeepsFixedOutputs404 completedNativePrioritySource404 :=
  supported_rules_keep_exact_rows404

private theorem direct_entry_is_not_variable404 {s q row need}
    (entry : CompletedUnaryEntry404 s q row need)
    (scope : ∀ d ∈ visible s.core q, RepeatedRow403 q d) : False := by
  have written : entry.written ∈ row.head := by rw [entry.exactHead]; exact List.mem_cons_self
  rw [(scope row entry.visibleRow).literal] at written
  obtain ⟨n,_,literal⟩ := List.mem_map.mp written
  have dispatch := entry.dispatch
  rw [← literal] at dispatch
  cases dispatch

/-- The diagnostic at an already-entered child is allowed only with
that child's lower proof. Raw root K2, separately, need not read a
single output dependency. -/
theorem actual_completed_native_child_k2_rejects404 {s q needs}
    (prior : CompletedChildK2404 s q needs)
    (support : SupportForest completedNativePrioritySource404 s needs) :
    Classifies completedNativePrioritySource404 s q .rejected ∧
      PatternK2 s.core.current.ordinary prior.entry.lowerChild prior.entry.query := by
  classical
  have actual := completed_lower_justifies_entered_native_child404 prior.entry native_priority_keeps_exact_rows404
    support prior.index prior.onList
  have inspected : PatternK2 s.core.current.ordinary prior.entry.lowerChild prior.entry.query :=
    ⟨prior.entry.lowerChild,actual.2.2,prior.cycle⟩
  refine ⟨?_,inspected⟩
  by_cases raw : RootCycle s q
  · exact root_k2_is_rejected_for_every_primitive_system raw
  · exact ⟨.rejected,none,⟨.other .rejected raw (.inr ⟨rfl,⟨prior⟩⟩) support⟩,.rejected⟩

theorem native_child_entry_needs_completed_original404 {s q needs}
    (prior : CompletedChildK2404 s q needs)
    (unready : ¬ Classifies completedNativePrioritySource404 s prior.need.producer (.selected prior.need.dictionary)) :
    ¬ Nonempty (SupportForest completedNativePrioritySource404 s needs) := by
  rintro ⟨support⟩
  exact no_finite_selected_producer_no_support404 unready ⟨support.atOriginal prior.index prior.onList⟩

theorem completed_structural_input_never_silently_dropped404 {s q needs}
    (prior : CompletedChildK2404 s q needs) {d} :
    ¬ Classifies completedNativePrioritySource404 s q (.selected d) := by
  rintro ⟨t,_,⟨trace⟩,summary⟩
  cases trace with
  | rootK2 => cases summary
  | other verdict _ _ _ => cases verdict <;> cases summary
  | selected event safe chosen support kids =>
    rcases chosen with old|new
    · obtain ⟨read⟩ := old.2.1
      exact direct_entry_is_not_variable404 prior.entry read.elected.scope.allVisible
    · obtain ⟨read⟩ := new.1
      exact direct_entry_is_not_variable404 prior.entry read.choice.rowShape

end Yulang.GeneralDeclarativeI65.I72
