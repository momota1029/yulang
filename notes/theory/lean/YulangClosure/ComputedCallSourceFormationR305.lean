import YulangClosure.ComputedCallUnionRealizationR293

/-!
R305: exact constructor obstruction, not EI-All formation or App closure.

The authoritative EI-All rule (computed-call-result-constructor, §4) and
DefineResultView (§2, GR1) require the original complete arm declarations,
typed EvalInvoke operands and registered result view. Source.app and its
CallOwner.application inventory do not contain those formation operands.
SourceSignatureConstruction.Node.call receives its CallNodes and catalogue;
the current build compiles that supplied node without constructing them.

The theorem records why an existing Call node cannot serve as R293's new
alternative node at the SAME graph index. It does not rule out a genuine
future construction that adds a separate registered alternative node. No
source arm, original interface, admission or target checking is changed.
-/
namespace YulangClosure.ComputedCallSourceFormationR305

open OriginalSource OriginalSourceInterpretation OriginalSourceEnvironment
open SourceSignatureConstruction SourceContributionConstruction
open ComputedCallUnionRealizationR293

/-- R293.sourceContribution and R293.armContribution both require a lookup
of their actual unionNode. An authentic Call lookup cannot discharge that
premise by a constructor cast, for any result catalogue or arm family. -/
theorem call_lookup_excludes_union {s : Sorts} {View : Type}
    (inputs : Inputs s) (state : Decoded s View) (scope : List Binder)
    (graph : Graph (RawObservation s)) (index : Nat)
    (context : Context) (mark : Mark) (callee argument : Source .expression)
    (nodes : CallNodes) (locals : List (Introduction (RawObservation s)))
    (result : Catalogue (RawObservation s))
    (found : graph.node index = some (.call context mark callee argument nodes locals result))
    (site : Site) (left right : Nat) (source : Endpoint) (arms : List Endpoint) :
    graph.node index ≠ some (unionNode inputs state scope site left right source arms) := by
  rw [found]
  intro same
  cases same

end YulangClosure.ComputedCallSourceFormationR305
