import Yulang.GeneralDeclarativeObservedCompound347
import Yulang.GeneralDeclarativeCompoundCompiler338

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeObservedBody347
open GeneralDeclarations (Registry Declaration Checked Clause)
open GeneralDeclarativeHead320 (Equation State)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeCompoundTree338 (World Span Tree)
open GeneralDeclarativeCompoundInputs338 (Inputs)
open GeneralDeclarativeCompoundCompiler338 (body_ready)
open GeneralDeclarativeEndpointBody336 (Body)
open GeneralDeclarativeNestedBody332 (compileBody)
open GeneralDeclarativeNormalizeAssoc324 (one)
open GeneralDeclarativeBatch320 (collect)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCenteredHeadWFSource (Coverage)
open GeneralDeclarationPatterns (normalize)
open GeneralSourceState (Output)

theorem prints_target {r : Registry} {i : Interpretation} {impl : Declaration} {d : Demand}
    {cap : Nat → Capture} {out : Output} {rows : List Equation}
    (compiled : one r i impl d cap out = some rows) :
    rows.map Equation.left = [out.target] := by
  unfold one at compiled
  obtain ⟨_,_,rest⟩ := Option.bind_eq_some_iff.mp compiled
  obtain ⟨_,_,printed⟩ := Option.bind_eq_some_iff.mp rest
  rw [← Option.some.inj printed]
  rfl

theorem target_order {r : Registry} {i : Interpretation} {impl : Declaration} {d : Demand}
    {cap : Nat → Capture} {outs : List Output} {rows : List Equation}
    (compiled : collect (one r i impl d cap) outs = some rows) :
    rows.map Equation.left = outs.map Output.target := by
  induction outs generalizing rows with
  | nil =>
    cases Option.some.inj compiled
    rfl
  | cons out rest ih =>
    unfold collect at compiled
    obtain ⟨first,firstCode,later⟩ := Option.bind_eq_some_iff.mp compiled
    obtain ⟨remain,tailCode,fin⟩ := Option.bind_eq_some_iff.mp later
    rw [← Option.some.inj fin,List.map_append,prints_target firstCode,ih tailCode]
    rfl

/-- The established raw-origin tree now feeds the existing literal
ordered body compiler. Associated rows retain every requested target
in order; a compiled body is not by itself a proof of ordinary
consistency or successful native selection. -/
theorem compile_one_arg {r : Registry} {i : Interpretation} {d : Demand} {impl : Declaration}
    {w v : World done} {arg : Capture} {pat} {used : List Span} {keep : List Nat}
    (root : d.arguments = [arg]) (shape : impl.head = [pat])
    (tree : Tree keep w arg (normalize pat) v used)
    (checked : Checked r) (covered : Coverage r i) (visible : impl ∈ r.declarations)
    (role : impl.role = d.role) (wanted : Declared r d) (fallback : Nat → Capture)
    (targets : Clause → Nat → Nat) :
    ∃ s children, ∃ b : @Body r i d impl s children,
      compileBody r i d impl v.state used keep fallback targets = some (s,children) ∧
      b.rootRows.map Equation.left = d.outputs.map Output.target ∧
      b.spans = used ∧ b.targets = targets ∧
      GeneralDeclarativeGrowth327.Extends (GeneralDeclarativeStableAssemble329.tieState v.state used fallback) s := by
  have ins : Inputs r.constructors i keep w d.arguments impl.head v used := by
    rw [root,shape]
    simpa only [List.append_nil] using Inputs.compound (c := r.constructors) (i := i) (p := pat) tree Inputs.nil
  obtain ⟨s,children,b,compiled,picked,fixed,grown⟩ := body_ready ins checked covered visible role wanted fallback targets
  exact ⟨s,children,b,compiled,target_order b.rootWritten,picked,fixed,grown⟩

end Yulang.GeneralDeclarativeObservedBody347
