import Yulang.GeneralDeclarativeI65I74StructuralWhereAssociatedEntry432

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.WhereAssociated432
open GeneralDeclarativeI65 StructuralWhere428
open Checker408 (Problem Result)
open CommonRoleOutermostResolver (Tree Dictionary Summarizes)
open CommonNominalFullCarrier (Ty Equivalent nominal)
open CommonDeclaredNominalInspection (Kind)

/-- Inverting a successful public check retrieves the same data-only
packet that the checker actually used, rather than a different
structural read that just happens to have the same dictionary. -/
theorem checked_associated_report_replays_actual_data433
    {p : Problem} {r : Result} {data : AssociatedWire432}
    (yes : check p r (.associatedWrap data) = true) :
    ∃ o : ReadAssociatedWrap432 p, readAssociatedWrap432 p data = some o ∧ r = o.report := by
  cases f : readAssociatedWrap432 p data with
  | none => simp [check,f] at yes
  | some o =>
    have checkExact : matchesAssociatedReport432 r o.report = true := by
      simpa [check,f] using yes
    exact ⟨o,rfl,(matches_associated_report_exact432 ..).mp checkExact⟩

/-- Accepted reports keep the exact occurrence/ordinal of the
original where child, carry its actual selected Event (not a fresh
proof about an equal-named model value), and retain its ordered ledger
in the parent's same State. This does not assert solver evaluation order. -/
theorem checked_associated_report_keeps_ordered_source_trace433
    {p : Problem} {r : Result} {data : AssociatedWire432}
    (yes : check p r (.associatedWrap data) = true) :
    ∃ (o : ReadAssociatedWrap432 p)
      (parent : SourceTrace R16.named426 p.state p.root o.tree (some o.event))
      (child : SourceTrace R16.named426 p.state o.original.origin.child
        (.selected o.child.declaration.decl.id []) (some o.child.event)),
      readAssociatedWrap432 p data = some o ∧ r = o.report ∧
      ActualWhereTraceAt432 parent 0 child ∧
      o.event.kids = [o.original.origin.child] ∧
      o.original.origin.child.occurrence = p.root.occurrence ++ [o.original.origin.clauseOrdinal] ∧
      Summarizes r.tree r.verdict ∧ r.writes = namedTraceWrites428 parent := by
  obtain ⟨o,replay,rExact⟩ := checked_associated_report_replays_actual_data433 yes
  obtain ⟨pt,ct,same,summary,ledger⟩ := read_wrap_preserves_exact_selected_source_and_writes432 o
  refine ⟨o,pt,ct,replay,rExact,same,exact_children432 o,rfl,?_,?_⟩
  · simpa [rExact] using summary
  · simpa [rExact] using ledger

/-- In the same fitting model the parent reads the child's fixed
target through the authored lexical binder and satisfies the actual
parent fixed targets. No fitting model is needed to identify the
child address or its occurrence. -/
theorem checked_associated_report_uses_child_in_same_model433
    {p : Problem} {r : Result} {data : AssociatedWire432}
    (yes : check p r (.associatedWrap data) = true) :
    ∃ (o : ReadAssociatedWrap432 p) (kt : Tree) (d : Dictionary)
      (e : Event p.state o.original.origin.child),
      readAssociatedWrap432 p data = some o ∧ r = o.report ∧
      (e.outputs o.original.origin.outputIndex).receipt.original = o.original.origin.output ∧
      (e.outputs o.original.origin.outputIndex).receipt.occurrence =
        p.root.occurrence ++ [o.original.origin.clauseOrdinal] ∧
      (e.outputs o.original.origin.outputIndex).receipt.outputOrdinal = o.original.origin.outputOrdinal ∧
      Summarizes kt (.selected d) ∧
      ∀ m : I72.Model, Fits p.state m →
        DictionaryEvidence p.state m p.root o.dictionary ∧
        DictionaryEvidence p.state m o.original.origin.child d ∧
        FixedTargets m o.event ∧
        (∀ k : Kind,
          sourceRead401 m (o.event.frame.slots (.explicit o.original.literalRhs))
            k o.original.outputBinder.name () = some (m.assignment o.original.origin.output.target)) ∧
        ∃ v : Ty, (e.outputs o.original.origin.outputIndex).receipt.actualEquation m =
          some (o.original.origin.output.target,v) ∧ Equivalent (m.assignment o.original.origin.output.target).1 v := by
  obtain ⟨o,pt,_,replay,eqReport,_,_,_,_,_⟩ :=
    checked_associated_report_keeps_ordered_source_trace433 yes
  have summary : Summarizes o.tree (.selected o.dictionary) :=
    .selected (.cons (.selected .nil (.selected rfl)) .nil) (.selected rfl)
  obtain ⟨kt,d,e,_,_,_,ks,occ,ord,outEq,_,actual⟩ :=
    actual_where_child_supplies_original_lexical_output432 associated_named_law432 pt summary o.original.origin
  refine ⟨o,kt,d,e,replay,eqReport,outEq,occ,ord,ks,?_⟩
  intro m fit
  obtain ⟨dict,read,target⟩ := actual m fit
  exact ⟨dictionary_sound_R16 _ _ _ (exact_associated_report_classifies_R16_432 o) m fit,
    dict,retained_typed_rows_satisfy_fixed_targets403 o.original.retained m fit,read,target⟩

/-- Publicly accepted source writes the original nominal constructor
applied to the child's assignment at its actual fixed target; equality
in the fitted model alone is not used to choose that target or body. -/
theorem checked_associated_report_evaluates_exact_parent_rhs433
    {p : Problem} {r : Result} {data : AssociatedWire432}
    (yes : check p r (.associatedWrap data) = true) :
    ∃ o : ReadAssociatedWrap432 p,
      readAssociatedWrap432 p data = some o ∧ r = o.report ∧
      ∀ m : I72.Model, Fits p.state m →
        (o.event.outputs o.original.indexedParentOutput).receipt.actualEquation m =
          some (p.root.demand.outputs[o.original.indexedParentOutput].target,
            nominal o.original.ctor [.inl (m.assignment o.original.origin.output.target).1]) ∧
        Equivalent (m.assignment p.root.demand.outputs[o.original.indexedParentOutput].target).1
          (nominal o.original.ctor [.inl (m.assignment o.original.origin.output.target).1]) := by
  obtain ⟨o,pt,_,replay,exactReport,_,_,_,_,_⟩ :=
    checked_associated_report_keeps_ordered_source_trace433 yes
  exact ⟨o,replay,exactReport,fun m fit =>
    actual_parent_unary_output_uses_exact_where_target432 associated_named_law432 pt
      o.original.origin o.original.indexedParentOutput o.original.body o.original.normalized
      o.original.actualTypedRhs m fit⟩

/-- This positive branch cannot accept a caller with a true raw root
K2, nor select a raw-cyclic actual where child's request. A false
result still means unsupported by this branch, not a new diagnosis. -/
theorem checked_associated_report_preserves_both_raw_roots433
    {p : Problem} {r : Result} {data : AssociatedWire432}
    (yes : check p r (.associatedWrap data) = true) :
    ¬ RootCycle p.state p.root ∧
      ∃ o : ReadAssociatedWrap432 p, readAssociatedWrap432 p data = some o ∧
        ¬ RootCycle p.state o.original.origin.child := by
  obtain ⟨o,replay,_⟩ := checked_associated_report_replays_actual_data433 yes
  exact ⟨o.original.rawRoot,o,replay,o.child.rawSafe⟩

end Yulang.GeneralDeclarativeI65.I72.WhereAssociated432
