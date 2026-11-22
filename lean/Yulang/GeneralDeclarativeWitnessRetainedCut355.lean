import Yulang.GeneralDeclarativeWitnessNominalSpineWhole355
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessRetainedCut355
open GeneralDeclarativeWitnessTypedRangeWriter354 (Run)
open GeneralDeclarativeWitnessRangeCut355 (residual_joins_only_allow_bare_here bare_scope selected_center)
open GeneralDeclarativeWitnessProblem349 (splitAnd)
open GeneralDeclarationPatterns (Pattern normalize normalizeArgs covered coveredArgs)
open GeneralDeclarativeWitnessCompiler350 (portNames)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeWitnessSpineNode355 (Node Step exact_physical_center no_payload_name_renaming)
open GeneralDeclarativeWitnessNominalSpine355 (Checked)
open GeneralDeclarativeHead320 (State)

theorem from_the_checked_head {p w} (r : Run p w) :
    coveredArgs (normalizeArgs r.readFrom.center.decl.head) = false := by
  rw [r.readFrom.center.written]
  simp only [normalizeArgs,r.readFrom.center.anchor.shape.extracted,coveredArgs,covered,
    Bool.false_and]

/-- The boundary is intrinsic to the retained C353/C354 typed reader,
not to the particular literal test binder numbers or role names. -/
theorem every_emitted_argument {p w} (r : Run p w) {d : Demand}
    (child : d ∈ r.children) :
    ∃ a, d.arguments = [a] ∧ a.center = r.readFrom.center.anchor.current.valueName := by
  obtain ⟨c,in_,exact⟩ := List.mem_map.mp child
  have legal := r.readFrom.center.good
  have every := (splitAnd (splitAnd (splitAnd legal).2).2).2
  have passed := List.all_eq_true.mp every c in_
  obtain ⟨n,shape⟩ := residual_joins_only_allow_bare_here (from_the_checked_head r) passed
  have names := bare_scope legal in_ shape
  refine ⟨(portNames r.readFrom.ctx r.ports).input n,?_,selected_center r names.1 names.2⟩
  rw [← exact]
  simp [GeneralDeclarativeSourceEmission322.demand, GeneralDeclarativeSourceEmission322.inputs,
    GeneralDeclarativeSourceEmission322.useArg,shape,normalize]

theorem cannot_rename_to_fixed_target {p w} (r : Run p w) {d : Demand}
    (child : d ∈ r.children) {a : Capture} (arg : a ∈ d.arguments) :
    a.center = r.readFrom.center.anchor.current.valueName := by
  obtain ⟨actual,one,center⟩ := every_emitted_argument r child
  rw [one] at arg
  exact (congrArg Capture.center (List.mem_singleton.mp arg)).trans center

theorem actual_link_target {s : State} {p : Node s} {a w} (q : Step p a w) :
    q.accepted.item.demand.target = p.valueName := by
  have d : q.actual ∈ p.proof.compiled.children := by rw [q.only]; exact List.mem_cons_self
  have exactArg : q.node.proof.compiled.readFrom.arg ∈ q.actual.arguments := by
    have shape := q.node.proof.compiled.readFrom.shape
    change q.actual.arguments = [_] at shape
    rw [shape]
    exact List.mem_cons_self
  exact (exact_physical_center q).symm.trans (cannot_rename_to_fixed_target p.proof.compiled d exactArg)

theorem no_distinct_physical_sites_along_spine {s : State} {p : Node s} (ok : Checked p) :
    ∀ edge ∈ ok.hops,edge.1 = p.valueName ∧ edge.2.1 = p.valueName := by
  induction ok with
  | leaf empty => intro edge missing; cases missing
  | @send middle a code edge tail ih =>
    have same := actual_link_target edge
    have checked := exact_physical_center edge
    intro triple more
    rcases List.mem_cons.mp more with first|later
    · cases first
      exact ⟨same,checked.trans same⟩
    · have kept := no_payload_name_renaming edge
      exact ⟨(ih _ later).1.trans kept,(ih _ later).2.trans kept⟩

end Yulang.GeneralDeclarativeWitnessRetainedCut355
