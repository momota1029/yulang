import Yulang.GeneralDeclarativeI65I74RepeatedCentersEntry421
import Yulang.GeneralDeclarativeI65I73RuleUnionInclusions407

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RepeatedCenters421
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open GeneralDeclarationPatterns (Pattern)

private theorem sameBinders {p} (a : Choice p) {d : Declaration}
    (seen : d ∈ visible p.state.core p.root) {ns : List Nat}
    (lit : d.head = ns.map Pattern.var) : ns = [a.binder,a.binder] := by
  have same : d = a.decl := by simpa [a.only] using seen
  have h : List.map Pattern.var ns = [.var a.binder,.var a.binder] :=
    lit.symm.trans ((congrArg Declaration.head same).trans a.literal)
  cases ns with
  | nil => simp at h
  | cons n ns =>
    cases ns with
    | nil => simp at h
    | cons m ns =>
      cases ns <;> simp_all

private theorem forcedCenterRow {p} (a : Choice p) {d : Declaration}
    (seen : d ∈ visible p.state.core p.root) (row : RepeatedRow403 p.root d)
    (apart : a.second.center ≠ a.first.center) :
    selectedCenterRows403 p.root row = [a.tie] := by
  have same := sameBinders a seen row.literal
  simp [selectedCenterRows403,selectedInputSpans403,selectedInput403,same,
    a.originalArgs,bindings403,centerTie403,Choice.tie,apart]

/-- At the same original request, the R0 rules cannot skip the
post-selection incompatibility by selecting through an older variable
or unary native path. No equality of source origins or capture triples
is assumed: the visible declaration and both original arguments fix
the directed tie. This excludes only R0 selection, not every old
diagnostic or every subsequent I74 extension. -/
theorem original_R0_selection_cannot_bypass_post_conflict421 {p} {a : Choice p}
    (bad : Conflict a) (e : Event p.state p.root) {needs} :
    ¬ R0.elected p.state p.root e needs := by
  intro old
  have fromRepeated (pick : RepeatedElection403 p.state p.root e.frame.decl)
      (retained : RetainedCenterRows403 pick) : False :=
    bad.absent (retained a.tie (by rw [forcedCenterRow a pick.inScope pick.row bad.read.apart]; simp))
  have fromWhere : Nonempty (VariableWhereReadback403 e) → False := by
    rintro ⟨read⟩
    exact fromRepeated read.elected read.retained
  have fromSupport : supportedVariableSource404.elected p.state p.root e needs → False := by
    intro supported
    rcases supported with oldWhere|fresh
    · exact fromWhere oldWhere.2.1
    · obtain ⟨read⟩ := fresh.1
      exact bad.absent (read.retained a.tie (by
        rw [forcedCenterRow a read.choice.inScope read.choice.row bad.read.apart]; simp))
  obtain ⟨_,family,rule⟩ := old
  cases family with
  | variableOnly =>
    obtain ⟨read⟩ := rule.2.1
    have seen : e.frame.decl ∈ visible p.state.core p.root := by
      rw [read.one]; exact List.mem_cons_self
    let row := read.scope.allVisible _ seen
    simpa [sameBinders a seen row.literal] using row.distinct
  | repeated =>
    obtain ⟨read⟩ := rule.2.1
    exact fromRepeated read.elected read.retained
  | whereTree | nativeK2 => exact fromWhere rule.2.1
  | supported | supportedK2 | supportedAmbiguity => exact fromSupport rule
  | authoredNative =>
    rcases rule with support|native
    · exact fromSupport support
    · obtain ⟨read⟩ := native.2.1
      have same : e.frame.decl = a.decl := by
        have h : e.frame.decl ∈ visible p.state.core p.root := by
          rw [read.test.visibleOnly]; exact List.mem_cons_self
        simpa [a.only] using h
      have impossible := congrArg List.length (read.test.writtenHead.symm.trans ((congrArg Declaration.head same).trans a.literal))
      simp at impossible

end Yulang.GeneralDeclarativeI65.I72.RepeatedCenters421
