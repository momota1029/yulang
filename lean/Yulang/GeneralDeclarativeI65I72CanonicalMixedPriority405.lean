import Yulang.GeneralDeclarativeI65I72UnifiedGroundedReplay405

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72
open GeneralDeclarativeI65
open GeneralDeclarationPatterns (Pattern)

private theorem scan_kinds_are_disjoint405 {s q e needs support}
    (plain : GroundedSelection405 (s := s) (q := q) authoredNativeSelectedSource405 e needs support)
    (native : AuthoredNativeSelected405 e) : False := by
  have whole := (variable_scan_is_total405 plain.scan).2.2
  have patternAt : authoredUnaryPattern405 native.test.key native.test.binder ∈ e.frame.decl.head := by
    rw [native.test.writtenHead]
    exact List.mem_cons_self
  obtain ⟨n,bad,_⟩ := whole e.frame.decl e.frame.inScope _ patternAt
  change Pattern.app native.test.key [.var native.test.binder] = Pattern.var n at bad
  cases bad

/-- A whole derived visit list is invariant under proof changes in
the same represented selection, including the nonempty native case.
There is no equivalence just by visited keys or membership order. -/
theorem canonical_actual_mixed_visit_order405 {s q e needs support}
    (a b : ChosenScan405 (s := s) (q := q) e (needs := needs) support) :
    a.visits = b.visits := by
  cases a with
  | variableCase a =>
    cases b with
    | variableCase b => exact (no_selection_proof_can_append_an_unvisited_site405 a b).2
    | nominal b => exact False.elim (scan_kinds_are_disjoint405 a b)
  | nominal a =>
    cases b with
    | variableCase b => exact False.elim (scan_kinds_are_disjoint405 b a)
    | nominal b =>
      have sameInput : a.test.interval = b.test.interval :=
        (List.cons.inj (a.test.writtenArgs.symm.trans b.test.writtenArgs)).1
      have sameOrdinal : a.origin.rawOrdinal = b.origin.rawOrdinal :=
        (congrArg AuthoredBodyFrame393.ordinal a.frame).symm.trans
          (congrArg AuthoredBodyFrame393.ordinal b.frame)
      change [(⟨a.origin.rawOrdinal,0,[],.value,false,a.test.interval.lower⟩ : CandidateVisit)] =
        [(⟨b.origin.rawOrdinal,0,[],.value,false,b.test.interval.lower⟩ : CandidateVisit)]
      simp [sameInput,sameOrdinal]

/-- Actual support-indexed obligation, not an independent choice of
which sites happen to occur. This describes the represented rule
family only, and does not assert coverage for more than those rules. -/
def required_visit_on_represented_source405 {s : State} {q : Request} {e : Event s q} {needs}
    (support : SupportForest authoredNativeSelectedSource405 s needs) (site : CandidateVisit) : Prop :=
  ∃ scan : ChosenScan405 (e : Event s q) support, site ∈ scan.visits

theorem actual_mixed_S03_is_exact405 {s q e needs support}
    (scan : ChosenScan405 (s := s) (q := q) e (needs := needs) support) (raw : ¬RootCycle s q) :
    (¬RootCycle s q) ∧
    (∀ site, site ∈ scan.visits ↔ required_visit_on_represented_source405 (e := e) support site) ∧
    ∀ site ∈ scan.visits, site.declarationOrdinal = e.frame.ordinal ∧ ¬CurrentCycleAt s site.site := by
  refine ⟨raw,?_,?_⟩
  · intro site
    constructor
    · exact fun seen => ⟨scan,seen⟩
    · rintro ⟨other,seen⟩
      rw [canonical_actual_mixed_visit_order405 scan other]
      exact seen
  · have grounded := (exact_chosen_scan_has_raw_priority405 scan raw).byActualRule
    obtain ⟨chosen,safe⟩ := grounded
    rw [canonical_actual_mixed_visit_order405 scan chosen]
    exact safe

end Yulang.GeneralDeclarativeI65.I72
